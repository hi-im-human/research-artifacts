"""Task 4: whole-run integrity, external anchoring, loading without execution, deterministic replay."""
import json

import pytest

from glab.core import runfile
from glab.core.evidence import Requirement, summarize
from glab.core.records import canonical_json, content_hash
from glab.core.registry import ActionSpec, Param, StateDraft
from glab.core.runfile import Run, RunIntegrityError, load_run, replay
from tests.core import toy
from tests.core.toy import REV, registry


def build_run(value="3"):
    run = Run(registry())
    a = run.apply("toy.int.source", 1, {"value": value})["output"]
    b = run.apply("toy.int.add", 1, {"k": 1}, a)["output"]
    run.apply("toy.int.divide", 1, {"d": 0}, b)            # failed attempt
    run.apply("toy.int.add", 2, {"k": 1}, b)               # rejected attempt
    run.check("toy.check.even", 1, b, {})
    run.check("toy.check.even", 1, b, {})                  # repeated check of one state
    run.check("toy.check.prime", 1, run.apply("toy.int.add", 1, {"k": 2000}, b)["output"], {})  # unknown
    return run


def saved(tmp_path, run, name="run.json"):
    p = tmp_path / name
    digest = run.save(p)
    return p, digest


def rewrite(path, fn, *, recompute=False):
    data = json.loads(path.read_text(encoding="ascii"))
    fn(data)
    if recompute:
        data["run_digest"] = content_hash({k: v for k, v in data.items() if k != "run_digest"})
    path.write_text(canonical_json(data) + "\n", encoding="ascii", newline="\n")


# ---------------------------------------------------------------- round trip and replay

def test_round_trip_and_replay_reproduce(tmp_path):
    run = build_run()
    p, digest = saved(tmp_path, run)
    loaded = load_run(p, expected_digest=digest)
    assert loaded.integrity == "internally_consistent" and loaded.anchor == "matched"
    assert loaded.authenticated is False
    # v2 format: actions and check attempts share one ordered "history" (repair R02).
    assert loaded.record["history"] == run.history and loaded.record["evidence"] == run.evidence
    assert [a["status"] for a in run.actions] == ["succeeded", "succeeded", "failed", "rejected",
                                                               "succeeded"]
    assert len(loaded.record["evidence"]) == 3  # repeated check not deduplicated
    report = replay(loaded, registry())
    assert report["outcome"] == "reproduced", report
    assert report["run_digest_reproduced"] is True
    assert [r["result"] for r in report["actions"]] == ["reproduced"] * 5
    assert [r["result"] for r in report["checks"]] == ["reproduced"] * 3


def test_unanchored_load_is_never_authenticated(tmp_path):
    p, _ = saved(tmp_path, build_run())
    loaded = load_run(p)
    assert loaded.anchor == "unanchored" and loaded.authenticated is False


def test_loaded_evidence_is_not_verified_until_replayed(tmp_path):
    run = build_run()
    p, digest = saved(tmp_path, run)
    loaded = load_run(p, expected_digest=digest)
    b = run.actions[1]["output"]
    reqs = [Requirement("toy.even", b)]
    reg = registry()
    before = summarize(loaded.record["evidence"], reqs, loaded.store, reg)
    assert before["outcome"] == "pass" and before["verified"] is False
    report = replay(loaded, reg)
    after = report["run"].summarize(reqs)
    assert after["outcome"] == "pass" and after["verified"] is True


def test_save_is_deterministic(tmp_path):
    p1, d1 = saved(tmp_path, build_run(), "a.json")
    p2, d2 = saved(tmp_path, build_run(), "b.json")
    assert d1 == d2 and p1.read_bytes() == p2.read_bytes()
    assert b"\r" not in p1.read_bytes()


# ---------------------------------------------------------------- tampering (internal integrity)

def _first_state(data, kind="toy.int", root=True):
    return next(h for h, s in data["states"].items() if s["kind"] == kind and (s["parent"] is None) == root)


@pytest.mark.parametrize("edit,msg", [
    (lambda d: d["states"][_first_state(d, root=False)]["payload"].update(value="99"), "does not match its hash"),
    (lambda d: d["states"][_first_state(d)]["payload"].update(value="99"), "does not match its hash"),
    (lambda d: d["history"][1]["params"].update(k=5), "run digest"),
    (lambda d: d["history"].insert(0, d["history"].pop(1)), "seq"),
    # Repair R02: check attempts list their evidence ids, so evidence edits now fail structurally.
    (lambda d: d["evidence"][0].update(outcome="fail"), "evidence ids differ"),
    (lambda d: d["evidence"][0].update(checker_revision="other"), "evidence ids differ"),
    (lambda d: d["identities"]["checkers"].update({"toy.check.even@1": "x"}), "run digest"),
    (lambda d: d["environment"].update(python="0.0.0"), "run digest"),
    (lambda d: d.update(extra=1), "keys"),
    (lambda d: d.update(schema="glab.run/9"), "unsupported run schema"),
])
def test_edits_break_internal_integrity(tmp_path, edit, msg):
    p, _ = saved(tmp_path, build_run())
    rewrite(p, edit)
    with pytest.raises(RunIntegrityError, match=msg):
        load_run(p)


def test_missing_referenced_state_is_rejected_even_with_recomputed_digest(tmp_path):
    run = build_run()
    p, _ = saved(tmp_path, run)
    b = run.actions[1]["output"]
    rewrite(p, lambda d: d["states"].pop(b), recompute=True)
    with pytest.raises(RunIntegrityError, match="unknown state"):
        load_run(p)


def test_action_order_swap_with_renumbered_seq_still_fails(tmp_path):
    p, _ = saved(tmp_path, build_run())

    def swap(d):
        d["history"][0], d["history"][1] = d["history"][1], d["history"][0]
        for i, a in enumerate(d["history"]):
            a["seq"] = i
    rewrite(p, swap)
    # Repair R05: chronology is now checked before the digest, so the child-before-parent order is named.
    with pytest.raises(RunIntegrityError, match="not yet available"):
        load_run(p)


@pytest.mark.parametrize("text,msg", [
    ('{"schema":"glab.run/1","schema":"glab.run/1"}', "duplicate"),
    ('{"schema":"glab.run/1","x":NaN}', "nonfinite"),
    ("not json", "invalid JSON"),
])
def test_malformed_json_rejected(tmp_path, text, msg):
    p = tmp_path / "bad.json"
    p.write_text(text, encoding="ascii")
    with pytest.raises(RunIntegrityError, match=msg):
        load_run(p)


def test_cyclic_or_dangling_state_graph_rejected(tmp_path):
    p, _ = saved(tmp_path, build_run())
    x, y = "sha256:" + "a" * 64, "sha256:" + "b" * 64

    def cyc(d):
        d["states"][x] = {"schema": "glab.state/1", "kind": "toy.int", "parent": y, "representation": "exact",
                          "payload": {}}
        d["states"][y] = {"schema": "glab.state/1", "kind": "toy.int", "parent": x, "representation": "exact",
                          "payload": {}}
    rewrite(p, cyc, recompute=True)
    with pytest.raises(RunIntegrityError):
        load_run(p)


# ---------------------------------------------------------------- external anchor

def test_wholly_rewritten_run_fails_against_external_old_digest(tmp_path):
    original = build_run("3")
    p, old_digest = saved(tmp_path, original)
    forged_run = build_run("5")  # a different, internally consistent history
    forged_run.save(p)
    assert load_run(p).integrity == "internally_consistent"  # consistent is not authentic
    with pytest.raises(RunIntegrityError, match="externally retained"):
        load_run(p, expected_digest=old_digest)


def test_evidence_only_edit_with_recomputed_digest_needs_the_anchor(tmp_path):
    p, old_digest = saved(tmp_path, build_run())
    naive = tmp_path / "naive.json"
    naive.write_bytes(p.read_bytes())
    rewrite(naive, lambda d: d["evidence"][2].update(outcome="pass"), recompute=True)
    with pytest.raises(RunIntegrityError, match="evidence ids differ"):  # repair R02 binds attempts to ids
        load_run(naive)

    def forge(d):  # a careful forger also rewrites the producing attempt's evidence list
        from glab.core.evidence import evidence_id
        d["evidence"][2]["outcome"] = "pass"
        attempt = d["history"][d["evidence"][2]["attempt"]]
        attempt["evidence"] = [evidence_id(d["evidence"][2])]
    rewrite(p, forge, recompute=True)
    assert load_run(p).integrity == "internally_consistent"
    with pytest.raises(RunIntegrityError, match="externally retained"):
        load_run(p, expected_digest=old_digest)


# ---------------------------------------------------------------- loading never executes

def test_loading_does_not_execute(tmp_path):
    calls = []

    def spy(state, params, seed):
        calls.append(1)
        return StateDraft("toy.int", {"value": "1"}, "exact")
    reg = registry()
    reg.register_action(ActionSpec("toy.int.spy", 1, None, {}, "spy-1", spy))
    run = Run(reg)
    run.apply("toy.int.spy", 1, {})
    p, digest = saved(tmp_path, run)
    assert calls == [1]
    load_run(p, expected_digest=digest)
    assert calls == [1]
    replay(load_run(p), reg)
    assert calls == [1, 1]  # only replay re-executes


# ---------------------------------------------------------------- replay mismatches

def test_changed_implementation_same_revision_is_a_mismatch(tmp_path):
    p, _ = saved(tmp_path, build_run())
    reg = registry()
    reg._actions[("toy.int.add", 1)] = ActionSpec(
        "toy.int.add", 1, "toy.int", {"k": Param.int()}, REV,
        lambda s, prm, seed: StateDraft("toy.int", {"value": "0"}, "exact"))
    report = replay(load_run(p), reg)
    assert report["outcome"] == "mismatch"


def test_changed_revision_is_not_run_not_a_pass(tmp_path):
    p, _ = saved(tmp_path, build_run())
    reg = registry()
    spec = reg._checkers[("toy.check.even", 1)]
    reg._checkers[("toy.check.even", 1)] = type(spec)(spec.name, 1, spec.accepts, spec.params, "rev-2", spec.fn)
    report = replay(load_run(p), reg)
    assert report["outcome"] == "not_run"
    assert [r["result"] for r in report["checks"]][:2] == ["not_run", "not_run"]


def test_missing_action_makes_dependents_not_run(tmp_path):
    p, _ = saved(tmp_path, build_run())
    reg = registry()
    del reg._actions[("toy.int.add", 1)]
    report = replay(load_run(p), reg)
    assert report["outcome"] == "not_run"
    results = [r["result"] for r in report["actions"]]
    assert results[0] == "reproduced" and results[1] == "not_run"
    assert all(r == "not_run" for r in results[2:])


def test_environment_mismatch_is_not_reproduced(tmp_path, monkeypatch):
    p, _ = saved(tmp_path, build_run())
    real = runfile.environment()
    monkeypatch.setattr(runfile, "environment", lambda: dict(real, python="9.9.9"))
    report = replay(load_run(p), registry())
    assert report["outcome"] == "environment_mismatch" and report["environment_match"] is False
