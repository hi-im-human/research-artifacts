"""Stage 1 repair controls around System's review cases R01-R05 (see STAGE-1-REPAIR-PLAN.md)."""
import json

import pytest

from glab.core.evidence import EvidenceError, Requirement, evidence_id, summarize
from glab.core.records import canonical_json, content_hash
from glab.core.registry import CheckerSpec, Claim, RegistryError
from glab.core.runfile import Run, RunIntegrityError, load_run, replay
from tests.core.toy import registry


def src(run, value="4"):
    return run.apply("toy.int.source", 1, {"value": value})["output"]


def save(tmp_path, run, name="r.json"):
    p = tmp_path / name
    return p, run.save(p)


def recompute(p, fn):
    data = json.loads(p.read_text(encoding="ascii"))
    fn(data)
    data["run_digest"] = content_hash({k: v for k, v in data.items() if k != "run_digest"})
    p.write_text(canonical_json(data) + "\n", encoding="ascii", newline="\n")


def reg_with(*checkers):
    reg = registry()
    for name, fn in checkers:
        reg.register_checker(CheckerSpec(name, 1, "toy.int", {}, f"{name}-rev", fn))
    return reg


# ---------------------------------------------------------------- R01

def test_rejected_bool_version_is_stored_as_json_bool_and_replays(tmp_path):
    run = Run(registry())
    a = src(run)
    rec = run.apply("toy.int.add", True, {"k": 1}, a)
    assert rec["status"] == "rejected" and rec["version"] is True and rec["unrepresentable"] == []
    p, d = save(tmp_path, run)
    report = replay(load_run(p, expected_digest=d), registry())
    assert report["outcome"] == "reproduced" and report["run_digest_reproduced"] is True


def test_unrepresentable_input_is_described_not_evaluated(tmp_path):
    run = Run(registry())
    a = src(run)
    rec = run.apply("toy.int.add", 1, {"k": {1, 2}}, a)
    assert rec["status"] == "rejected"
    assert rec["params"] == {"python_type": "dict"} and rec["unrepresentable"] == ["params"]
    p, _ = save(tmp_path, run)
    report = replay(load_run(p), registry())
    assert report["actions"][1]["result"] == "not_replayable"
    assert report["outcome"] == "not_run" and report["run_digest_reproduced"] is False


def test_reproduced_always_means_full_digest_reproduced(tmp_path):
    run = Run(registry())
    a = src(run)
    run.apply("toy.int.divide", 1, {"d": 0}, a)
    run.check("toy.check.even", 1, a, {})
    p, _ = save(tmp_path, run)
    report = replay(load_run(p), registry())
    assert report["outcome"] == "reproduced" and report["run_digest_reproduced"] is True


# ---------------------------------------------------------------- R02

def test_failed_checker_attempt_is_recorded_raised_and_does_not_negate_earlier_evidence():
    calls = []

    def flaky(state, params):
        calls.append(1)
        if len(calls) > 1:
            raise RuntimeError("crash")
        return [Claim("toy.flaky", "pass", "exact_computation", "exact_rational")]
    run = Run(reg_with(("toy.check.flaky", flaky)))
    a = src(run)
    run.check("toy.check.flaky", 1, a, {})
    with pytest.raises(RuntimeError):
        run.check("toy.check.flaky", 1, a, {})
    checks = run.checks
    assert [c["status"] for c in checks] == ["completed", "failed"]
    assert checks[1]["failure"] == {"stage": "execution", "type": "RuntimeError", "message": "crash"}
    assert checks[1]["evidence"] == [] and len(run.evidence) == 1 and run.evidence[0]["outcome"] == "pass"
    assert run.summarize([Requirement("toy.flaky", a)])["outcome"] == "pass"


def test_rejected_check_attempts_are_recorded_then_raised():
    run = Run(registry())
    a = src(run)
    for args in (("toy.check.missing", 1, a, {}), ("toy.check.even", True, a, {}),
                 ("toy.check.even", 1, a, {"x": 1}), ("toy.check.even", 1, "sha256:" + "0" * 64, {})):
        with pytest.raises(RegistryError):
            run.check(*args)
    assert [c["status"] for c in run.checks] == ["rejected"] * 4
    assert all(c["failure"]["stage"] == "validation" for c in run.checks)
    assert run.checks[1]["version"] is True


def test_malformed_and_formal_outputs_are_failed_attempts():
    run = Run(reg_with(("toy.check.bad", lambda s, p: "not a list"),
                       ("toy.check.formal", lambda s, p: [Claim("toy.x", "pass", "formal_proof", "lean")])))
    a = src(run)
    with pytest.raises(RegistryError):
        run.check("toy.check.bad", 1, a, {})
    with pytest.raises(EvidenceError):
        run.check("toy.check.formal", 1, a, {})
    assert [(c["status"], c["failure"]["type"]) for c in run.checks] == [("failed", "RegistryError"),
                                                                        ("failed", "EvidenceError")]
    assert run.evidence == []


def test_zero_claim_and_multi_claim_checks_replay_as_whole_attempts(tmp_path):
    calls = []

    def empty(state, params):
        calls.append("empty")
        return []

    def two(state, params):
        calls.append("two")
        return [Claim("toy.a", "pass", "exact_computation", "exact_rational"),
                Claim("toy.b", "unknown", "numerical_diagnostic", "float64")]
    reg = reg_with(("toy.check.empty", empty), ("toy.check.two", two))
    run = Run(reg)
    a = src(run)
    e = run.check("toy.check.empty", 1, a, {})
    t = run.check("toy.check.two", 1, a, {})
    run.check("toy.check.two", 1, a, {})  # repeated check: a distinct attempt
    assert e == [] and len(t) == 2
    checks = run.checks
    assert [len(c["evidence"]) for c in checks] == [0, 2, 2] and checks[1]["evidence"] != checks[2]["evidence"]
    assert [ev["attempt"] for ev in run.evidence] == [checks[1]["seq"]] * 2 + [checks[2]["seq"]] * 2
    p, d = save(tmp_path, run)
    report = replay(load_run(p, expected_digest=d), reg)
    assert calls == ["empty", "two", "two", "empty", "two", "two"]
    assert report["outcome"] == "reproduced" and [r["result"] for r in report["checks"]] == ["reproduced"] * 3


def test_history_interleaves_actions_and_checks():
    run = Run(registry())
    a = src(run)
    run.check("toy.check.even", 1, a, {})
    run.apply("toy.int.add", 1, {"k": 1}, a)
    assert [(h["schema"], h["seq"]) for h in run.history] == [("glab.action/2", 0), ("glab.check/1", 1),
                                                              ("glab.action/2", 2)]


# ---------------------------------------------------------------- R03

def test_caller_mutation_after_apply_cannot_change_the_record():
    run = Run(registry())
    a = src(run)
    params = {"k": 1}
    run.apply("toy.int.add", 1, params, a)
    before = run.digest()
    params["k"] = 99
    assert run.digest() == before and run.actions[1]["params"] == {"k": 1}


def test_loaded_record_and_store_are_fresh_copies_of_one_snapshot(tmp_path):
    run = Run(registry())
    a = src(run)
    run.check("toy.check.even", 1, a, {})
    p, d = save(tmp_path, run)
    loaded = load_run(p, expected_digest=d)
    loaded.record["evidence"].clear()
    loaded.record["history"].clear()
    loaded.store.put({"schema": "glab.state/1", "kind": "x", "parent": None, "representation": "exact",
                      "payload": {}})
    assert len(loaded.record["evidence"]) == 1 and len(loaded.store) == 1
    report = replay(loaded, registry())
    assert report["outcome"] == "reproduced" and report["run_digest_reproduced"] is True


# ---------------------------------------------------------------- R04

def _coverage_run(*coverages_and_outcomes):
    def fn(state, params):
        return [Claim("toy.scope", o, "exact_computation", "exact_rational", coverage=c)
                for c, o in coverages_and_outcomes]
    run = Run(reg_with(("toy.check.scope", fn)))
    a = src(run)
    run.check("toy.check.scope", 1, a, {})
    return run, a


def test_full_coverage_satisfies_default_all_requirement():
    run, a = _coverage_run(("all", "pass"))
    out = run.summarize([Requirement("toy.scope", a)])
    assert out["outcome"] == "pass" and out["verified"] is True


def test_partial_coverage_needs_an_explicit_matching_requirement():
    run, a = _coverage_run(("sample:one", "pass"))
    assert run.summarize([Requirement("toy.scope", a)])["outcome"] == "unknown"
    assert run.summarize([Requirement("toy.scope", a, coverage="all")])["verified"] is False
    assert run.summarize([Requirement("toy.scope", a, coverage="sample:one")])["outcome"] == "pass"
    assert run.summarize([Requirement("toy.scope", a, coverage=None)])["outcome"] == "pass"


def test_missing_scope_evidence_is_not_run():
    run, a = _coverage_run(("all", "pass"))
    other = src(run, "6")
    assert run.summarize([Requirement("toy.scope", other)])["outcome"] == "not_run"


def test_sample_failure_conflicts_with_full_pass():
    run, a = _coverage_run(("all", "pass"), ("sample:one", "fail"))
    out = run.summarize([Requirement("toy.scope", a)])
    assert out["outcome"] == "unknown" and "conflict" in out["requirements"][0]["reason"]


# ---------------------------------------------------------------- R05

def test_rejected_request_for_missing_input_is_an_honest_loadable_record(tmp_path):
    run = Run(registry())
    run.apply("toy.int.add", 1, {"k": 1}, "sha256:" + "9" * 64)
    with pytest.raises(RegistryError):
        run.check("toy.check.even", 1, "sha256:" + "8" * 64, {})
    p, d = save(tmp_path, run)
    assert load_run(p, expected_digest=d).integrity == "internally_consistent"


def test_orphan_state_rejected(tmp_path):
    run = Run(registry())
    src(run)
    p, _ = save(tmp_path, run)
    orphan = {"schema": "glab.state/1", "kind": "toy.int", "parent": None, "representation": "exact",
              "payload": {"value": "7"}}
    recompute(p, lambda d: d["states"].update({content_hash(orphan): orphan}))
    with pytest.raises(RunIntegrityError, match="not produced"):
        load_run(p)


def test_check_before_its_subject_exists_rejected(tmp_path):
    run = Run(registry())
    a = src(run)
    run.check("toy.check.even", 1, a, {})
    p, _ = save(tmp_path, run)

    def swap(d):
        d["history"].reverse()
        for i, h in enumerate(d["history"]):
            h["seq"] = i
        for ev in d["evidence"]:
            ev["attempt"] = 0
        ids = [evidence_id(ev) for ev in d["evidence"]]
        d["history"][0]["evidence"] = ids
    recompute(p, swap)
    with pytest.raises(RunIntegrityError, match="not yet available"):
        load_run(p)


@pytest.mark.parametrize("edit,msg", [
    (lambda d: d["history"][0].update(seq=True), "seq"),
    (lambda d: d["history"][0].update(version=True), "version"),
    (lambda d: d["history"][1].update(version=True), "version"),
    (lambda d: d["history"][0].update(seed="1"), "seed"),
    (lambda d: d["history"][0].update(implementation_revision=None), "revision"),
    (lambda d: d["evidence"][0].update(attempt=0), "attempt"),
])
def test_primitive_fields_are_validated(tmp_path, edit, msg):
    run = Run(registry())
    a = src(run)
    run.check("toy.check.even", 1, a, {})
    p, _ = save(tmp_path, run)
    recompute(p, edit)
    with pytest.raises(RunIntegrityError, match=msg):
        load_run(p)


# ---------------------------------------------------------------- format version

def test_stage1_v1_run_file_is_rejected_clearly():
    from pathlib import Path
    old = Path(__file__).resolve().parents[2] / "receipts" / "demo" / "demo.run.json"
    with pytest.raises(RunIntegrityError, match="glab.run/1"):
        load_run(old)
