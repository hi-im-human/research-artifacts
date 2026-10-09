"""ADAPTED copy of System's Stage 1 review cases (sanitized copy of the verbatim original at review-cases/stage1-review/;
original Git blob 52c99f943934cf03becf4cbc8302f6c24b7badaf, retained privately).

Single change: in R05 the run record key "actions" became "history", because run format
glab.run/2 keeps actions and check attempts in one ordered history (repair R02). Nothing else
differs; the verbatim file is run separately and its result is reported in the repair return.

Original docstring follows:
System's Stage 1 review cases, run against unmodified head commit-26.

Run from engine/ with its Python:
  python -m pytest -q /path/to/test_review_regressions.py

Alternatively set GLAB_ENGINE to that engine directory. These tests specify
requested repair behavior. Failures on the reviewed head are preserved as
review evidence, not presented as newly fixed or passing engine tests.
"""
from __future__ import annotations

import json
import os
import sys
from pathlib import Path

import pytest

ENGINE = Path(os.environ.get("GLAB_ENGINE", str(Path.cwd()))).resolve()
sys.path.insert(0, str(ENGINE))

from glab.core.evidence import Requirement, summarize
from glab.core.records import canonical_json, content_hash
from glab.core.registry import ActionSpec, CheckerSpec, Claim, Param, Registry, StateDraft
from glab.core.runfile import Run, RunIntegrityError, load_run, replay


def setup(check_fn=None):
    registry = Registry()
    registry.register_action(ActionSpec(
        "review.source", 1, None, {"value": Param.int()}, "source-v1",
        lambda state, params, seed: StateDraft("review.integer", {"value": params["value"]}, "exact")))
    registry.register_action(ActionSpec(
        "review.add", 1, "review.integer", {"delta": Param.int()}, "add-v1",
        lambda state, params, seed: StateDraft(
            "review.integer", {"value": state["payload"]["value"] + params["delta"]}, "exact")))
    if check_fn is not None:
        registry.register_checker(CheckerSpec(
            "review.check", 1, "review.integer", {}, "checker-v1", check_fn))
    run = Run(registry)
    h = run.apply("review.source", 1, {"value": 2})["output"]
    return registry, run, h


def positive(state, params):
    return [Claim("review.p", "pass", "exact_computation", "integers")]


def test_control_normal_run_reproduces_full_digest(tmp_path):
    registry, run, h = setup(positive)
    run.check("review.check", 1, h, {})
    path = tmp_path / "normal.json"
    digest = run.save(path)
    report = replay(load_run(path, expected_digest=digest), registry)
    assert report["outcome"] == "reproduced"
    assert report["run_digest_reproduced"] is True


def test_control_loading_does_not_verify_recorded_claim(tmp_path):
    registry, run, h = setup(positive)
    run.check("review.check", 1, h, {})
    path = tmp_path / "loaded.json"
    run.save(path)
    loaded = load_run(path)
    result = summarize(loaded.record["evidence"], [Requirement("review.p", h)], loaded.store, registry)
    assert result["outcome"] == "pass"
    assert result["verified"] is False


def test_R01_invalid_json_version_replay_cannot_claim_reproduced_with_different_digest(tmp_path):
    registry, run, h = setup()
    attempt = run.apply("review.add", True, {"delta": 1}, h)
    assert attempt["status"] == "rejected"
    path = tmp_path / "rejected.json"
    run.save(path)
    report = replay(load_run(path), registry)
    assert report["outcome"] != "reproduced" or report["run_digest_reproduced"], report


def test_R01_changed_failure_message_cannot_claim_whole_run_reproduced(tmp_path):
    registry, run, h = setup()
    def first(state, params, seed):
        raise ValueError("first reason")
    registry.register_action(ActionSpec("review.error", 1, "review.integer", {}, "error-v1", first))
    run.apply("review.error", 1, {}, h)
    path = tmp_path / "failed.json"
    run.save(path)
    other, _, _ = setup()
    def second(state, params, seed):
        raise ValueError("different reason")
    other.register_action(ActionSpec("review.error", 1, "review.integer", {}, "error-v1", second))
    report = replay(load_run(path), other)
    assert report["outcome"] != "reproduced" or report["run_digest_reproduced"], report


def test_R02_checker_crash_is_retained_as_an_attempt():
    count = [0]
    def checker(state, params):
        count[0] += 1
        if count[0] > 1:
            raise RuntimeError("deliberate checker crash")
        return positive(state, params)
    registry, run, h = setup(checker)
    run.check("review.check", 1, h, {})
    previous_digest = run.digest()
    try:
        run.check("review.check", 1, h, {})
    except RuntimeError:
        pass  # raising is allowed; losing the attempted check is not
    assert run.digest() != previous_digest, "The crashed check left no record in the run."
    assert run.evidence[0]["outcome"] == "pass", "Preserve the earlier result; a crash is not its negation."


def test_R02_zero_claim_check_is_retained_and_reexecuted(tmp_path):
    calls = [0]
    def checker(state, params):
        calls[0] += 1
        return []
    registry, run, h = setup(checker)
    previous_digest = run.digest()
    run.check("review.check", 1, h, {})
    assert run.digest() != previous_digest, "A completed zero-claim check vanished from the history."
    path = tmp_path / "empty-check.json"
    run.save(path)
    report = replay(load_run(path), registry)
    assert calls == [2]
    assert report["outcome"] == "reproduced"


def test_R03_checker_owned_receipt_cannot_mutate_retained_history():
    receipt = {"nested": {"observations": [1]}}
    policy = {"absolute": "0"}
    def checker(state, params):
        return [Claim("review.p", "pass", "exact_computation", "integers",
                      tolerances=policy, receipt=receipt)]
    registry, run, h = setup(checker)
    run.check("review.check", 1, h, {})
    before = run.evidence
    previous_digest = run.digest()
    receipt["nested"]["observations"].append(2)
    policy["absolute"] = "1"
    assert run.evidence == before, "The callback still owns mutable objects inside the retained evidence."
    assert run.digest() == previous_digest


def test_R03_mutating_loaded_public_record_cannot_bypass_integrity(tmp_path):
    registry, run, h = setup(positive)
    run.check("review.check", 1, h, {})
    path = tmp_path / "anchored.json"
    expected = run.save(path)
    loaded = load_run(path, expected_digest=expected)
    try:
        loaded.record["evidence"].clear()
    except (AttributeError, TypeError):
        return  # immutable view is acceptable
    try:
        report = replay(loaded, registry)
    except RunIntegrityError:
        return  # detecting mutation at the reuse boundary is also acceptable
    assert report["outcome"] != "reproduced" or report["run_digest_reproduced"], report


def test_R04_explicit_all_scope_requirement_rejects_sample_only_evidence():
    """New schema requirement: scope must be expressible, not guessed from a predicate name.

    The implementer may expose an equivalent typed scope contract and adapt
    this call with an explanation. Full/sample scope matching remains required.
    """
    def checker(state, params):
        return [Claim("review.p", "pass", "exact_computation", "integers", coverage="sample:one")]
    registry, run, h = setup(checker)
    run.check("review.check", 1, h, {})
    req = Requirement("review.p", h, coverage="all")
    result = run.summarize([req])
    assert result["outcome"] != "pass" and result["verified"] is False


def test_R05_successful_actions_cannot_reference_a_future_output(tmp_path):
    registry, run, h = setup()
    run.apply("review.add", 1, {"delta": 1}, h)
    data = run.to_record()
    data["history"].reverse()
    for index, action in enumerate(data["history"]):
        action["seq"] = index
    data["run_digest"] = content_hash({k: v for k, v in data.items() if k != "run_digest"})
    path = tmp_path / "future-reference.json"
    path.write_text(canonical_json(data), encoding="ascii")
    with pytest.raises(RunIntegrityError):
        load_run(path)
