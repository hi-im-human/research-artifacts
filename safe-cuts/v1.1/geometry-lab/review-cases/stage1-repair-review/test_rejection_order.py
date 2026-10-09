"""System follow-up C01: rejected JSON objects must replay independent of key insertion order.

Run from engine/: python -m pytest -q /path/to/test_rejection_order.py
Expected at commit-30: two failures. This is a safe mismatch, not a false reproduced result.
"""
import pytest
from glab.core.registry import ActionSpec, CheckerSpec, Claim, Param, Registry, RegistryError, StateDraft
from glab.core.runfile import Run, load_run, replay


def make_registry():
    reg = Registry()
    reg.register_action(ActionSpec("follow.source", 1, None, {}, "follow-1",
                                   lambda s, p, seed: StateDraft("follow.int", {"value": "4"}, "exact")))
    reg.register_action(ActionSpec("follow.add", 1, "follow.int", {"k": Param.int()}, "follow-1",
                                   lambda s, p, seed: StateDraft("follow.int", {"value": str(4+p["k"])}, "exact")))
    reg.register_checker(CheckerSpec("follow.check", 1, "follow.int", {"limit": Param.int()}, "follow-1",
                                     lambda s, p: [Claim("follow.p", "unknown", "numerical_diagnostic", "integer")]))
    return reg


@pytest.mark.parametrize("kind", ["action", "check"])
def test_rejected_parameter_order_replays_without_record_drift(tmp_path, kind):
    reg = make_registry()
    run = Run(reg)
    subject = run.apply("follow.source", 1, {})["output"]
    # This insertion order differs from canonical JSON order. Both keys are invalid.
    params = {"z": 0, "a": 0}
    if kind == "action":
        assert run.apply("follow.add", 1, params, subject)["status"] == "rejected"
    else:
        with pytest.raises(RegistryError):
            run.check("follow.check", 1, subject, params)
    path = tmp_path / "run.json"
    expected = run.save(path)
    report = replay(load_run(path, expected_digest=expected), reg)
    assert report["outcome"] == "reproduced", report
    assert report["run_digest_reproduced"] is True
