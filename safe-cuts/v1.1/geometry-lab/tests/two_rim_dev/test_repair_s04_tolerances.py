"""Stage 3 repair S04: numerical claims carry the tolerance policy in the core's Claim.tolerances field."""
import copy

from glab.check.two_rim_development import (CUT_CLAIMS, DEV_EXACT, DIAGNOSTICS, NUMERICAL,
                                            NUMERICAL_TOLERANCE_POLICY, TRIM_EXACT)
from glab.core.evidence import Requirement, validate_evidence
from glab.core.runfile import load_run, replay
from glab.two_rim.search import enumerated_candidate_search
from tests.two_rim_dev.helpers import developed, material, new_run, registry

SQ = [[0, 0], [0, 2], [2, 2], [2, 0]]
SQUARE = {"top": SQ, "bottom": SQ, "height": "3", "input_kind": "cyclic_boundary"}
NUMERICAL_CLAIMS = set(NUMERICAL) | {DIAGNOSTICS[0], DIAGNOSTICS[2]}
OTHER = copy.deepcopy(NUMERICAL_TOLERANCE_POLICY)
OTHER["length_tolerance"]["relative"] = 1e-6


def _evidence(run, d):
    return (run.check("two_rim.check.cut", 1, d["cut"], {}) +
            run.check("two_rim.check.development", 2, d["development"], {}) +
            run.check("two_rim.check.trimmed_development", 2, d["trimmed"], {}))


def test_policy_is_documented_and_distinguishes_threshold_kinds():
    p = NUMERICAL_TOLERANCE_POLICY
    assert "not a rigorous error bound" in p["status"]
    assert p["rigidity_threshold"]["units"] == "dimensionless"
    assert p["length_tolerance"]["units"] == "length"
    assert p["area_threshold"]["units"] == "area"
    assert p["angle_threshold"]["units"] == "radian"


def test_numerical_claims_carry_the_policy_and_exact_claims_do_not():
    run = new_run()
    evs = _evidence(run, developed(run, SQUARE, delta="1/4"))
    for e in evs:
        if e["claim"] in NUMERICAL_CLAIMS:
            assert e["tolerances"] == NUMERICAL_TOLERANCE_POLICY, e["claim"]
            assert "tau" in (e["receipt"] or {}), e["claim"]  # effective values stay in the receipt
        else:
            assert e["claim"] in set(CUT_CLAIMS) | set(DEV_EXACT) | set(TRIM_EXACT) | {DIAGNOSTICS[1]}
            assert e["tolerances"] is None, e["claim"]


def test_validate_and_summarize_against_matching_and_mismatched_policies():
    run = new_run()
    d = developed(run, SQUARE, delta="1/4")
    evs = _evidence(run, d)
    num = [e for e in evs if e["claim"] in NUMERICAL_CLAIMS]
    assert all(run.validate(e, expected_tolerances=NUMERICAL_TOLERANCE_POLICY)["status"] == "current" for e in num)
    assert all(run.validate(e, expected_tolerances=OTHER)["status"] == "policy_mismatch" for e in num)
    exact = [e for e in evs if e["claim"] not in NUMERICAL_CLAIMS]
    assert all(run.validate(e, expected_tolerances=None)["status"] == "current" for e in exact)
    req = [Requirement(c, d["trimmed"]) for c in NUMERICAL]
    assert run.summarize(req, expected_tolerances=NUMERICAL_TOLERANCE_POLICY)["outcome"] == "pass"
    bad = run.summarize(req, expected_tolerances=OTHER)
    assert bad["outcome"] != "pass" and all(r["invalid"] for r in bad["requirements"])


def test_search_can_require_the_numerical_policy():
    run = new_run()
    _, m = material(run, SQUARE)
    ok = enumerated_candidate_search(run, m, "1/4", expected_numerical_tolerances=NUMERICAL_TOLERANCE_POLICY)
    assert all(r["source_linked_trimmed_obligations"] == "pass" for r in ok["results"])
    run2 = new_run()
    _, m2 = material(run2, SQUARE)
    bad = enumerated_candidate_search(run2, m2, "1/4", expected_numerical_tolerances=OTHER)
    assert all(r["source_linked_trimmed_obligations"] != "pass" for r in bad["results"])


def test_policy_survives_save_load_and_replay(tmp_path):
    run = new_run()
    d = developed(run, SQUARE, delta="1/4")
    _evidence(run, d)
    path = tmp_path / "run.json"
    digest = run.save(path)
    loaded = load_run(path, expected_digest=digest)
    reg = registry()
    for e in loaded.record["evidence"]:
        if e["claim"] in NUMERICAL_CLAIMS:
            assert validate_evidence(e, loaded.store, reg,
                                     expected_tolerances=NUMERICAL_TOLERANCE_POLICY)["status"] == "current"
            assert validate_evidence(e, loaded.store, reg, expected_tolerances=OTHER)["status"] == "policy_mismatch"
    out = replay(loaded, reg)
    assert out["outcome"] == "reproduced" and out["run_digest_reproduced"]
