"""Stage 4B: the ideal state, its action, and schema/domain/convention checks before any interpretation."""
import pytest

from glab.ideal_check.checker import IDEAL_CLAIMS, IDEAL_POLICY
from glab.core.registry import RegistryError

from .helpers import (IDEAL_CHECKER, IDEAL_KIND, NORMALIZATION, ORIENTATION, SQUARE, by_claim, check_ideal,
                      ideal_lane, material, new_run, outcomes, raw_ideal, succeeded)

AFTER_DOMAIN = IDEAL_CLAIMS[3:]    # premises and every geometric claim


def test_define_records_the_cut_copy_and_the_fixed_conventions():
    run = new_run()
    lane = ideal_lane(run, SQUARE, "E0", "1/4")
    state = run.get(lane["ideal"])
    assert state["kind"] == IDEAL_KIND and state["representation"] == "exact" and state["parent"] == lane["cut"]
    assert state["payload"] == {"schema": "two_rim.ideal_trim/1", "definition": "two_rim.ideal_development/1",
                                "delta": "1/4", "orientation": ORIENTATION, "normalization": NORMALIZATION,
                                "cut": run.get(lane["cut"])["payload"]}


@pytest.mark.parametrize("delta", ["2/8", " 1/4", "0.25", "1e-4", "0", "1/2", "3/4", "-1/4", "1/0", 1])
def test_define_refuses_noncanonical_or_unsupported_delta_without_a_state(delta):
    run = new_run()
    _, m = material(run, SQUARE)
    c = succeeded(run.apply("two_rim.cut.open", 1, {"seam": "E0"}, m))
    before = len(run.to_record()["states"])
    res = run.apply("two_rim.ideal.define", 1, {"delta": delta}, c)
    assert res["status"] in ("failed", "rejected") and res["output"] is None
    assert len(run.to_record()["states"]) == before


@pytest.mark.parametrize("delta", [True, None, 0.25])
def test_define_rejects_non_exact_parameters_at_validation(delta):
    run = new_run()
    _, m = material(run, SQUARE)
    c = succeeded(run.apply("two_rim.cut.open", 1, {"seam": "E0"}, m))
    assert run.apply("two_rim.ideal.define", 1, {"delta": delta}, c)["status"] == "rejected"


def test_define_accepts_only_an_exact_cut_parent_never_a_float_state():
    run = new_run()
    _, m = material(run, SQUARE)
    c = succeeded(run.apply("two_rim.cut.open", 1, {"seam": "E0"}, m))
    d = succeeded(run.apply("two_rim.develop.static", 1, {}, c))
    t = succeeded(run.apply("two_rim.trim.apply", 1, {"delta": "1/4"}, d))
    for parent in (m, d, t):
        res = run.apply("two_rim.ideal.define", 1, {"delta": "1/4"}, parent)
        assert res["status"] == "rejected" and "accepts two_rim.cut" in res["failure"]["message"]


def test_the_ideal_checker_accepts_only_ideal_states():
    run = new_run()
    lane = ideal_lane(run, SQUARE, "E0", "1/4")
    d = succeeded(run.apply("two_rim.develop.static", 1, {}, lane["cut"]))
    t = succeeded(run.apply("two_rim.trim.apply", 1, {"delta": "1/4"}, d))
    for subject in (lane["cut"], d, t):
        with pytest.raises(RegistryError):
            run.check(*IDEAL_CHECKER, subject, {})
    assert run.checks[-1]["status"] == "rejected" and run.checks[-1]["evidence"] == []


def test_claims_follow_the_published_contract():
    run = new_run()
    evs = check_ideal(run, ideal_lane(run, SQUARE, "E0", "1/4")["ideal"])
    assert [e["claim"] for e in evs] == list(IDEAL_CLAIMS)
    assert IDEAL_CLAIMS == ("two_rim.ideal.record_schema", "two_rim.ideal.cut_copy_matches_parent",
                            "two_rim.ideal.delta_in_supported_domain", "two_rim.ideal.local_premises",
                            "two_rim.ideal.retained_hinge_sides_opposite",
                            "two_rim.ideal.retained_neighbours_interiors_disjoint",
                            "two_rim.ideal.remaining_pairs_interiors_disjoint",
                            "two_rim.ideal.pair_coverage_complete")
    meta = {e["claim"]: (e["method"], e["numeric_domain"], e["coverage"], e["tolerances"]) for e in evs}
    exact = ("exact_computation", "exact_rational")
    for claim in IDEAL_CLAIMS[:5] + IDEAL_CLAIMS[7:]:
        cov = "retained_hinge_pairs" if claim.endswith("sides_opposite") else "all"
        assert meta[claim] == exact + (cov, None), claim
    assert meta[IDEAL_CLAIMS[5]] == exact + ("retained_hinge_pairs", IDEAL_POLICY)
    assert meta[IDEAL_CLAIMS[6]] == ("rigorous_enclosure", "rational_interval", "pairs_not_decided_by_theorem_s",
                                     IDEAL_POLICY)
    assert all(e["method"] != "formal_proof" for e in evs)
    assert all(e["representation"] == "exact" and e["params"] == {} for e in evs)


SCHEMA_FAULTS = ["extra_key", "missing_key", "wrong_schema", "wrong_definition", "prototype_definition",
                 "wrong_orientation", "wrong_normalization", "delta_int", "cut_not_object"]


@pytest.mark.parametrize("mutation", SCHEMA_FAULTS)
def test_schema_or_convention_faults_stop_all_interpretation(mutation):
    run = new_run(test_actions=True)
    _, m = material(run, SQUARE)
    c = succeeded(run.apply("two_rim.cut.open", 1, {"seam": "E0"}, m))
    evs = check_ideal(run, succeeded(raw_ideal(run, c, mutation)))
    out = outcomes(evs)
    assert out[IDEAL_CLAIMS[0]] == "fail"
    assert all(out[c] == "unknown" for c in IDEAL_CLAIMS[1:]), out
    assert all("not_interpreted" in by_claim(evs)[c]["receipt"] for c in IDEAL_CLAIMS[1:])


@pytest.mark.parametrize("delta", ["2/8", " 1/4", "0.25", "1e-4"])
def test_noncanonical_delta_in_a_record_is_a_schema_fault(delta):
    run = new_run(test_actions=True)
    _, m = material(run, SQUARE)
    c = succeeded(run.apply("two_rim.cut.open", 1, {"seam": "E0"}, m))
    out = outcomes(check_ideal(run, succeeded(raw_ideal(run, c, "none", delta=delta))))
    assert out[IDEAL_CLAIMS[0]] == "fail" and set(out[c] for c in IDEAL_CLAIMS[1:]) == {"unknown"}


@pytest.mark.parametrize("delta", ["0", "1/2", "3/4", "-1/4", "7"])
def test_delta_outside_the_domain_is_unsupported_input_never_an_overlap(delta):
    run = new_run(test_actions=True)
    _, m = material(run, SQUARE)
    c = succeeded(run.apply("two_rim.cut.open", 1, {"seam": "E0"}, m))
    evs = check_ideal(run, succeeded(raw_ideal(run, c, "none", delta=delta)))
    out = outcomes(evs)
    assert out[IDEAL_CLAIMS[0]] == "pass" and out[IDEAL_CLAIMS[1]] == "pass"
    assert out["two_rim.ideal.delta_in_supported_domain"] == "fail"
    assert all(out[c] == "unknown" for c in AFTER_DOMAIN), out
    assert all("unsupported input" in by_claim(evs)[c]["receipt"]["not_interpreted"] for c in AFTER_DOMAIN)
