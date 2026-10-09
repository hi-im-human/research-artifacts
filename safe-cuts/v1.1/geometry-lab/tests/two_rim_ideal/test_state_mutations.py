"""Stage 4B: substitutions and nested mutation of the ideal record; ancestors that are not an exact cut."""
import pytest

from glab.ideal_check.checker import IDEAL_CLAIMS

from .helpers import (E11, E11_DELTA, SQUARE, by_claim, check_ideal, ideal_lane, material, new_run, outcomes,
                      raw_ideal, succeeded)

COPY = "two_rim.ideal.cut_copy_matches_parent"


@pytest.fixture(scope="module")
def run_and_cuts():
    run = new_run(test_actions=True)
    sm = material(run, E11)
    cuts = {s: succeeded(run.apply("two_rim.cut.open", 1, {"seam": s}, sm[1])) for s in ("E4", "E9")}
    return run, sm, cuts


def test_the_raw_control_equals_the_maintained_action(run_and_cuts):
    run, _, cuts = run_and_cuts
    raw = succeeded(raw_ideal(run, cuts["E9"], "none", delta=E11_DELTA))
    assert raw == succeeded(run.apply("two_rim.ideal.define", 1, {"delta": E11_DELTA}, cuts["E9"]))


@pytest.mark.parametrize("mutation", ["other_seam_cut", "nested_coordinate", "other_material_cut"])
def test_a_substituted_or_mutated_cut_copy_fails_the_copy_claim(run_and_cuts, mutation):
    run, _, cuts = run_and_cuts
    arg = {"seam": "E4"}
    if mutation == "other_material_cut":
        other = new_run()
        arg = {"cut": other.get(ideal_lane(other, SQUARE, "E0", "1/4")["cut"])["payload"]}
    evs = by_claim(check_ideal(run, succeeded(raw_ideal(run, cuts["E9"], mutation, delta=E11_DELTA, arg=arg))))
    assert evs["two_rim.ideal.record_schema"]["outcome"] == "pass"
    assert evs[COPY]["outcome"] == "fail" and evs[COPY]["receipt"]["cut_copy_matches_parent_cut"] is False
    # the geometry is reconstructed from the ACTUAL ancestors (the E9 cut), never from the carried copy
    genuine = by_claim(check_ideal(run, succeeded(run.apply("two_rim.ideal.define", 1, {"delta": E11_DELTA},
                                                                cuts["E9"]))))
    for claim in IDEAL_CLAIMS[2:]:
        assert evs[claim]["outcome"] == genuine[claim]["outcome"]
        assert evs[claim]["receipt"] == genuine[claim]["receipt"]


def test_an_ideal_record_under_a_float_state_is_never_interpreted():
    run = new_run(test_actions=True)
    lane = ideal_lane(run, SQUARE, "E0", "1/4")
    d = succeeded(run.apply("two_rim.develop.static", 1, {}, lane["cut"]))
    foreign = succeeded(run.apply("test.ideal.on_float_parent", 1, {"delta": "1/4"}, d))
    evs = by_claim(check_ideal(run, foreign))
    assert evs[COPY]["outcome"] == "fail" and "ancestors" in " ".join(evs[COPY]["receipt"]["problems"])
    assert all(evs[c]["outcome"] == "unknown" for c in IDEAL_CLAIMS[3:])
    assert all(e["subject"] == foreign for e in evs.values())


def test_mutating_returned_records_changes_nothing_retained(run_and_cuts):
    run, _, cuts = run_and_cuts
    i = succeeded(run.apply("two_rim.ideal.define", 1, {"delta": E11_DELTA}, cuts["E4"]))
    evs = check_ideal(run, i)
    attempt, claim = evs[6]["attempt"], evs[6]["claim"]
    state = run.get(i)
    state["payload"]["cut"]["material"]["vertices"][0]["xyz"][0] = "12345"
    evs[6]["receipt"]["rows"][0]["outcome"] = "fail"
    assert run.get(i)["payload"]["cut"] == run.get(cuts["E4"])["payload"]
    assert outcomes(check_ideal(run, i)) == {c: "pass" for c in IDEAL_CLAIMS}
    kept = next(e for e in run.evidence if e["attempt"] == attempt and e["claim"] == claim)
    assert kept["receipt"]["rows"][0]["outcome"] == "pass"
