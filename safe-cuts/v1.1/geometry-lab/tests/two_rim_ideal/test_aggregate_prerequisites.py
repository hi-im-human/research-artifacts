"""Stage 4B: the source-linked ideal aggregate and the geometric verdict on D.

A source-linked verdict needs complete, current, passing source, material and cut evidence from the expected
checkers, plus every ideal claim under the expected policy. Missing, stale, failing, foreign or policy-mismatched
evidence gives `not_determined`, never an overlap and never a pass.
"""
import json

import pytest

from glab.core.registry import CheckerSpec
from glab.ideal_check.checker import IDEAL_CLAIMS, IDEAL_POLICY, enclosure_policy, ideal_claims
from glab.two_rim import ideal_search
from glab.two_rim.ideal_search import AGGREGATE, ideal_candidate_search, ideal_obligations

from .helpers import (E11, E11_DELTA, IDEAL_CHECKER, SQUARE, fake_source_checker, ideal_lane, material, new_run,
                      raw_ideal, succeeded)

PASSING = ["E0", "E1", "E2", "E4", "E5", "E6", "E7"]
FAILING = ["E3", "E8", "E9", "E10"]


@pytest.fixture(scope="module")
def e11_search():
    run = new_run()
    _, m = material(run, E11)
    return run, ideal_candidate_search(run, m, E11_DELTA, expected_policy=IDEAL_POLICY)


def _checked_lane(run, params, seam, delta, *, source=True, material_check=True, cut=True, ideal=True):
    lane = ideal_lane(run, params, seam, delta)
    if source:
        run.check("two_rim.check.source", 2, lane["source"], {})
    if material_check:
        run.check("two_rim.check.material", 2, lane["material"], {})
    if cut:
        run.check("two_rim.check.cut", 1, lane["cut"], {})
    if ideal:
        run.check(*IDEAL_CHECKER, lane["ideal"], {})
    return lane


def test_e11_search_gives_seven_source_linked_passes_and_four_certified_overlaps(e11_search):
    _, result = e11_search
    rows = {r["seam"]: r for r in result["results"]}
    assert result["prerequisites"]["source"]["status"] == "checked"
    assert result["prerequisites"]["material"]["status"] == "checked"
    for seam in PASSING:
        assert rows[seam][AGGREGATE] == "pass" and rows[seam]["ideal_geometric_verdict"]["verdict"] == "pass", seam
    for seam in FAILING:
        assert rows[seam][AGGREGATE] == "fail" and rows[seam]["ideal_geometric_verdict"]["verdict"] == "fail", seam
    for r in rows.values():
        ob = r["obligations"]
        assert len(ob["requirements"]) == 4 + 5 + 5 + 8 and ob["identity_problems"] == []
        assert {row["role"] for row in ob["requirements"]} == {"source", "material", "cut", "ideal"}
        assert all(row["evidence"] for row in ob["requirements"])


def test_aggregate_definition_names_every_requirement_and_policy(e11_search):
    _, result = e11_search
    definition = result["aggregate_definition"]
    assert definition["name"] == AGGREGATE and "not_determined" in definition["verdicts"]
    assert result["expected_policy"] == IDEAL_POLICY
    assert ideal_search.IDEAL_OBLIGATIONS == IDEAL_CLAIMS    # kept in step with the checker, never imported by it
    assert ideal_search.CHECKERS["ideal"] == IDEAL_CHECKER


@pytest.mark.parametrize("missing", ["source", "material_check", "cut", "ideal"])
def test_missing_prerequisite_evidence_gives_no_geometric_verdict(missing):
    run = new_run()
    lane = _checked_lane(run, E11, "E4", E11_DELTA, **{missing: False})     # E4: a seam whose D passes
    ob = ideal_obligations(run, lane["ideal"], expected_policy=IDEAL_POLICY)
    assert ob["outcome"] == "not_run" and ob["ideal_geometric_verdict"]["verdict"] == "not_determined"


def test_a_complete_lane_outside_the_search_has_the_same_verdict():
    run = new_run()
    lane = _checked_lane(run, E11, "E9", E11_DELTA)
    ob = ideal_obligations(run, lane["ideal"], expected_policy=IDEAL_POLICY)
    assert ob["outcome"] == "fail" and ob["ideal_geometric_verdict"]["verdict"] == "fail"


def test_a_substituted_source_fails_its_prerequisite_and_blocks_the_overlap_verdict():
    run = new_run(test_actions=True)
    square_source, _ = material(run, SQUARE)
    _, e11_material = material(run, E11)
    adopted = succeeded(run.apply("test.material.adopted", 1,
                                  {"payload": json.dumps(run.get(e11_material)["payload"])}, square_source))
    c = succeeded(run.apply("two_rim.cut.open", 1, {"seam": "E9"}, adopted))
    i = succeeded(run.apply("two_rim.ideal.define", 1, {"delta": E11_DELTA}, c))
    for name, version, subject in (("two_rim.check.source", 2, square_source), ("two_rim.check.material", 2, adopted),
                                   ("two_rim.check.cut", 1, c), (*IDEAL_CHECKER, i)):
        run.check(name, version, subject, {})
    ob = ideal_obligations(run, i, expected_policy=IDEAL_POLICY)
    ideal_rows = [r for r in ob["requirements"] if r["role"] == "ideal"]
    assert any(r["claim"] == "two_rim.ideal.remaining_pairs_interiors_disjoint" and r["outcome"] == "fail"
               for r in ideal_rows)                                    # the geometry of D alone does fail ...
    assert any(r["claim"] == "two_rim.material.matches_parent_source" and r["outcome"] == "fail"
               for r in ob["requirements"])
    assert ob["outcome"] == "fail" and ob["ideal_geometric_verdict"]["verdict"] == "not_determined"  # ... not linked


@pytest.mark.parametrize("mutation", ["other_seam_cut", "nested_coordinate", "extra_key"])
def test_a_substituted_or_mutated_ideal_record_gives_no_geometric_verdict(mutation):
    run = new_run(test_actions=True)
    s, m = material(run, E11)
    c = succeeded(run.apply("two_rim.cut.open", 1, {"seam": "E9"}, m))
    i = succeeded(raw_ideal(run, c, mutation, delta=E11_DELTA, arg={"seam": "E4"}))
    for name, version, subject in (("two_rim.check.source", 2, s), ("two_rim.check.material", 2, m),
                                   ("two_rim.check.cut", 1, c), (*IDEAL_CHECKER, i)):
        run.check(name, version, subject, {})
    ob = ideal_obligations(run, i, expected_policy=IDEAL_POLICY)
    assert ob["outcome"] == "fail" and ob["ideal_geometric_verdict"]["verdict"] == "not_determined"


def test_a_wrong_checker_identity_never_counts_as_a_prerequisite():
    run = new_run(extra_checkers=[fake_source_checker()])
    lane = _checked_lane(run, E11, "E4", E11_DELTA, source=False)
    run.check("test.fake.check.source", 2, lane["source"], {})
    ob = ideal_obligations(run, lane["ideal"], expected_policy=IDEAL_POLICY)
    source_rows = [r for r in ob["requirements"] if r["role"] == "source"]
    assert all(r["outcome"] == "pass" for r in source_rows)          # the core summary alone would accept them ...
    assert ob["identity_problems"] and all(r["identity_problems"] for r in source_rows)
    assert ob["outcome"] == "unknown" and ob["ideal_geometric_verdict"]["verdict"] == "not_determined"  # ... never here


def test_a_different_expected_policy_is_a_mismatch_not_a_pass():
    run = new_run()
    lane = _checked_lane(run, E11, "E4", E11_DELTA)
    ob = ideal_obligations(run, lane["ideal"], expected_policy=enclosure_policy((16, 32)))
    mismatched = [r for r in ob["requirements"] if r["invalid"]]
    assert {r["claim"] for r in mismatched} == {"two_rim.ideal.retained_neighbours_interiors_disjoint",
                                                "two_rim.ideal.remaining_pairs_interiors_disjoint"}
    assert all(i["status"] == "policy_mismatch" for r in mismatched for i in r["invalid"])
    assert ob["outcome"] == "unknown" and ob["ideal_geometric_verdict"]["verdict"] == "not_determined"


def test_expected_policy_is_required():
    run = new_run()
    lane = _checked_lane(run, SQUARE, "E0", "1/4")
    with pytest.raises(TypeError):
        ideal_obligations(run, lane["ideal"])


def test_honest_unknown_pairs_give_unknown_never_a_pass():
    low = CheckerSpec(IDEAL_CHECKER[0], IDEAL_CHECKER[1], "two_rim.ideal_trimmed_development", {},
                      "test-only-low-precision", lambda s, p, c: ideal_claims(s, c, schedule=(2,)), uses_context=True)
    run = new_run(replace_checkers=[low])
    lane = _checked_lane(run, E11, "E4", E11_DELTA)
    ob = ideal_obligations(run, lane["ideal"], expected_policy=enclosure_policy((2,)))
    remaining = next(r for r in ob["requirements"] if r["claim"] == "two_rim.ideal.remaining_pairs_interiors_disjoint")
    assert remaining["outcome"] == "unknown" and remaining["reason"] == ""       # valid evidence that says unknown
    assert ob["outcome"] == "unknown" and ob["ideal_geometric_verdict"]["verdict"] == "unknown"


def test_unsupported_delta_creates_nothing_and_decides_nothing():
    run = new_run()
    _, m = material(run, SQUARE)
    result = ideal_candidate_search(run, m, "1/2", expected_policy=IDEAL_POLICY)
    for r in result["results"]:
        assert r["ideal"] is None and r[AGGREGATE] == "not_run"
        assert r["ideal_geometric_verdict"]["verdict"] == "not_determined"


def test_square_prism_search_passes_every_seam():
    run = new_run()
    _, m = material(run, SQUARE)
    result = ideal_candidate_search(run, m, "1/3", expected_policy=IDEAL_POLICY)
    assert [r["ideal_geometric_verdict"]["verdict"] for r in result["results"]] == ["pass"] * 4
