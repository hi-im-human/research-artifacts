"""Stage 4B firewall: ideal evidence never transfers to float states, and the float lane is unchanged.

The eleven-panel float search keeps its seven `unknown` trimmed totals on the historically safe seams; running the
ideal lane in the same Run changes none of its states, evidence or totals.
"""
import pytest

from glab.core.evidence import Requirement
from glab.ideal_check.checker import IDEAL_CLAIMS, IDEAL_POLICY
from glab.two_rim.ideal_search import ideal_candidate_search
from glab.two_rim.search import enumerated_candidate_search

from .helpers import E11, E11_DELTA, IDEAL_CHECKER, material, new_run

SAFE = ["E0", "E1", "E2", "E4", "E5", "E6", "E7"]
PAIRS = "two_rim.development.face_interiors_disjoint_all_pairs"


@pytest.fixture(scope="module")
def both_lanes():
    run = new_run()
    _, m = material(run, E11)
    float_before = enumerated_candidate_search(run, m, E11_DELTA)
    evidence_before = run.evidence
    ideal = ideal_candidate_search(run, m, E11_DELTA, expected_policy=IDEAL_POLICY)
    return run, m, float_before, evidence_before, ideal


def test_the_float_lane_keeps_its_unknowns_and_nothing_is_relabelled(both_lanes):
    run, m, before, evidence_before, ideal = both_lanes
    rows = {r["seam"]: r for r in before["results"]}
    for seam in SAFE:
        assert rows[seam]["trimmed_claims"][PAIRS] == "unknown", seam
        assert rows[seam]["source_linked_trimmed_obligations"] == "unknown", seam
    assert {r["seam"]: r["ideal_geometric_verdict"]["verdict"] for r in ideal["results"]
            if r["seam"] in SAFE} == {s: "pass" for s in SAFE}
    # the earlier float records are untouched by the ideal lane
    assert run.evidence[:len(evidence_before)] == evidence_before


def test_float_totals_are_identical_after_the_ideal_lane(both_lanes):
    run, m, before, _, _ = both_lanes
    after = enumerated_candidate_search(run, m, E11_DELTA)
    strip = lambda res: [{k: v for k, v in r.items()} for r in res["results"]]   # noqa: E731
    assert strip(after) == strip(before)
    assert set(after) == set(before) and "source_linked_ideal_trimmed_obligations" not in after["aggregate_definitions"]


def test_ideal_evidence_never_applies_to_a_float_subject_or_the_reverse(both_lanes):
    run, _, before, _, ideal = both_lanes
    float_row = next(r for r in before["results"] if r["seam"] == "E4")
    ideal_row = next(r for r in ideal["results"] if r["seam"] == "E4")
    for float_subject in (float_row["development"], float_row["trimmed"]):
        summary = run.summarize([Requirement(c, float_subject) for c in IDEAL_CLAIMS])
        assert {r["outcome"] for r in summary["requirements"]} == {"not_run"}
    summary = run.summarize([Requirement(PAIRS, ideal_row["ideal"])])
    assert summary["requirements"][0]["outcome"] == "not_run"
    ideal_evidence = [e for e in run.evidence if e["checker"] == IDEAL_CHECKER[0]]
    assert ideal_evidence and all(run.get(e["subject"])["kind"] == "two_rim.ideal_trimmed_development"
                                  for e in ideal_evidence)
    assert all(run.get(e["subject"])["representation"] == "exact" for e in ideal_evidence)
