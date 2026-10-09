"""Stage 4B: the eleven-panel specimen at delta = 1/10000, all 605 pairs through the maintained checker.

The port is compared with the accepted Stage 4A prototype (probes/stage4a, kept unchanged) on the same exact inputs:
every Theorem S record and every interval row must be identical. Historical classes are read only after
classification, as a reference.
"""
from fractions import Fraction as F

import pytest

from glab.ideal_check.checker import IDEAL_CLAIMS
from probes.stage4a.classify import classify_seam, to_json
from probes.stage4a.ideal import model_from_payloads

from .helpers import E11, E11_DELTA, by_claim, check_ideal, ideal_lane, material, new_run, outcomes

SIDES = "two_rim.ideal.retained_hinge_sides_opposite"
THEOREM_S = "two_rim.ideal.retained_neighbours_interiors_disjoint"
REMAINING = "two_rim.ideal.remaining_pairs_interiors_disjoint"
PASSING = ["E0", "E1", "E2", "E4", "E5", "E6", "E7"]
FAILING = ["E3", "E8", "E9", "E10"]


@pytest.fixture(scope="module")
def e11():
    run = new_run()
    sm = material(run, E11)
    seams = {}
    for e in run.get(sm[1])["payload"]["hinges"]:
        lane = ideal_lane(run, E11, e["id"], E11_DELTA, source_material=sm)
        seams[e["id"]] = dict(lane, claims=by_claim(check_ideal(run, lane["ideal"])))
    return run, seams


def test_seven_ideal_seams_pass_and_four_fail(e11):
    _, seams = e11
    assert sorted(seams, key=lambda s: int(s[1:])) == [f"E{i}" for i in range(11)]
    for seam, s in seams.items():
        out = {c: e["outcome"] for c, e in s["claims"].items()}
        assert all(out[c] == "pass" for c in IDEAL_CLAIMS if c != REMAINING), (seam, out)
        assert out[REMAINING] == ("pass" if seam in PASSING else "fail"), seam
    assert sorted(s for s in seams if seams[s]["claims"][REMAINING]["outcome"] == "fail") == sorted(FAILING)


def test_all_605_pairs_decided_110_by_theorem_s_484_by_axes_11_by_witnesses(e11):
    _, seams = e11
    theorem_s = sum(len(s["claims"][THEOREM_S]["receipt"]["decided_pairs"]) for s in seams.values())
    rows = [r for s in seams.values() for r in s["claims"][REMAINING]["receipt"]["rows"]]
    methods = [r.get("method") for r in rows]
    assert theorem_s == 110 and len(rows) == 495 and theorem_s + len(rows) == 605
    assert methods.count("separating_axis") == 484 and methods.count("interior_witness") == 11
    assert all(r["outcome"] != "unknown" for r in rows)
    assert max(r["bits"] for r in rows) == 64
    for s in seams.values():
        cov = s["claims"]["two_rim.ideal.pair_coverage_complete"]["receipt"]
        assert (cov["expected_pairs"], cov["theorem_s_pairs"], cov["enclosure_pairs"]) == (55, 10, 45)


def test_known_overlap_f10_f7_at_e9_is_a_certified_witness(e11):
    _, seams = e11
    rows = {tuple(r["pair"]): r for r in seams["E9"]["claims"][REMAINING]["receipt"]["rows"]}
    row = rows.get(("F10", "F7")) or rows[("F7", "F10")]
    assert row["outcome"] == "fail" and row["method"] == "interior_witness"
    assert F(row["certificate"]["cross_lower_bound"]) > 0


def test_every_row_and_record_equals_the_accepted_prototype(e11):
    run, seams = e11
    for seam, s in seams.items():
        cut = run.get(s["cut"])["payload"]
        model = model_from_payloads(run.get(s["material"])["payload"], cut, E11_DELTA)
        proto = to_json(classify_seam(model))["rows"]
        shared = [r["shared_hinge"] for r in proto if r.get("method") == "shared_hinge_exact"]
        others = [r for r in proto if r.get("method") != "shared_hinge_exact"]
        assert s["claims"][SIDES]["receipt"]["rows"] == shared, seam
        assert s["claims"][REMAINING]["receipt"]["rows"] == others, seam


def test_verdicts_agree_with_the_mapped_historical_classes_after_classification(e11):
    from tests.two_rim_dev.eleven_panel import build_mapping, load_certificate   # reference only, read afterwards
    run, seams = e11
    cert = load_certificate()
    mapping = build_mapping(run.get(next(iter(seams.values()))["material"])["payload"], cert)
    for k in range(mapping["n"]):
        seam = mapping["cuts"][k]
        expected = "fail" if k in cert["unsafe_cuts"] else "pass"
        assert seams[seam]["claims"][REMAINING]["outcome"] == expected, (k, seam)
