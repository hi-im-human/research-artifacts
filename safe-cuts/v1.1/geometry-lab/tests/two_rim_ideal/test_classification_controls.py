"""Stage 4B: prototype controls C2, C4, C5, C6 on the maintained geometry, budget exhaustion and honest unknowns.

Ported from probes/stage4a/tests/controls (test_c4_c6_c7_specimens.py blob e5cf8fb3, test_c5_synthetic_pairs.py blob
97b90062) with imports changed to the maintained modules; claim-level unknowns use a test-only registered checker.
"""
import copy
from fractions import Fraction as F

import pytest

from glab.ideal_check.geometry import (SCHEDULE, classify_pair, classify_seam, decide_boxes, enclose,
                                       model_from_payloads, shared_hinge_decision)
from glab.ideal_check.checker import IDEAL_POLICY, enclosure_policy, ideal_claims
from glab.core.registry import CheckerSpec
from glab.rigorous.ratint import Interval, IntervalError

from .helpers import E11, E11_DELTA, by_claim, check_ideal, ideal_lane, material, new_run, outcomes

REMAINING = "two_rim.ideal.remaining_pairs_interiors_disjoint"


@pytest.fixture(scope="module")
def e11_payloads():
    run = new_run()
    sm = material(run, E11)
    lanes = {s: ideal_lane(run, E11, s, E11_DELTA, source_material=sm) for s in ("E4", "E9")}
    mat = run.get(sm[1])["payload"]
    return mat, {s: run.get(lane["cut"])["payload"] for s, lane in lanes.items()}


@pytest.fixture(scope="module")
def e9(e11_payloads):
    mat, cuts = e11_payloads
    return model_from_payloads(mat, cuts["E9"], E11_DELTA)


# ---------------------------------------------------------------- C5 synthetic pairs

def square(x0, y0, s=F(1)):
    pts = [(x0, y0), (x0 + s, y0), (x0 + s, y0 + s), (x0, y0 + s)]
    return [(Interval.exact(F(x)), Interval.exact(F(y))) for x, y in pts]


def widen(poly, eps):
    return [(Interval(x.lo - eps, x.hi + eps), Interval(y.lo - eps, y.hi + eps)) for x, y in poly]


def test_overlap_is_a_certified_fail_with_a_witness_inside_both():
    out, d = decide_boxes(square(0, 0), square(F(1, 2), F(1, 2)), True)
    assert out == "fail" and d["method"] == "interior_witness" and d["cross_lower_bound"] > 0
    assert F(1, 2) < d["witness"][0] < 1 and F(1, 2) < d["witness"][1] < 1


def test_separation_is_a_certified_pass_with_a_gap():
    out, d = decide_boxes(square(0, 0), square(2, 0), True)
    assert out == "pass" and d["method"] == "separating_axis" and d["euclidean_gap_lower_bound"] > F(99, 100)


def test_exact_touching_is_a_pass_boundary_contact_allowed():
    out, d = decide_boxes(square(0, 0), square(1, 0), True)
    assert out == "pass" and d["axis_gap"] == 0


def test_touching_with_enclosure_width_is_unknown_not_a_verdict():
    out, _ = decide_boxes(widen(square(0, 0), F(1, 2**40)), widen(square(1, 0), F(1, 2**40)), True)
    assert out == "unknown"


@pytest.mark.parametrize("shift, eps_bits, expected", [(1 - F(1, 2**60), 16, "unknown"), (1 - F(1, 2**60), 100, "fail"),
                                                       (1 + F(1, 2**60), 16, "unknown"), (1 + F(1, 2**60), 100, "pass")])
def test_near_touch_resolves_only_with_precision(shift, eps_bits, expected):
    P = widen(square(0, 0), F(1, 2**eps_bits))
    Q = widen(square(shift, 0), F(1, 2**eps_bits))
    assert decide_boxes(P, Q, True)[0] == expected


def test_overlap_without_certified_orientation_is_never_a_fail():
    out, d = decide_boxes(square(0, 0), square(F(1, 2), F(1, 2)), False)
    assert out == "unknown" and "not certified" in d["reason"]


def test_wide_boxes_never_produce_a_verdict():
    assert decide_boxes(widen(square(0, 0), F(3)), widen(square(F(1, 2), 0), F(3)), True)[0] == "unknown"


# ---------------------------------------------------------------- C4 low precision, budget exhaustion

def test_low_precision_never_gives_a_false_verdict(e9):
    high = classify_seam(e9, schedule=(128,))
    decided = {tuple(r["pair"]): r["outcome"] for r in high["rows"] if r.get("method") != "shared_hinge_exact"}
    assert set(decided.values()) == {"pass", "fail"}
    partial = False
    for bits in (0, 2, 4, 8, 16, 32, 40, 48, 56):
        outs = []
        for r in classify_seam(e9, schedule=(bits,))["rows"]:
            if r.get("method") == "shared_hinge_exact":
                continue
            outs.append(r["outcome"])
            assert r["outcome"] in ("unknown", decided[tuple(r["pair"])]), (bits, r["pair"], r["outcome"])
        partial = partial or ("unknown" in outs and any(o != "unknown" for o in outs))
    assert partial


def test_known_overlap_is_unknown_at_very_low_precision_and_fail_at_high(e9):
    assert classify_pair(e9, "F10", "F7", schedule=(0,))["outcome"] == "unknown"
    row = classify_pair(e9, "F10", "F7", schedule=(64,))
    assert row["outcome"] == "fail" and row["method"] == "interior_witness"


def test_budget_exhaustion_is_unknown_with_every_attempt_recorded(e9):
    row = classify_pair(e9, "F10", "F7", schedule=(0, 1, 2))
    assert row["outcome"] == "unknown" and row["reason"] == "budget_exhausted"
    assert [a["bits"] for a in row["attempts"]] == [0, 1, 2] and "certificate" not in row
    assert SCHEDULE == (16, 32, 64, 128, 256, 512) and IDEAL_POLICY["precision_schedule"] == list(SCHEDULE)


def test_zero_denominator_in_classification_is_unknown(e11_payloads):
    mat, cuts = e11_payloads
    material = copy.deepcopy(mat)
    h = next(e for e in material["hinges"] if e["id"] == "E5")
    upper = next(v for v in material["vertices"] if v["id"] == h["upper"])
    lower = next(v for v in material["vertices"] if v["id"] == h["lower"])
    upper["xyz"] = list(lower["xyz"])   # L = U: |e| = 0
    model = model_from_payloads(material, dict(cuts["E9"], material=material), E11_DELTA)
    with pytest.raises(IntervalError):
        enclose(model, 64)
    res = classify_seam(model, schedule=(64,))
    assert all(r["outcome"] == "unknown" for r in res["rows"] if r.get("method") != "shared_hinge_exact")
    assert any("zero_denominator" in r.get("reason", "") for r in res["rows"])


# ---------------------------------------------------------------- C6 incorrect shared-hinge mapping

def test_valid_retained_neighbours_pass_by_exact_sides(e9):
    a, b = e9.chain[3], e9.chain[4]
    row = shared_hinge_decision(e9, a, b, e9.faces[a]["exit"])
    assert row["outcome"] == "pass" and set(row["sides"].values()) == {-1, 1}


def test_wrong_hinge_nonconsecutive_faces_and_the_seam_pair_are_refused(e9):
    a, b = e9.chain[3], e9.chain[4]
    assert shared_hinge_decision(e9, a, b, e9.faces[a]["entry"])["outcome"] == "unknown"
    assert shared_hinge_decision(e9, e9.chain[2], e9.chain[4], e9.faces[e9.chain[2]]["exit"])["outcome"] == "unknown"
    first, last = e9.chain[0], e9.chain[-1]
    row = shared_hinge_decision(e9, last, first, e9.seam)
    assert row["outcome"] == "unknown" and any("seam" in p for p in row["problems"])
    assert classify_pair(e9, first, last, schedule=(128,)).get("method") != "shared_hinge_exact"


def _tampered(e11_payloads, mutate):
    mat, cuts = e11_payloads
    material = copy.deepcopy(mat)
    mutate(material, cuts["E9"]["face_order"])
    return model_from_payloads(material, dict(cuts["E9"], material=material), E11_DELTA)


def test_matching_hinge_ids_with_a_different_endpoint_are_refused(e11_payloads):
    def mutate(material, order):
        b = next(f for f in material["faces"] if f["id"] == order[4])
        h = next(e for e in material["hinges"] if e["id"] == b["entry"])
        old = next(v for v in material["vertices"] if v["id"] == h["lower"])
        material["vertices"].append({"id": "Bcopy", "rim": old["rim"], "xyz": list(old["xyz"])})
        b["boundary"] = ["Bcopy" if v == h["lower"] else v for v in b["boundary"]]
    m = _tampered(e11_payloads, mutate)
    row = shared_hinge_decision(m, m.chain[3], m.chain[4], m.faces[m.chain[3]]["exit"])
    assert row["outcome"] == "unknown" and any("lacks the hinge endpoint" in p for p in row["problems"])


def test_inward_normal_is_refused(e11_payloads):
    def mutate(material, order):
        b = next(f for f in material["faces"] if f["id"] == order[4])
        b["plane"] = [-c for c in b["plane"]]
    m = _tampered(e11_payloads, mutate)
    row = shared_hinge_decision(m, m.chain[3], m.chain[4], m.faces[m.chain[3]]["exit"])
    assert row["outcome"] == "unknown" and any("opposite" in p for p in row["problems"])


# ---------------------------------------------------------------- claim level: an honest unknown

def _low_precision_checker(bits):
    def fn(state, params, context):
        return ideal_claims(state, context, schedule=(bits,))
    return CheckerSpec("test.check.ideal_low_precision", 1, "two_rim.ideal_trimmed_development", {}, "test-only", fn,
                       uses_context=True)


def test_low_precision_claims_are_unknown_never_fabricated_and_declare_their_own_policy():
    run = new_run(extra_checkers=[_low_precision_checker(2)])
    lane = ideal_lane(run, E11, "E4", E11_DELTA)
    full = by_claim(check_ideal(run, lane["ideal"]))
    low = by_claim(run.check("test.check.ideal_low_precision", 1, lane["ideal"], {}))
    assert low[REMAINING]["outcome"] == "unknown" and full[REMAINING]["outcome"] == "pass"
    decided = {tuple(r["pair"]): r["outcome"] for r in full[REMAINING]["receipt"]["rows"]}
    for r in low[REMAINING]["receipt"]["rows"]:
        assert r["outcome"] in ("unknown", decided[tuple(r["pair"])])
        if r["outcome"] == "unknown":
            assert r["reason"] == "budget_exhausted" or r["reason"].startswith("error:")
    assert low[REMAINING]["tolerances"] == enclosure_policy((2,)) != IDEAL_POLICY
    # exact claims do not depend on precision
    assert {c: low[c]["outcome"] for c in low if c != REMAINING} == \
        {c: full[c]["outcome"] for c in full if c != REMAINING}
    assert outcomes(check_ideal(run, lane["ideal"])) == {c: e["outcome"] for c, e in full.items()}
