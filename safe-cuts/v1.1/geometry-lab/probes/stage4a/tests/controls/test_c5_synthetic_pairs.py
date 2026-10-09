"""Stage 4A control C5 (isolated prototype): overlap versus separation versus exact touching, with widths."""
from fractions import Fraction as F

import pytest

from probes.stage4a.classify import decide_boxes
from probes.stage4a.ratint import Interval


def square(x0, y0, s=F(1)):
    """Counterclockwise exact square as interval boxes."""
    pts = [(x0, y0), (x0 + s, y0), (x0 + s, y0 + s), (x0, y0 + s)]
    return [(Interval.exact(F(x)), Interval.exact(F(y))) for x, y in pts]


def widen(poly, eps):
    return [(Interval(x.lo - eps, x.hi + eps), Interval(y.lo - eps, y.hi + eps)) for x, y in poly]


def test_overlap_is_a_certified_fail_with_a_witness_inside_both():
    out, d = decide_boxes(square(0, 0), square(F(1, 2), F(1, 2)), True)
    assert out == "fail" and d["method"] == "interior_witness" and d["cross_lower_bound"] > 0
    y = d["witness"]
    assert F(1, 2) < y[0] < 1 and F(1, 2) < y[1] < 1


def test_separation_is_a_certified_pass_with_a_gap():
    out, d = decide_boxes(square(0, 0), square(2, 0), True)
    assert out == "pass" and d["method"] == "separating_axis" and d["euclidean_gap_lower_bound"] > F(99, 100)


def test_exact_touching_is_a_pass_boundary_contact_allowed():
    out, d = decide_boxes(square(0, 0), square(1, 0), True)
    assert out == "pass" and d["axis_gap"] == 0


def test_touching_with_enclosure_width_is_unknown_not_a_verdict():
    out, d = decide_boxes(widen(square(0, 0), F(1, 2**40)), widen(square(1, 0), F(1, 2**40)), True)
    assert out == "unknown"


@pytest.mark.parametrize("eps_bits, expected", [(16, "unknown"), (100, "fail")])
def test_near_touch_overlap_resolves_only_with_precision(eps_bits, expected):
    shift = 1 - F(1, 2**60)   # overlap strip of width 2^-60
    P = widen(square(0, 0), F(1, 2**eps_bits))
    Q = widen(square(shift, 0), F(1, 2**eps_bits))
    assert decide_boxes(P, Q, True)[0] == expected


@pytest.mark.parametrize("eps_bits, expected", [(16, "unknown"), (100, "pass")])
def test_near_touch_gap_resolves_only_with_precision(eps_bits, expected):
    shift = 1 + F(1, 2**60)   # gap of 2^-60
    P = widen(square(0, 0), F(1, 2**eps_bits))
    Q = widen(square(shift, 0), F(1, 2**eps_bits))
    assert decide_boxes(P, Q, True)[0] == expected


def test_overlap_without_certified_orientation_is_never_a_fail():
    out, d = decide_boxes(square(0, 0), square(F(1, 2), F(1, 2)), False)
    assert out == "unknown" and "not certified" in d["reason"]


def test_wide_boxes_never_produce_a_verdict():
    P, Q = widen(square(0, 0), F(3)), widen(square(F(1, 2), 0), F(3))
    assert decide_boxes(P, Q, True)[0] == "unknown"
