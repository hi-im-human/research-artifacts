"""Stage 3 pair policy controls: glued proximity never upgrades an unresolved pair."""
import numpy as np

from glab.check.two_rim_development import classify_pair

SQ = [(0.0, 0.0), (1.0, 0.0), (1.0, 1.0), (0.0, 1.0)]
TAU = 1e-9
EPS = 2.0 ** -40  # exactly representable, far below the tolerance


def run(P, Q, shared=None):
    return classify_pair(np.array(P), np.array(Q), TAU, shared=shared)


def shifted(dx, dy=0.0):
    return [(x + dx, y + dy) for x, y in SQ]


def test_separated_is_a_numerical_pass():
    assert run(SQ, shifted(2.0))[:2] == ("pass", "separated")


def test_overlap_beyond_tolerance_fails():
    res, why, info = run(SQ, shifted(0.5, 0.5))
    assert (res, why) == ("fail", "interior_overlap") and abs(info["overlap_area"] - 0.25) < 1e-12


def test_exact_boundary_contact_on_represented_coordinates():
    res, why, info = run(SQ, shifted(1.0))
    assert res == "pass" and why == "boundary_contact_or_gap_exact_on_represented_coordinates"
    assert "represented" in info["exactness_scope"]


def test_tiny_nonglued_overlap_is_unknown():
    assert run(SQ, shifted(1.0 - EPS))[:2] == ("unknown", "near_contact_unresolved")


def test_tiny_overlap_along_a_glued_hinge_is_unknown_not_pass():
    hinge = {"kind": "retained_hinge", "P": (1, 2), "Q": (0, 3)}  # P edge 1-2 is x=1; Q edge 3-0 is x=1-eps
    res, why, info = run(SQ, shifted(1.0 - EPS), shared=hinge)
    assert (res, why) == ("unknown", "near_contact_unresolved")
    assert info["opposite_sides_margin"] > 0.5  # recorded as information only; it does not decide the pair


def test_tiny_overlap_at_a_glued_vertex_is_unknown_not_pass():
    corner = {"kind": "glued_vertex", "P": [2], "Q": [0]}
    res, why, info = run(SQ, shifted(1.0 - EPS, 1.0 - EPS), shared=corner)
    assert (res, why) == ("unknown", "near_contact_unresolved") and "tangent_cone_gap" in info
