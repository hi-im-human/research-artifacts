"""Stage 4B: exact prisms, non-dyadic values and positive near-boundary trims (the exact zero-width path)."""
from fractions import Fraction as F

import pytest

from glab.ideal_check.checker import IDEAL_CLAIMS

from .helpers import NEAR_HALF, NEAR_ZERO, NONDYADIC, SQUARE, by_claim, check_ideal, ideal_lane, material, new_run, \
    outcomes

REMAINING = "two_rim.ideal.remaining_pairs_interiors_disjoint"


def _lane_claims(params, delta):
    run = new_run()
    sm = material(run, params)
    seams = [e["id"] for e in run.get(sm[1])["payload"]["hinges"]]
    return {seam: check_ideal(run, ideal_lane(run, params, seam, delta, source_material=sm)["ideal"])
            for seam in seams}


def _endpoints(receipt):
    for level in receipt["enclosures"].values():
        for boxes in level["boxes"].values():
            for vertex in boxes:
                for lo, hi in vertex:
                    yield F(lo), F(hi)


@pytest.mark.parametrize("delta", ["1/4", "1/3", "1/7", "1/10000", NEAR_ZERO, NEAR_HALF])
def test_square_prism_every_claim_passes_with_zero_width_boxes(delta):
    claims = _lane_claims(SQUARE, delta)
    assert sorted(claims) == ["E0", "E1", "E2", "E3"]
    for seam, evs in claims.items():
        assert set(outcomes(evs).values()) == {"pass"}, (seam, outcomes(evs))
        receipt = by_claim(evs)[REMAINING]["receipt"]
        assert all(lo == hi for lo, hi in _endpoints(receipt)), "the exact path must keep every box zero-width"
        assert {r["method"] for r in receipt["rows"]} == {"separating_axis"}


@pytest.mark.parametrize("delta", ["1/3", "1/7", NEAR_ZERO])
def test_non_dyadic_prism_is_decided_exactly(delta):
    claims = _lane_claims(NONDYADIC, delta)
    for seam, evs in claims.items():
        assert set(outcomes(evs).values()) == {"pass"}, (seam, outcomes(evs))
        receipt = by_claim(evs)[REMAINING]["receipt"]
        ends = list(_endpoints(receipt))
        assert all(lo == hi for lo, hi in ends)
        # exactness is not an artefact of dyadic inputs: some endpoints have odd denominators
        assert any(lo.denominator % 2 == 1 and lo.denominator > 1 for lo, _ in ends)


def test_near_boundary_trims_are_distinct_subjects():
    run = new_run()
    sm = material(run, SQUARE)
    ids = {d: ideal_lane(run, SQUARE, "E0", d, source_material=sm)["ideal"] for d in (NEAR_ZERO, NEAR_HALF, "1/4")}
    assert len(set(ids.values())) == 3
    for h in ids.values():
        assert outcomes(check_ideal(run, h)) == {c: "pass" for c in IDEAL_CLAIMS}
