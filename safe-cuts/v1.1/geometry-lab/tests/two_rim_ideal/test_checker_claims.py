"""Stage 4B: claim receipts, reported bounds, the checker's self-check, pair coverage and invalid local premises."""
from fractions import Fraction as F

import pytest

from glab.ideal_check import geometry as ideal_geometry
from glab.ideal_check.checker import CHECKED_FIELDS, DIAGNOSTIC_FIELDS, IDEAL_CLAIMS

from .helpers import (E11, E11_DELTA, MATERIAL_MUTATIONS, by_claim, check_ideal, ideal_lane, material, new_run,
                      outcomes, succeeded)

SIDES = "two_rim.ideal.retained_hinge_sides_opposite"
THEOREM_S = "two_rim.ideal.retained_neighbours_interiors_disjoint"
REMAINING = "two_rim.ideal.remaining_pairs_interiors_disjoint"
PREMISES = "two_rim.ideal.local_premises"


@pytest.fixture(scope="module")
def e11_lanes():
    run = new_run()
    sm = material(run, E11)
    lanes = {s: ideal_lane(run, E11, s, E11_DELTA, source_material=sm) for s in ("E4", "E9")}
    return run, {s: dict(lane, claims=by_claim(check_ideal(run, lane["ideal"]))) for s, lane in lanes.items()}


def _box(receipt, bits, face):
    return [((F(x[0]), F(x[1])), (F(y[0]), F(y[1]))) for x, y in receipt["enclosures"][str(bits)]["boxes"][face]]


def _sup(d, poly):
    return max(max(d[0] * x[0], d[0] * x[1]) + max(d[1] * y[0], d[1] * y[1]) for x, y in poly)


def _inf(d, poly):
    return min(min(d[0] * x[0], d[0] * x[1]) + min(d[1] * y[0], d[1] * y[1]) for x, y in poly)


def _margin(P, Q, y):
    lows = []
    for poly in (P, Q):
        for i in range(len(poly)):
            (x0, y0), (x1, y1) = poly[i], poly[(i + 1) % len(poly)]
            ex, ey = (x1[0] - x0[1], x1[1] - x0[0]), (y1[0] - y0[1], y1[1] - y0[0])
            wx, wy = (y[0] - x0[1], y[0] - x0[0]), (y[1] - y0[1], y[1] - y0[0])
            a = [p * q for p in ex for q in wy]
            b = [p * q for p in ey for q in wx]
            lows.append(min(a) - max(b))
    return min(lows)


def test_receipts_separate_checked_fields_from_diagnostics(e11_lanes):
    _, lanes = e11_lanes
    receipt = lanes["E9"]["claims"][REMAINING]["receipt"]
    assert receipt["checked_fields"] == CHECKED_FIELDS and receipt["diagnostic_fields"] == DIAGNOSTIC_FIELDS
    assert set(CHECKED_FIELDS) >= {"pair", "positions", "method", "outcome", "certificate.axis", "certificate.order",
                                   "certificate.axis_gap", "certificate.euclidean_gap_lower_bound",
                                   "certificate.witness", "certificate.cross_lower_bound"}
    assert set(DIAGNOSTIC_FIELDS) >= {"attempts", "reason"} and not set(CHECKED_FIELDS) & set(DIAGNOSTIC_FIELDS)
    used = {r["bits"] for r in receipt["rows"] if "bits" in r}
    assert used and {str(b) for b in used} <= set(receipt["enclosures"])
    chain = lanes["E9"]["claims"][PREMISES]["receipt"]["chain"]
    assert chain[0] == "F9" and len(chain) == 11
    for level in receipt["enclosures"].values():
        assert sorted(level["boxes"]) == sorted(chain)
        assert all(rec["checked"] is True for rec in level["sqrt_records"])


def test_every_recorded_certificate_and_bound_checks_exactly_on_its_recorded_boxes(e11_lanes):
    run, lanes = e11_lanes
    for seam, lane in lanes.items():
        receipt = lane["claims"][REMAINING]["receipt"]
        for r in receipt["rows"]:
            a, b = r["pair"]
            P, Q = _box(receipt, r["bits"], a), _box(receipt, r["bits"], b)
            c = r["certificate"]
            if r["method"] == "separating_axis":
                d = (F(c["axis"][0]), F(c["axis"][1]))
                assert d != (0, 0)
                g = _inf(d, Q) - _sup(d, P) if c["order"] == "P_below_Q" else _inf(d, P) - _sup(d, Q)
                eb = F(c["euclidean_gap_lower_bound"])
                assert g >= 0 and g == F(c["axis_gap"]) and 0 <= eb and eb * eb * (d[0] ** 2 + d[1] ** 2) <= g * g
            else:
                y = (F(c["witness"][0]), F(c["witness"][1]))
                m = _margin(P, Q, y)
                assert r["method"] == "interior_witness" and 0 < F(c["cross_lower_bound"]) <= m, (seam, a, b)


def test_theorem_s_claim_names_its_pinned_dependency_and_premises(e11_lanes):
    _, lanes = e11_lanes
    rec = lanes["E4"]["claims"][THEOREM_S]["receipt"]
    assert rec["premise_claims"] == [PREMISES, SIDES]
    dep = rec["analytic_dependency"]
    assert dep["contract"] == "engine/IDEAL-DEVELOPMENT-CONTRACT.md" and len(dep["contract_sha256_lf"]) == 64
    assert "not machine-checked" in dep["status"] and "not Lean" in dep["status"]
    assert len(rec["decided_pairs"]) == 10 and rec["undecided_pairs"] == []
    sides = lanes["E4"]["claims"][SIDES]["receipt"]["rows"]
    assert all(r["outcome"] == "pass" and set(r["sides"].values()) == {-1, 1} for r in sides)


def test_pair_coverage_partitions_the_chain_pairs(e11_lanes):
    _, lanes = e11_lanes
    for lane in lanes.values():
        cov = lane["claims"]["two_rim.ideal.pair_coverage_complete"]
        assert cov["outcome"] == "pass"
        assert cov["receipt"]["missing"] == [] and cov["receipt"]["duplicated"] == []


def test_an_inflated_euclidean_bound_fails_the_self_check_and_never_passes(monkeypatch):
    original = ideal_geometry.certify_separation

    def inflated(P, Q):
        best = original(P, Q)
        if best is not None:
            best = dict(best, euclidean_gap_lower_bound=best["euclidean_gap_lower_bound"] + 1)
        return best
    monkeypatch.setattr(ideal_geometry, "certify_separation", inflated)
    run = new_run()
    evs = by_claim(check_ideal(run, ideal_lane(run, E11, "E4", E11_DELTA)["ideal"]))
    rec = evs[REMAINING]["receipt"]
    assert evs[REMAINING]["outcome"] == "unknown"
    assert rec["self_check"]["failed"] and all(r["outcome"] == "unknown" for r in rec["rows"]
                                                if r.get("reason", "").startswith("certificate_self_check_failed"))
    assert not any(r.get("method") == "separating_axis" for r in rec["rows"])


def test_an_inflated_witness_bound_fails_the_self_check_and_never_fails_the_pair(monkeypatch):
    original = ideal_geometry.certify_witness

    def inflated(P, Q):
        w = original(P, Q)
        return None if w is None else dict(w, cross_lower_bound=w["cross_lower_bound"] * 2 + 1)
    monkeypatch.setattr(ideal_geometry, "certify_witness", inflated)
    run = new_run()
    evs = by_claim(check_ideal(run, ideal_lane(run, E11, "E9", E11_DELTA)["ideal"]))
    rows = evs[REMAINING]["receipt"]["rows"]
    assert evs[REMAINING]["outcome"] == "unknown"
    assert not any(r.get("method") == "interior_witness" for r in rows)
    assert any(r.get("reason", "").startswith("certificate_self_check_failed") for r in rows)


@pytest.mark.parametrize("mutation", sorted(MATERIAL_MUTATIONS))
def test_invalid_local_geometry_is_unsupported_input_with_its_code(mutation):
    run = new_run(test_actions=True)
    _, m = material(run, E11)
    bad = succeeded(run.apply("test.material.mutated", 1, {"mutation": mutation}, m))
    c = succeeded(run.apply("two_rim.cut.open", 1, {"seam": "E9"}, bad))
    i = succeeded(run.apply("two_rim.ideal.define", 1, {"delta": E11_DELTA}, c))
    evs = by_claim(check_ideal(run, i))
    out = {k: e["outcome"] for k, e in evs.items()}
    assert out[PREMISES] == "fail", out
    codes = {p["code"] for p in evs[PREMISES]["receipt"]["problems"]}
    assert MATERIAL_MUTATIONS[mutation][1] in codes, (mutation, codes)
    assert all(out[k] == "unknown" for k in IDEAL_CLAIMS[4:]), out
    assert all("unsupported input" in evs[k]["receipt"]["not_interpreted"] for k in IDEAL_CLAIMS[4:])


def test_a_cut_whose_face_order_is_not_the_chain_is_refused():
    run = new_run(test_actions=True)
    _, m = material(run, E11)
    c = succeeded(run.apply("test.cut.permuted", 1, {"seam": "E9"}, m))
    evs = by_claim(check_ideal(run, succeeded(run.apply("two_rim.ideal.define", 1, {"delta": E11_DELTA}, c))))
    assert evs[PREMISES]["outcome"] == "fail"
    assert "chain" in {p["code"] for p in evs[PREMISES]["receipt"]["problems"]}
    assert all(evs[k]["outcome"] == "unknown" for k in IDEAL_CLAIMS[4:])


def test_repeated_checks_give_identical_evidence(e11_lanes):
    run, lanes = e11_lanes
    again = check_ideal(run, lanes["E9"]["ideal"])
    assert {e["claim"]: e["receipt"] for e in again} == {c: e["receipt"] for c, e in lanes["E9"]["claims"].items()}
    assert outcomes(again) == {c: e["outcome"] for c, e in lanes["E9"]["claims"].items()}
