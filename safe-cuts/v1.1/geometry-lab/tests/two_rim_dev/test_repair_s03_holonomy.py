"""Stage 3 repair S03: principal rotation and lifted total turn are reported separately."""
import math

import pytest

from glab.check.two_rim_development import DIAGNOSTICS, lifted_turn_summary
from tests.two_rim.golden_support import random_cases
from tests.two_rim_dev.helpers import E11, developed, fixture, new_run

HOL = DIAGNOSTICS[2]


def wrap(a):
    return math.atan2(math.sin(a), math.cos(a))


@pytest.mark.parametrize("incs, lifted_sign, principal_sign", [
    ([2.0, 2.0, 2.0], "positive", "negative"),     # lift 6.0 crosses +pi; principal about -0.283
    ([-2.5, -2.5], "negative", "positive"),        # lift -5.0 crosses -pi; principal about +1.283
    ([0.7, -0.2], "positive", "positive"),         # no crossing
])
def test_lift_crossing_the_principal_branch_keeps_its_own_sign(incs, lifted_sign, principal_sign):
    total = math.fsum(incs)
    outcome, r = lifted_turn_summary(incs, wrap(total), total)
    assert outcome == "pass"
    assert r["lift_decided"] is True and r["rotations_agree_mod_2pi"] is True
    assert r["lifted_total_turn"] == pytest.approx(total)
    assert r["lifted_total_turn_sign"] == lifted_sign and r["principal_rotation_sign"] == principal_sign
    assert r["generator_sum_q"]["attributed_to"] == "generator" and r["generator_agrees_with_checker_lift"] is True
    assert "defect_sign" not in r and "abs_values_agree" not in r


def test_near_identity_has_no_epsilon_sign_choice():
    outcome, r = lifted_turn_summary([1e-12, -2e-12], -1e-12, -1e-12)
    assert outcome == "pass"
    assert r["lifted_total_turn_sign"] == "unknown" and r["principal_rotation_sign"] == "unknown"


def test_increment_at_the_branch_leaves_the_lift_undecided():
    incs = [math.pi - 1e-12, 0.1]
    outcome, r = lifted_turn_summary(incs, wrap(math.fsum(incs)), math.fsum(incs))
    assert outcome == "unknown"
    assert r["lift_decided"] is False and r["lifted_total_turn_sign"] == "unknown"


def test_generator_sum_that_differs_by_a_full_turn_is_flagged():
    incs = [2.0, 2.0, 2.0]
    outcome, r = lifted_turn_summary(incs, wrap(6.0), 6.0 - 2 * math.pi)
    assert outcome == "fail" and r["generator_agrees_with_checker_lift"] is False
    assert r["lifted_total_turn_sign"] == "positive"  # the checker's own lift, not the generator's value


def test_principal_rotation_inconsistent_with_the_lift_is_flagged():
    outcome, r = lifted_turn_summary([1.0], 0.5, 1.0)
    assert outcome == "fail" and r["rotations_agree_mod_2pi"] is False


def _hol(run, h, checker):
    return next(e for e in run.check(checker, 2, h, {}) if e["claim"] == HOL)


def test_eleven_panel_e9_negative_lift_positive_principal_rotation():
    run = new_run()
    d = developed(run, E11, seam="E9", delta="1/10000")
    q = run.get(d["development"])["payload"]["generator"]["sum_q"]
    for h, checker in ((d["development"], "two_rim.check.development"),
                       (d["trimmed"], "two_rim.check.trimmed_development")):
        ev = _hol(run, h, checker)
        r = ev["receipt"]
        assert ev["outcome"] == "pass"
        assert r["lifted_total_turn"] == pytest.approx(-6.207602934472599, abs=1e-9)
        assert r["lifted_total_turn"] == pytest.approx(q, abs=1e-9)
        assert r["lifted_total_turn_sign"] == "negative"
        assert r["principal_rotation"] == pytest.approx(0.07558237270698709, abs=1e-9)
        assert r["principal_rotation_sign"] == "positive"
        assert "defect_sign" not in r


def test_positive_lift_beyond_pi_end_to_end():
    run = new_run()
    d = developed(run, random_cases()[0][32], seam="E0")
    r = _hol(run, d["development"], "two_rim.check.development")["receipt"]
    assert r["lifted_total_turn"] > math.pi and r["lifted_total_turn_sign"] == "positive"
    assert r["principal_rotation_sign"] == "negative"


def test_translated_prism_is_near_identity_and_unsigned():
    run = new_run()
    d = developed(run, fixture("F1_translated_square_prism"), seam="E0")
    ev = _hol(run, d["development"], "two_rim.check.development")
    assert ev["outcome"] == "pass" and ev["receipt"]["lifted_total_turn_sign"] == "unknown"
