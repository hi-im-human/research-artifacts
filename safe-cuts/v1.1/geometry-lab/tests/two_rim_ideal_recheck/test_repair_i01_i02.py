"""Stage 4B repair I01/I02 (System review stage4b-commit-79): the portable re-checker, one fault at a time.

I01: a truthful record in which no interval row is decided asserts no enclosure, so it is checkable without precision
levels; a decided row still needs its level. I02: every supplied side record and the Theorem S partition are validated
before any dictionary or set could hide a row. Needs mpmath (review environment); skipped elsewhere.
"""
import copy
import json

import pytest

pytest.importorskip("mpmath")

from glab.ideal_check.checker import IDEAL_POLICY                              # noqa: E402
from glab.two_rim.ideal_search import ideal_candidate_search                   # noqa: E402
from tests.two_rim_ideal.helpers import E11, E11_DELTA, SQUARE, material, new_run   # noqa: E402

from . import recheck_ideal_mpmath as rc                                       # noqa: E402
from .bundle import ideal_bundle                                               # noqa: E402

SIDES = "two_rim.ideal.retained_hinge_sides_opposite"
THEOREM_S = "two_rim.ideal.retained_neighbours_interiors_disjoint"
REMAINING = "two_rim.ideal.remaining_pairs_interiors_disjoint"
FLAT = dict(E11, height="1/1" + "0" * 200)      # System's I01 input: valid, but too flat for the default budget


def _bundle(params, delta, seam):
    run = new_run()
    _, m = material(run, params)
    row = ideal_candidate_search(run, m, delta, expected_policy=IDEAL_POLICY, seams=[seam])["results"][0]
    return row, ideal_bundle(run, {seam: row["ideal"]})


@pytest.fixture(scope="module")
def square():
    return _bundle(SQUARE, "1/4", "E0")[1]


@pytest.fixture(scope="module")
def flat():
    return _bundle(FLAT, E11_DELTA, "E4")


def run_rc(bundle, tmp_path):
    inp, out = tmp_path / "in.json", tmp_path / "out.json"
    inp.write_text(json.dumps(bundle), encoding="ascii")
    totals = rc.main(str(inp), str(out))
    return totals, json.loads(out.read_text(encoding="ascii"))


def reasons(report):
    return {f["code"] for s in report["seams"].values() for f in s["failures"]} | \
        {f["code"] for f in report.get("bundle_failures", [])}


def _claim(b, seam, name):
    return next(e for e in b["seams"][seam]["evidence"] if e["claim"] == name)


# ---------------------------------------------------------------- I01

def test_all_unknown_record_is_verified_with_no_enclosure_claimed(flat, tmp_path):
    row, b = flat
    assert row["ideal_geometric_verdict"]["verdict"] == "unknown"
    rem = _claim(b, "E4", REMAINING)
    assert rem["receipt"]["enclosures"] == {} and rem["tolerances"] == IDEAL_POLICY
    totals, report = run_rc(b, tmp_path)
    assert totals["verified"] is True and totals["failures"] == 0
    assert totals["unknown_rows"] == 45 and totals["theorem_s_confirmed"] == 10
    assert totals["coordinates_checked"] == 0 and totals["axis_rows"] == totals["witness_rows"] == 0
    assert report["seams"]["E4"]["recomputed_verdict"] == "unknown"      # verified report, never a safety pass


def test_a_decided_row_without_its_level_is_still_rejected(flat, tmp_path):
    b = copy.deepcopy(flat[1])
    r = _claim(b, "E4", REMAINING)["receipt"]["rows"][0]
    r.pop("reason", None)
    r.update(method="separating_axis", outcome="pass", bits=16,
             certificate={"method": "separating_axis", "axis": ["1", "0"], "order": "P_below_Q", "axis_gap": "0",
                          "euclidean_gap_lower_bound": "0"})
    totals, report = run_rc(b, tmp_path)
    assert totals["verified"] is False and "bits_level" in reasons(report)
    assert totals["coordinates_checked"] == 0


def test_a_genuine_overlap_stays_a_verified_fail_not_an_unknown(tmp_path):
    _, b = _bundle(E11, E11_DELTA, "E9")
    totals, report = run_rc(b, tmp_path)
    assert totals["verified"] is True and report["seams"]["E9"]["recomputed_verdict"] == "fail"
    assert totals["coordinates_checked"] > 0 and totals["witness_bounds_confirmed"] >= 1


# ---------------------------------------------------------------- I02

def _sides(b):
    return _claim(b, "E0", SIDES)["receipt"]["rows"]


def _ts(b):
    return _claim(b, "E0", THEOREM_S)["receipt"]


def _dup_valid(b):
    _sides(b).insert(0, copy.deepcopy(_sides(b)[0]))


def _dup_corrupt(b):
    extra = copy.deepcopy(_sides(b)[0])
    face = extra["pair"][0]
    extra["sigma"][face][next(iter(extra["sigma"][face]))] = "999999"
    _sides(b).insert(0, extra)


def _reversed(b):
    _sides(b)[0]["pair"].reverse()


def _nonconsecutive(b):
    first, second = _sides(b)[0]["pair"][0], _sides(b)[1]["pair"][1]
    _sides(b)[0]["pair"] = [first, second]


def _corrupt_sigma(b):
    face = _sides(b)[0]["pair"][0]
    _sides(b)[0]["sigma"][face][next(iter(_sides(b)[0]["sigma"][face]))] = "999999"


def _disagree(b):
    _ts(b)["undecided_pairs"] = [_ts(b)["decided_pairs"].pop(0)]


FAULTS = {
    "side_duplicate": _dup_valid,
    "side_duplicate_corrupt": _dup_corrupt,
    "side_pair_ids": lambda b: _sides(b).append({"pair": ["F0", "F99"], "outcome": "pass", "sigma": {}}),
    "side_pair_order": _reversed,
    "side_pair_order_nonconsecutive": _nonconsecutive,
    "side_coverage": lambda b: _sides(b).pop(1),
    "unrecognized_field": lambda b: _sides(b)[0].update(note="extra"),
    "side_outcome": lambda b: _sides(b)[0].update(outcome="unknown"),
    "theorem_s": _corrupt_sigma,
    "partition_duplicate": lambda b: _ts(b)["decided_pairs"].append(copy.deepcopy(_ts(b)["decided_pairs"][0])),
    "partition_overlap": lambda b: _ts(b).update(undecided_pairs=[copy.deepcopy(_ts(b)["decided_pairs"][0])]),
    "partition_coverage": lambda b: _ts(b)["decided_pairs"].pop(0),
    "partition_disagrees": _disagree,
}
EXPECTED = {"side_duplicate_corrupt": "side_duplicate", "side_pair_order_nonconsecutive": "side_pair_order"}


@pytest.mark.parametrize("name", sorted(FAULTS))
def test_each_side_record_and_partition_fault_has_its_reason(square, tmp_path, name):
    b = copy.deepcopy(square)
    FAULTS[name](b)
    totals, report = run_rc(b, tmp_path)
    assert totals["verified"] is False and totals["failures"] > 0, name
    assert EXPECTED.get(name, name) in reasons(report), (name, sorted(reasons(report)))


def test_the_genuine_square_bundle_still_verifies(square, tmp_path):
    totals, report = run_rc(square, tmp_path)
    assert totals["verified"] is True and totals["theorem_s_confirmed"] == 3
    assert report["seams"]["E0"]["recomputed_verdict"] == "pass"
