"""Stage 4B: separate re-check of fresh maintained bundles, and the existing adversarial cases in the new format.

The re-checker (recheck_ideal_mpmath.py) is the accepted Stage 4A re-checker (blob cb483479: A03, R01, R02) with its
binding layer adapted to maintained records. The adversarial cases are ported from the accepted A03 and R01/R02 tests
(blobs b5cbb7cb and af11a53e) and from System's acceptance cases on main (reviews/stage4a-repair-commit-62). Needs
mpmath, so it runs in the throwaway review environment and is skipped elsewhere.
"""
import copy
import json
import subprocess
import sys
from fractions import Fraction as F
from pathlib import Path

import pytest

pytest.importorskip("mpmath")

from glab.core.records import content_hash                                     # noqa: E402
from glab.ideal_check.checker import IDEAL_POLICY                              # noqa: E402
from glab.two_rim.ideal_search import ideal_candidate_search                   # noqa: E402
from tests.two_rim_ideal.helpers import E11, E11_DELTA, SQUARE, material, new_run   # noqa: E402

from . import recheck_ideal_mpmath as rc                                       # noqa: E402
from .bundle import ideal_bundle                                               # noqa: E402

HERE = Path(__file__).resolve().parent
PREMISES = "two_rim.ideal.local_premises"
SIDES = "two_rim.ideal.retained_hinge_sides_opposite"
REMAINING = "two_rim.ideal.remaining_pairs_interiors_disjoint"
COVERAGE = "two_rim.ideal.pair_coverage_complete"
PASSING = ["E0", "E1", "E2", "E4", "E5", "E6", "E7"]


def _search(params, delta):
    run = new_run()
    _, m = material(run, params)
    res = ideal_candidate_search(run, m, delta, expected_policy=IDEAL_POLICY)
    return ideal_bundle(run, {r["seam"]: r["ideal"] for r in res["results"]})


@pytest.fixture(scope="module")
def e11():
    return _search(E11, E11_DELTA)


@pytest.fixture(scope="module")
def pair(e11):
    return dict(e11, seams={s: e11["seams"][s] for s in ("E4", "E9")})


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


def _rows(b, seam):
    return _claim(b, seam, REMAINING)["receipt"]["rows"]


def _first(b, seam, method):
    return next(r for r in _rows(b, seam) if r.get("method") == method)


def _level(b, seam):
    enc = _claim(b, seam, REMAINING)["receipt"]["enclosures"]
    return enc[sorted(enc, key=int)[0]]


# ---------------------------------------------------------------- fresh bundles

def test_fresh_e11_bundle_verifies_every_seam_and_bound(e11, tmp_path):
    totals, report = run_rc(e11, tmp_path)
    assert totals["verified"] is True and totals["failures"] == 0 and totals["verified_seams"] == 11
    assert totals["rows_checked"] == totals["expected_pairs"] == 605 and totals["unknown_rows"] == 0
    assert totals["theorem_s_rows"] == totals["theorem_s_confirmed"] == 110
    assert totals["axis_rows"] == totals["axis_confirmed"] == totals["euclidean_bounds_confirmed"] == 484
    assert totals["witness_rows"] == totals["witness_confirmed"] == totals["witness_bounds_confirmed"] == 11
    assert totals["coordinates_checked"] == totals["coordinates_contained"] > 0
    verdicts = {s: r["recomputed_verdict"] for s, r in report["seams"].items()}
    assert verdicts == {s: ("pass" if s in PASSING else "fail") for s in verdicts}
    assert {r["local_preconditions"] for r in report["seams"].values()} == {"checked"}


def test_the_report_states_its_scope(e11, tmp_path):
    _, report = run_rc(dict(e11, seams={"E4": e11["seams"]["E4"]}), tmp_path)
    scope = report["scope"]
    assert "not re-proved" in scope["stage2_source_correspondence_and_run_evidence"]
    assert "not a safety statement" in scope["meaning_of_verified"]
    assert "not confirmed" in scope["meaning_of_containment_failure"]
    assert "not by itself proof" in scope["meaning_of_containment_failure"]
    assert "structural binding" in scope["evidence_records"]
    assert report["contract"] == "two_rim.ideal.recheck_bundle/1"
    assert set(report["diagnostic_fields_not_verified"]) >= {"attempts", "reason"}


def test_fresh_square_bundles_verify_on_the_exact_path(tmp_path):
    for delta in ("1/4", "1/3"):
        totals, report = run_rc(_search(SQUARE, delta), tmp_path)
        assert totals["verified"] is True and totals["verified_seams"] == 4
        assert {r["recomputed_verdict"] for r in report["seams"].values()} == {"pass"}


def test_exact_non_dyadic_boxes_are_not_confirmed_by_binary_intervals(tmp_path):
    """Documented limitation (added after the adaptation): a zero-width recorded box at a non-dyadic rational point
    cannot contain mpmath's binary interval around that point, so containment is NOT CONFIRMED although every
    certificate re-verifies on the recorded boxes. Failure to confirm is not proof that the first enclosure is wrong."""
    from tests.two_rim_ideal.helpers import NONDYADIC
    totals, report = run_rc(_search(NONDYADIC, "1/3"), tmp_path)
    assert totals["verified"] is False and reasons(report) == {"containment"}
    assert totals["coordinates_contained"] < totals["coordinates_checked"]
    assert {r["status"] for r in report["seams"].values()} == {"failed"}
    assert {r["recomputed_verdict"] for r in report["seams"].values()} == {"pass"}
    assert all("not confirmed" in f["detail"] for r in report["seams"].values() for f in r["failures"])


# ---------------------------------------------------------------- single faults, each with its reason code

def _swap_bounds(b):
    box = _level(b, "E4")["boxes"]["F5"][0][0]
    box[0], box[1] = box[1], box[0]


def _noncanonical(b):
    c = _first(b, "E4", "separating_axis")["certificate"]
    x = F(c["axis"][0])
    c["axis"][0] = f"{2 * x.numerator}/{2 * x.denominator}"


def _flip_sides(b):
    sh = _claim(b, "E4", SIDES)["receipt"]["rows"][0]
    sh["sides"] = {k: -v for k, v in sh["sides"].items()}


def _cut_state(b):
    return b["states"][b["states"][b["seams"]["E4"]["ideal_state"]]["parent"]]


def _drop_claim(b):
    b["seams"]["E4"]["evidence"] = [e for e in b["seams"]["E4"]["evidence"] if e["claim"] != COVERAGE]


FAULTS = {
    "axis_zero": lambda b: _first(b, "E4", "separating_axis")["certificate"].update(axis=["0", "0"]),
    "axis_order": lambda b: _first(b, "E4", "separating_axis")["certificate"].update(order="sideways"),
    "noncanonical_number": _noncanonical,
    "interval_bounds": _swap_bounds,
    "box_shape": lambda b: _level(b, "E4")["boxes"].update(F5=_level(b, "E4")["boxes"]["F5"][:3]),
    "box_coverage": lambda b: _level(b, "E4")["boxes"].pop("F5"),
    "pair_coverage": lambda b: _rows(b, "E4").pop(7),
    "pair_duplicate": lambda b: _rows(b, "E4").append(copy.deepcopy(_rows(b, "E4")[7])),
    "pair_ids": lambda b: _rows(b, "E4")[7]["pair"].__setitem__(1, "F99"),
    "pair_order": lambda b: _rows(b, "E4")[7]["pair"].reverse(),
    "method_outcome": lambda b: _first(b, "E9", "interior_witness").update(outcome="pass"),
    "verdict": lambda b: _claim(b, "E9", REMAINING).update(outcome="pass"),
    "witness_bound": lambda b: _first(b, "E9", "interior_witness")["certificate"].update(
        cross_lower_bound="1" + "0" * 30),
    "euclidean_gap_bound": lambda b: _first(b, "E4", "separating_axis")["certificate"].update(
        euclidean_gap_lower_bound="1" + "0" * 30),
    "euclidean_gap_bound_shape": lambda b: _first(b, "E4", "separating_axis")["certificate"].update(
        euclidean_gap_lower_bound="-1"),
    "unrecognized_field": lambda b: _first(b, "E4", "separating_axis")["certificate"].update(certified_area="5"),
    "positions": lambda b: _first(b, "E4", "separating_axis").update(positions=[0, 1]),
    "bits_level": lambda b: _first(b, "E4", "separating_axis").update(bits=999),
    "shared_hinge_record": _flip_sides,
    "state_hash": lambda b: _cut_state(b)["payload"].update(seam="E5"),
    "evidence_subject": lambda b: _claim(b, "E4", SIDES).update(subject="sha256:" + "0" * 64),
    "evidence_checker": lambda b: _claim(b, "E4", SIDES).update(checker="two_rim.check.other"),
    "evidence_claims": _drop_claim,
    "declared_claims": lambda b: _claim(b, "E4", PREMISES).update(outcome="fail"),
    "bundle_schema": lambda b: b.pop("schema"),
}


@pytest.mark.parametrize("code", sorted(FAULTS))
def test_single_fault_is_rejected_with_its_reason(pair, tmp_path, code):
    b = copy.deepcopy(pair)
    FAULTS[code](b)
    totals, report = run_rc(b, tmp_path)
    assert totals["verified"] is False and totals["failures"] > 0, code
    assert code in reasons(report), (code, sorted(reasons(report)))


def test_the_prototype_bundle_format_is_refused(tmp_path):
    totals, report = run_rc({"schema": "stage4a.recheck_bundle/2", "states": {}, "seams": {"E4": {}}}, tmp_path)
    assert totals["verified"] is False and reasons(report) == {"bundle_schema"}


# ---------------------------------------------------------------- self-consistently rehashed faults

def _chain(states, h):
    out = []
    while h is not None:
        out.append(h)
        h = states[h]["parent"]
    return out


def rebind(bundle, seam, *, material=None, ideal=None, ideal_parent_is_material=False):
    """Mutate, then rehash material, cut and ideal and re-point the evidence, so only the named fault remains."""
    b = copy.deepcopy(bundle)
    S = b["seams"][seam]
    idl = copy.deepcopy(b["states"][S["ideal_state"]])
    cut = copy.deepcopy(b["states"][idl["parent"]])
    mat = copy.deepcopy(b["states"][cut["parent"]])
    if material is not None:
        material(mat["payload"])
        mat["payload"]["identity"] = rc.chash({k: v for k, v in mat["payload"].items() if k != "identity"})
        b["states"][content_hash(mat)] = mat
        cut["parent"] = content_hash(mat)
        cut["payload"]["material"] = copy.deepcopy(mat["payload"])
        b["states"][content_hash(cut)] = cut
        idl["parent"] = content_hash(cut)
        idl["payload"]["cut"] = copy.deepcopy(cut["payload"])
    if ideal is not None:
        ideal(idl["payload"])
    if ideal_parent_is_material:
        idl["parent"] = cut["parent"]
    h = content_hash(idl)
    b["states"][h] = idl
    for e in S["evidence"]:
        e["subject"], e["dependencies"] = h, _chain(b["states"], h)
    S["ideal_state"] = h
    b["seams"] = {seam: S}
    return b


def _set(key, value):
    return lambda p: p.update({key: value})


@pytest.mark.parametrize("code, kw", [
    ("subject_constants", {"ideal": _set("normalization", "N1: centroid at the origin")}),
    ("delta_domain", {"ideal": _set("delta", "3/4")}),
    ("cut_copy", {"ideal": lambda p: p["cut"].update(seam="E5")}),
    ("parent_link", {"ideal_parent_is_material": True}),
])
def test_rehashed_record_faults_are_rejected_at_binding(pair, tmp_path, code, kw):
    totals, report = run_rc(rebind(pair, "E4", **kw), tmp_path)
    assert totals["verified"] is False and code in reasons(report), (code, sorted(reasons(report)))
    assert totals["coordinates_checked"] == 0


def _face(p, fid):
    return next(f for f in p["faces"] if f["id"] == fid)


def _hinge(p, hid):
    return next(e for e in p["hinges"] if e["id"] == hid)


def _degenerate(p):
    h = _hinge(p, "E5")
    h["upper"] = h["lower"]


def _lacks_endpoint(p):
    f = _face(p, "F5")
    lo = _hinge(p, f["entry"])["lower"]
    f["boundary"] = [v for v in f["boundary"] if v != lo]


def _swap_ends(p):
    h = _hinge(p, "E5")
    h["lower"], h["upper"] = h["upper"], h["lower"]


R02 = {"ring_not_on_plane": lambda p: p["faces"][0]["plane"].__setitem__(3, p["faces"][0]["plane"][3] + 1),
       "orientation_not_outward": lambda p: p["faces"][0].update(plane=[-x for x in p["faces"][0]["plane"]]),
       "normal_zero": lambda p: p["faces"][0].update(plane=[0, 0, 0, 0]),
       "hinge_degenerate": _degenerate,
       "identity_ambiguous": lambda p: p["vertices"].append(copy.deepcopy(p["vertices"][0])),
       "reference_missing": lambda p: p["faces"][0].update(entry="E99"),
       "incidence": _lacks_endpoint,
       "trimmed_ring_not_convex_ccw": _swap_ends}


@pytest.mark.parametrize("code", sorted(R02))
def test_rehashed_bad_geometry_is_rejected_before_any_geometry(pair, tmp_path, code):
    totals, report = run_rc(rebind(pair, "E9", material=R02[code]), tmp_path)
    assert totals["verified"] is False and report["seams"]["E9"]["status"] == "rejected", code
    assert report["seams"]["E9"]["local_preconditions"] == "failed"
    assert code in reasons(report), (code, sorted(reasons(report)))
    assert totals["coordinates_checked"] == 0


def test_rehash_without_a_fault_still_verifies(pair, tmp_path):
    assert run_rc(rebind(pair, "E9", material=lambda p: None), tmp_path)[0]["verified"] is True


def test_a_consistent_but_different_trim_is_not_confirmed_rather_than_declared_invalid(pair, tmp_path):
    totals, report = run_rc(rebind(pair, "E4", ideal=_set("delta", "1/5000")), tmp_path)
    seam = report["seams"]["E4"]
    assert totals["verified"] is False and seam["status"] == "failed" and "containment" in reasons(report)
    assert all("not confirmed" in f["detail"] for f in seam["failures"] if f["code"] == "containment")


# ---------------------------------------------------------------- honest unknowns and the CLI

def _make_unknown(b):
    row = _first(b, "E4", "separating_axis")
    for k in ("method", "certificate", "bits"):
        row.pop(k, None)
    row.update(outcome="unknown", reason="review budget")


def test_an_honest_unknown_row_is_counted_not_rejected(pair, tmp_path):
    b = copy.deepcopy(pair)
    _make_unknown(b)
    _claim(b, "E4", REMAINING)["outcome"] = "unknown"
    totals, report = run_rc(b, tmp_path)
    assert totals["verified"] is True and totals["unknown_rows"] == 1
    assert report["seams"]["E4"]["recomputed_verdict"] == "unknown"


def test_an_unknown_row_must_change_the_declared_outcome(pair, tmp_path):
    b = copy.deepcopy(pair)
    _make_unknown(b)
    totals, report = run_rc(b, tmp_path)
    assert totals["verified"] is False and "verdict" in reasons(report)


def test_exit_codes_genuine_inflated_witness_inflated_gap_invalid_plane(pair, tmp_path):
    cases = {"genuine": copy.deepcopy(pair), "inflated_witness": copy.deepcopy(pair),
             "inflated_gap": copy.deepcopy(pair), "invalid_plane": rebind(pair, "E9", material=R02["ring_not_on_plane"])}
    FAULTS["witness_bound"](cases["inflated_witness"])
    FAULTS["euclidean_gap_bound"](cases["inflated_gap"])
    codes = {}
    for name, b in cases.items():
        path = tmp_path / f"{name}.json"
        path.write_text(json.dumps(b), encoding="ascii")
        codes[name] = subprocess.run([sys.executable, "-B", str(HERE / "recheck_ideal_mpmath.py"), str(path),
                                      str(tmp_path / f"{name}.out.json")], capture_output=True).returncode
    assert codes == {"genuine": 0, "inflated_witness": 1, "inflated_gap": 1, "invalid_plane": 1}
