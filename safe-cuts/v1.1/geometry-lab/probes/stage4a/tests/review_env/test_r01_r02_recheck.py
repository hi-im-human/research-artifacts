"""Stage 4A re-check repair R01/R02 (isolated prototype): quantitative bounds and local geometry preconditions.

Single fault per test on a genuine bound bundle, with its expected reason code. Needs mpmath (review environment).
"""
import copy
import json
from fractions import Fraction as F
from math import isqrt

import pytest

pytest.importorskip("mpmath")

from probes.stage4a import recheck_mpmath as rc               # noqa: E402
from probes.stage4a.run_probe import recheck_bundle           # noqa: E402
from probes.stage4a.specimens import E11, prepare             # noqa: E402


@pytest.fixture(scope="module")
def genuine():
    return recheck_bundle(prepare(E11, seams=["E9", "E4"]), ["E9", "E4"])


def run(bundle, tmp_path):
    inp, out = tmp_path / "in.json", tmp_path / "out.json"
    inp.write_text(json.dumps(bundle), encoding="ascii")
    totals = rc.main(str(inp), str(out))
    return totals, json.loads(out.read_text(encoding="ascii"))


def reasons(report):
    return {f["code"] for s in report["seams"].values() for f in s["failures"]} | \
        {f["code"] for f in report.get("bundle_failures", [])}


def _first(b, seam, method):
    return next(r for r in b["seams"][seam]["rows"] if r.get("method") == method)


def _witness_minimum(b, seam):
    """The re-checker's own recomputed lower bound for the first witness row (exact, on the recorded boxes)."""
    row = _first(b, seam, "interior_witness")
    boxes = {f: rc.parse_box(v) for f, v in b["seams"][seam]["boxes"].items()}
    spec = b["seams"][seam]["subject"]["spec"]
    data = rc.Data(b["states"][spec["material_state"]]["payload"], spec["delta"])
    ok, m = rc.witness_ok(data, row["pair"], boxes[row["pair"][0]], boxes[row["pair"][1]], row["certificate"])
    assert ok
    return row, m


def test_genuine_bundle_still_verifies_and_states_its_scope(genuine, tmp_path):
    totals, report = run(genuine, tmp_path)
    assert totals["verified"] is True and totals["failures"] == 0
    scope = report["scope"]
    assert "not re-verified" in scope["stage2_source_correspondence_and_run_evidence"]
    assert "not a safety statement" in scope["meaning_of_verified"]
    assert set(report["diagnostic_fields_not_verified"]) >= {"bits", "attempts", "reason"}
    for seam in ("E9", "E4"):
        assert report["seams"][seam]["local_preconditions"] == "checked"


# ---------------------------------------------------------------- R01 witness bound

def test_witness_bound_at_the_recomputed_value_verifies(genuine, tmp_path):
    b = copy.deepcopy(genuine)
    row, m = _witness_minimum(b, "E9")
    row["certificate"]["cross_lower_bound"] = str(m)
    assert run(b, tmp_path)[0]["verified"] is True


def test_smaller_witness_bound_verifies(genuine, tmp_path):
    b = copy.deepcopy(genuine)
    row, m = _witness_minimum(b, "E9")
    row["certificate"]["cross_lower_bound"] = str(m / 3)
    assert run(b, tmp_path)[0]["verified"] is True


@pytest.mark.parametrize("inflate", ["just_above", "huge"])
def test_inflated_witness_bound_is_rejected(genuine, tmp_path, inflate):
    b = copy.deepcopy(genuine)
    row, m = _witness_minimum(b, "E9")
    row["certificate"]["cross_lower_bound"] = str(m + F(1, 10**40)) if inflate == "just_above" else "10" + "0" * 30
    totals, report = run(b, tmp_path)
    assert totals["verified"] is False and "witness_bound" in reasons(report)


# ---------------------------------------------------------------- R01 Euclidean gap bound

def _axis_limit(row):
    d = [F(x) for x in row["certificate"]["axis"]]
    g = F(row["certificate"]["axis_gap"])
    return d, g


def test_probe_recorded_and_zero_euclidean_bounds_verify(genuine, tmp_path):
    b = copy.deepcopy(genuine)
    _first(b, "E4", "separating_axis")["certificate"]["euclidean_gap_lower_bound"] = "0"
    assert run(b, tmp_path)[0]["verified"] is True        # genuine bundle keeps the probe's own recorded bounds


def test_euclidean_bound_just_above_the_exact_limit_is_rejected(genuine, tmp_path):
    b = copy.deepcopy(genuine)
    row = _first(b, "E4", "separating_axis")
    d, g = _axis_limit(row)
    dd = d[0] * d[0] + d[1] * d[1]
    # exact: N = floor(t * 10^80) with t = g^2/(d.d); b = (isqrt(N) + 1)/10^40 satisfies b^2 > t by about 10^-40
    t = g * g / dd
    n = (t.numerator * 10**80) // t.denominator
    root = F(isqrt(n) + 1, 10**40)
    assert root * root * dd > g * g and (root - F(2, 10**40)) ** 2 * dd <= g * g
    row["certificate"]["euclidean_gap_lower_bound"] = str(root)
    totals, report = run(b, tmp_path)
    assert totals["verified"] is False and "euclidean_gap_bound" in reasons(report)


def test_huge_euclidean_bound_is_rejected(genuine, tmp_path):
    b = copy.deepcopy(genuine)
    _first(b, "E4", "separating_axis")["certificate"]["euclidean_gap_lower_bound"] = "1" + "0" * 30
    totals, report = run(b, tmp_path)
    assert totals["verified"] is False and "euclidean_gap_bound" in reasons(report)


@pytest.mark.parametrize("value, code", [("-1", "euclidean_gap_bound_shape"), ("2/4", "noncanonical_number"),
                                         (None, "euclidean_gap_bound_shape")])
def test_malformed_euclidean_bound_is_rejected(genuine, tmp_path, value, code):
    b = copy.deepcopy(genuine)
    cert = _first(b, "E4", "separating_axis")["certificate"]
    if value is None:
        del cert["euclidean_gap_lower_bound"]
    else:
        cert["euclidean_gap_lower_bound"] = value
    totals, report = run(b, tmp_path)
    assert totals["verified"] is False and code in reasons(report)


def test_unrecognized_certificate_field_is_rejected_not_ignored(genuine, tmp_path):
    b = copy.deepcopy(genuine)
    _first(b, "E4", "separating_axis")["certificate"]["certified_area"] = "5"
    totals, report = run(b, tmp_path)
    assert totals["verified"] is False and "unrecognized_field" in reasons(report)


def test_positions_and_shared_hinge_record_are_verified(genuine, tmp_path):
    b = copy.deepcopy(genuine)
    _first(b, "E4", "separating_axis")["positions"] = [0, 1]
    totals, report = run(b, tmp_path)
    assert totals["verified"] is False and "positions" in reasons(report)
    b = copy.deepcopy(genuine)
    sh = _first(b, "E4", "shared_hinge_exact")["shared_hinge"]
    sh["sides"] = {k: -v for k, v in sh["sides"].items()}
    totals, report = run(b, tmp_path)
    assert totals["verified"] is False and "shared_hinge_record" in reasons(report)


# ---------------------------------------------------------------- R02 local geometry preconditions

def rebind(bundle, seam, mutate):
    """Mutate the material payload, then rehash material, cut and spec self-consistently (geometry is the fault)."""
    b = copy.deepcopy(bundle)
    spec = b["seams"][seam]["subject"]["spec"]
    mat = copy.deepcopy(b["states"][spec["material_state"]])
    mutate(mat["payload"])
    mat["payload"]["identity"] = rc.chash({k: v for k, v in mat["payload"].items() if k != "identity"})
    mh = rc.chash(mat)
    cut = copy.deepcopy(b["states"][spec["cut_state"]])
    cut["parent"] = mh
    cut["payload"]["material"] = copy.deepcopy(mat["payload"])
    ch = rc.chash(cut)
    b["states"][mh], b["states"][ch] = mat, cut
    spec.update(material_state=mh, material_identity=mat["payload"]["identity"], cut_state=ch)
    b["seams"][seam]["subject"]["id"] = rc.chash(spec)
    b["seams"] = {seam: b["seams"][seam]}
    return b


def _face(payload, fid):
    return next(f for f in payload["faces"] if f["id"] == fid)


def _hinge(payload, hid):
    return next(e for e in payload["hinges"] if e["id"] == hid)


def _offset(p):
    p["faces"][0]["plane"][3] += 1


def _inward(p):
    p["faces"][0]["plane"] = [-x for x in p["faces"][0]["plane"]]


def _zero_normal(p):
    p["faces"][0]["plane"] = [0, 0, 0, 0]


def _degenerate_hinge(p):
    h = _hinge(p, "E5")
    h["upper"] = h["lower"]


def _duplicate_vertex(p):
    p["vertices"].append(copy.deepcopy(p["vertices"][0]))


def _missing_hinge(p):
    p["faces"][0]["entry"] = "E99"


def _ring_lacks_endpoint(p):
    f = _face(p, "F5")
    lo = _hinge(p, f["entry"])["lower"]
    f["boundary"] = [v for v in f["boundary"] if v != lo]


def _swapped_hinge_ends(p):
    h = _hinge(p, "E5")
    h["lower"], h["upper"] = h["upper"], h["lower"]


R02_CASES = {"ring_not_on_plane": _offset, "orientation_not_outward": _inward, "normal_zero": _zero_normal,
             "hinge_degenerate": _degenerate_hinge, "identity_ambiguous": _duplicate_vertex,
             "reference_missing": _missing_hinge, "incidence": _ring_lacks_endpoint,
             "trimmed_ring_not_convex_ccw": _swapped_hinge_ends}


@pytest.mark.parametrize("code", sorted(R02_CASES))
def test_self_consistently_rehashed_bad_geometry_is_rejected_before_geometry(genuine, tmp_path, code):
    b = rebind(genuine, "E9", R02_CASES[code])
    totals, report = run(b, tmp_path)
    assert totals["verified"] is False and report["seams"]["E9"]["status"] == "rejected", code
    assert code in reasons(report), (code, sorted(reasons(report)))
    assert totals["coordinates_checked"] == 0          # rejected before any geometric confirmation


def test_rehash_without_mutation_still_verifies(genuine, tmp_path):
    b = rebind(genuine, "E9", lambda p: None)
    assert run(b, tmp_path)[0]["verified"] is True
