"""Stage 4A repair A03 (isolated prototype): the re-checker's input contract, one fault at a time.

Runs only in the throwaway review environment (needs mpmath); skipped elsewhere.
"""
import copy
import json
import subprocess
import sys
from fractions import Fraction as F
from pathlib import Path

import pytest

pytest.importorskip("mpmath")

from glab.core.records import content_hash                    # noqa: E402
from probes.stage4a import recheck_mpmath as rc               # noqa: E402
from probes.stage4a.run_probe import recheck_bundle           # noqa: E402
from probes.stage4a.specimens import E11, prepare             # noqa: E402

HERE = Path(__file__).resolve().parents[2]


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


def test_genuine_bundle_is_verified(genuine, tmp_path):
    totals, report = run(genuine, tmp_path)
    assert totals["verified"] is True and totals["failures"] == 0
    assert report["seams"]["E9"]["status"] == report["seams"]["E4"]["status"] == "verified"
    assert totals["coordinates_checked"] == totals["coordinates_contained"] == 176
    assert totals["rows_checked"] == totals["expected_pairs"] == 110 and totals["unknown_rows"] == 0


def _first(bundle, seam, method):
    return next(r for r in bundle["seams"][seam]["rows"] if r.get("method") == method)


def _mutations():
    def zero_axis(b):
        _first(b, "E4", "separating_axis")["certificate"]["axis"] = ["0", "0"]

    def bad_order(b):
        _first(b, "E4", "separating_axis")["certificate"]["order"] = "sideways"

    def noncanonical(b):
        c = _first(b, "E4", "separating_axis")["certificate"]
        c["axis"][0] = str(F(c["axis"][0]).numerator * 2) + "/" + str(F(c["axis"][0]).denominator * 2)

    def reversed_bounds(b):
        box = b["seams"]["E4"]["boxes"]["F5"][0][0]
        box[0], box[1] = box[1], box[0]

    def face_truncated(b):
        b["seams"]["E4"]["boxes"]["F5"] = b["seams"]["E4"]["boxes"]["F5"][:3]

    def coordinate_three(b):
        b["seams"]["E4"]["boxes"]["F5"][1] = b["seams"]["E4"]["boxes"]["F5"][1] + [["0", "0"]]

    def missing_face(b):
        del b["seams"]["E4"]["boxes"]["F5"]

    def extra_face(b):
        b["seams"]["E4"]["boxes"]["F99"] = copy.deepcopy(b["seams"]["E4"]["boxes"]["F5"])

    def missing_row(b):
        b["seams"]["E4"]["rows"].pop(7)

    def duplicate_row(b):
        b["seams"]["E4"]["rows"].append(copy.deepcopy(b["seams"]["E4"]["rows"][7]))

    def wrong_id(b):
        b["seams"]["E4"]["rows"][7]["pair"][1] = "F99"

    def reversed_pair(b):
        b["seams"]["E4"]["rows"][7]["pair"].reverse()

    def witness_as_pass(b):
        _first(b, "E9", "interior_witness")["outcome"] = "pass"

    def shared_on_nonconsecutive(b):
        axis_row = _first(b, "E4", "separating_axis")
        shared = _first(b, "E4", "shared_hinge_exact")
        axis_row["method"] = "shared_hinge_exact"
        axis_row["shared_hinge"] = copy.deepcopy(shared["shared_hinge"])

    def verdict_mismatch(b):
        b["seams"]["E9"]["verdict_on_D"] = "pass"

    def spec_altered(b):
        b["seams"]["E4"]["subject"]["spec"]["seam"] = "E5"

    def state_altered(b):
        cut = b["seams"]["E4"]["subject"]["spec"]["cut_state"]
        b["states"][cut]["payload"]["seam"] = "E5"

    def unbound(b):
        del b["schema"]

    return {"axis_zero": zero_axis, "axis_order": bad_order, "noncanonical_number": noncanonical,
            "interval_bounds": reversed_bounds, "box_shape": face_truncated, "box_shape_coordinate": coordinate_three,
            "box_coverage": missing_face, "box_coverage_extra": extra_face, "pair_coverage": missing_row,
            "pair_duplicate": duplicate_row, "pair_ids": wrong_id, "pair_order": reversed_pair,
            "method_outcome": witness_as_pass, "shared_hinge_pair": shared_on_nonconsecutive,
            "verdict": verdict_mismatch, "subject_id": spec_altered, "state_hash": state_altered,
            "bundle_schema": unbound}


EXPECTED = {"box_shape_coordinate": "box_shape", "box_coverage_extra": "box_coverage"}


@pytest.mark.parametrize("name", sorted(_mutations()))
def test_single_fault_is_rejected_with_its_reason(genuine, tmp_path, name):
    b = copy.deepcopy(genuine)
    _mutations()[name](b)
    totals, report = run(b, tmp_path)
    assert totals["verified"] is False and totals["failures"] > 0, name
    assert EXPECTED.get(name, name) in reasons(report), (name, sorted(reasons(report)))


def test_parent_link_forgery_with_consistent_hashes_is_rejected(genuine, tmp_path):
    b = copy.deepcopy(genuine)
    seam = b["seams"]["E4"]
    spec = seam["subject"]["spec"]
    cut = copy.deepcopy(b["states"][spec["cut_state"]])
    cut["parent"] = spec["source_state"]                       # cut claims the source as its parent
    new = content_hash(cut)
    b["states"][new] = cut
    spec["cut_state"] = new
    seam["subject"]["id"] = content_hash(spec)
    totals, report = run(b, tmp_path)
    assert totals["verified"] is False and "parent_link" in reasons(report)


def test_delta_changed_with_a_consistent_id_fails_geometry_not_silently(genuine, tmp_path):
    b = copy.deepcopy(genuine)
    seam = b["seams"]["E4"]
    seam["subject"]["spec"]["delta"] = "1/5000"
    seam["subject"]["id"] = content_hash(seam["subject"]["spec"])
    totals, report = run(b, tmp_path)
    assert totals["verified"] is False and report["seams"]["E4"]["status"] == "failed"
    assert "containment" in reasons(report)


def test_honest_unknown_row_is_counted_not_rejected(genuine, tmp_path):
    b = copy.deepcopy(genuine)
    row = _first(b, "E4", "separating_axis")
    for k in ("method", "certificate", "bits"):
        row.pop(k, None)
    row["outcome"] = "unknown"
    b["seams"]["E4"]["verdict_on_D"] = "unknown"
    totals, report = run(b, tmp_path)
    assert totals["verified"] is True and totals["failures"] == 0 and totals["unknown_rows"] == 1
    assert report["seams"]["E4"]["recomputed_verdict"] == "unknown"


def test_unknown_row_must_change_the_declared_verdict(genuine, tmp_path):
    b = copy.deepcopy(genuine)
    row = _first(b, "E4", "separating_axis")
    for k in ("method", "certificate", "bits"):
        row.pop(k, None)
    row["outcome"] = "unknown"                                  # declared verdict left as pass
    totals, report = run(b, tmp_path)
    assert totals["verified"] is False and "verdict" in reasons(report)


def test_exit_code_reflects_verification(genuine, tmp_path):
    good, bad = tmp_path / "good.json", tmp_path / "bad.json"
    good.write_text(json.dumps(genuine), encoding="ascii")
    b = copy.deepcopy(genuine)
    b["seams"]["E4"]["rows"].pop(3)
    bad.write_text(json.dumps(b), encoding="ascii")
    script = HERE / "recheck_mpmath.py"
    ok = subprocess.run([sys.executable, "-B", str(script), str(good), str(tmp_path / "g.out.json")])
    ko = subprocess.run([sys.executable, "-B", str(script), str(bad), str(tmp_path / "b.out.json")])
    assert ok.returncode == 0 and ko.returncode != 0


def test_verbatim_style_unbound_bundle_is_rejected_for_the_binding_only(tmp_path):
    """System's verbatim A03 cases pass after the repair only because their unbound (pre-repair layout) bundle is
    rejected before any other check; that is not coverage of their properties (see ADAPTER-NOTE.md)."""
    from probes.stage4a.classify import classify_seam, to_json
    from probes.stage4a.ideal import enclose, load_subject
    from probes.stage4a.specimens import E11_DELTA
    p = prepare(E11, seams=["E9"])
    m = p.run.get(p.material)["payload"]
    s = load_subject(p, "E9", E11_DELTA)
    legacy = {"delta": E11_DELTA, "bits": 128, "vertices": {v["id"]: v["xyz"] for v in m["vertices"]},
              "faces": [{k: f[k] for k in ("id", "entry", "exit", "boundary", "plane")} for f in m["faces"]],
              "hinges": {e["id"]: [e["lower"], e["upper"]] for e in m["hinges"]},
              "seams": {"E9": {"subject_id": s.id, "chain": s.model.chain, "rings": s.model.rings,
                               "boxes": to_json(enclose(s.model, 128)["boxes"]),
                               "rows": to_json(classify_seam(s.model, schedule=(128,))["rows"])}}}
    totals, report = run(legacy, tmp_path)
    assert totals["verified"] is False and reasons(report) == {"bundle_schema"}


def test_recheck_constants_match_the_probe_definitions():
    from probes.stage4a.ideal import DEFINITION, NORMALIZATION, ORIENTATION
    assert (rc.DEFINITION, rc.ORIENTATION, rc.NORMALIZATION) == (DEFINITION, ORIENTATION, NORMALIZATION)
