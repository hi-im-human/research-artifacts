"""ISOLATED STAGE 4A PROTOTYPE: targets T1-T3, square prism, eleven-seam scan, historical reference, re-check bundle.

Usage (from engine/, maintained .venv, nothing installed):  python -m probes.stage4a.run_probe OUT_DIR
Order: controls are run and committed before this script is used (receipts/controls/).
Float states are used only to CHOOSE T1/T2 and for diagnostics; historical labels are read only AFTER
classification, for comparison.
"""
from __future__ import annotations

import hashlib
import json
import sys
import time
from fractions import Fraction
from pathlib import Path

from .classify import SCHEDULE, classify_pair, point_in_both, to_json
from .firewall import aligned_distance_to_enclosure, ideal_certificate
from .ideal import ISOLATED_LABEL, enclose, face_checks, load_subject
from .specimens import E11, E11_DELTA, SQUARE, float_states, prepare

__all__ = ["select_t1", "select_t2", "targets", "square_prism", "scan", "historical_reference", "recheck_bundle",
           "main"]

PAIRS = "two_rim.development.face_interiors_disjoint_all_pairs"


def _float_rows(prepared, seam):
    fl = float_states(prepared, seam, E11_DELTA)
    ev = next(e for e in fl["trimmed_evidence"] if e["claim"] == PAIRS)
    return fl, ev["receipt"]["rows"]


def select_t1(prepared, seam="E4"):
    """First retained hinge in chain order whose Stage 3 float row is near_contact_unresolved (choice only)."""
    subject = load_subject(prepared, seam, E11_DELTA)
    chain = subject.model.chain
    _, rows = _float_rows(prepared, seam)
    unresolved = {frozenset(r["pair"]) for r in rows
                  if r["shared"] == "retained_hinge" and r["reason"] == "near_contact_unresolved"}
    for a, b in zip(chain, chain[1:]):
        if frozenset((a, b)) in unresolved:
            return subject, a, b
    raise LookupError(f"no unresolved retained-neighbour float row on {seam}")


def select_t2(prepared, seam="E4"):
    """Unglued pair with the largest Stage 3 float separation (choice only)."""
    subject = load_subject(prepared, seam, E11_DELTA)
    pos = {f: i for i, f in enumerate(subject.model.chain)}
    _, rows = _float_rows(prepared, seam)
    best = min((r for r in rows if r["shared"] is None and r["outcome"] == "pass"), key=lambda r: r["sat_depth"])
    a, b = sorted(best["pair"], key=pos.get)
    return subject, a, b, best["sat_depth"]


def targets(prepared):
    s1, a1, b1 = select_t1(prepared)
    t1 = classify_pair(s1.model, a1, b1)
    t1_intervals_only = classify_pair(s1.model, a1, b1, try_shared=False)   # diagnostic: why Theorem S is needed
    s2, a2, b2, float_depth = select_t2(prepared)
    t2 = classify_pair(s2.model, a2, b2)
    s3 = load_subject(prepared, "E9", E11_DELTA)
    pos = {f: i for i, f in enumerate(s3.model.chain)}
    a3, b3 = sorted(("F10", "F7"), key=pos.get)
    t3 = classify_pair(s3.model, a3, b3)
    fl9 = float_states(prepared, "E9", E11_DELTA)
    diag = aligned_distance_to_enclosure(s3.model, enclose(s3.model, 128), prepared.run.get(fl9["trimmed"])["payload"])
    return {"label": ISOLATED_LABEL,
            "T1": {"subject": s1.spec, "subject_id": s1.id, "source_linked": s1.source_linked,
                   "selection": "first retained hinge in chain order on E4 whose Stage 3 float row is "
                                "near_contact_unresolved (the float row only chose the example)",
                   "row": t1, "same_pair_intervals_only": t1_intervals_only},
            "T2": {"subject": s2.spec, "subject_id": s2.id, "source_linked": s2.source_linked,
                   "selection": f"unglued pair on E4 with the largest Stage 3 float separation (sat_depth "
                                f"{float_depth})", "row": t2},
            "T3": {"subject": s3.spec, "subject_id": s3.id, "source_linked": s3.source_linked,
                   "selection": "known overlap F10/F7 at current E9 (mapped historical cut 6)", "row": t3},
            "E9_float_placement_vs_ideal_enclosure": diag}


def square_prism():
    out = {}
    for delta in ("1/4", "1/10000"):
        prep = prepare(SQUARE)
        for seam in prep.cuts:
            cert = ideal_certificate(load_subject(prep, seam, delta))
            widths = {str(w) for boxes in enclose(load_subject(prep, seam, delta).model, 64)["boxes"].values()
                      for box in boxes for w in (box[0].width(), box[1].width())}
            out[f"{seam}@{delta}"] = {"seam_verdict": cert["seam_verdict"], "digest": cert["digest"],
                                      "classification_digest": cert["classification_digest"],
                                      "all_box_widths_zero": widths == {"0"},
                                      "methods": sorted({r.get("method", "none") for r in
                                                         cert["classification"]["rows"]})}
    return {"label": ISOLATED_LABEL, "specimen": SQUARE, "seams": out}


def scan(prepared):
    seams, timing = {}, {}
    for seam in sorted(prepared.cuts, key=lambda s: int(s[1:])):
        t0 = time.perf_counter()
        cert = ideal_certificate(load_subject(prepared, seam, E11_DELTA))
        timing[seam] = time.perf_counter() - t0
        rows = cert["classification"]["rows"]
        bits = [r["bits"] for r in rows if "bits" in r]
        seams[seam] = {"seam_verdict": cert["seam_verdict"], "source_linked": cert["source_linked"],
                       "digest": cert["digest"], "classification_digest": cert["classification_digest"],
                       "shared_hinge_pass": sum(r.get("method") == "shared_hinge_exact" and r["outcome"] == "pass"
                                                for r in rows),
                       "axis_pass": sum(r.get("method") == "separating_axis" for r in rows),
                       "witness_fail": [r["pair"] for r in rows if r.get("method") == "interior_witness"],
                       "unknown": [r["pair"] for r in rows if r["outcome"] == "unknown"],
                       "max_bits_needed": max(bits) if bits else None, "certificate": cert}
    return seams, timing


def historical_reference(prepared, seams):
    """AFTER classification: compare with the mapped historical exact classes and certify its witness points in D."""
    from tests.two_rim_dev.eleven_panel import build_mapping, load_certificate   # test-side reference support
    cert = load_certificate()
    mapping = build_mapping(prepared.run.get(prepared.material)["payload"], cert)
    rows = []
    for k in range(mapping["n"]):
        seam = mapping["cuts"][k]
        historical = "unsafe" if k in cert["unsafe_cuts"] else "safe"
        ours = seams[seam]["seam_verdict"]
        verdict = {("unsafe", "fail"): "agree", ("safe", "pass"): "agree"}.get(
            (historical, ours), "not decided" if ours == "unknown" else "DISAGREE")
        rows.append({"historical_cut": k, "seam": seam, "historical_exact_class": historical,
                     "ideal_D_verdict": ours, "comparison": verdict})
    witnesses = []
    for rec in cert["overlap_receipts"]:
        seam = mapping["cuts"][rec["cut"]]
        subject = load_subject(prepared, seam, E11_DELTA)
        chain = subject.model.chain
        faces = [chain[i] for i in rec["panel_positions"]]
        y = tuple(Fraction(c) for c in rec["point"])
        ok = all(face_checks(subject.model)[f]["trimmed_ring_convex_counterclockwise"] for f in faces)
        boxes = enclose(subject.model, 128)["boxes"]
        margin = point_in_both(boxes[faces[0]], boxes[faces[1]], y) if ok else None
        witnesses.append({"historical_cut": rec["cut"], "seam": seam, "faces": faces, "point": rec["point"],
                          "certified_inside_both_faces_of_D": margin is not None,
                          "cross_lower_bound": None if margin is None else str(margin)})
    return {"label": ISOLATED_LABEL,
            "note": "historical classes and witness points are read only after classification; agreement on this "
                    "fixture is not a universal proof",
            "mapping_rotation": mapping["rotation_current_minus_historical"], "classes": rows,
            "historical_witness_points": witnesses}


def l4_hypotheses(model):
    """Exact per-instance hypotheses of the design's L4 derivation (section 2.5). The derivation itself is not checked.

    The chart psi_i = [nu_i ; -xi_i] has nu_i along M_exit - M_entry and xi_i along the component of the entry hinge
    G_i orthogonal to nu_i; its orientation sign with respect to n_i is sign(-(m x xi') . n_i), with exact
    m = M_exit - M_entry and xi' = G (m.m) - (G.m) m (positive rescalings of nu_i and xi_i).
    """
    from .ideal import cross, dot, sub
    mids = {h: tuple((a + b) / 2 for a, b in zip(*model.hinge_points(h))) for h in model.hinges}
    heights = {m[2] for m in mids.values()}
    extents = [U[2] - L[2] for L, U in (model.hinge_points(h) for h in model.hinges)]
    signs = {}
    for fid, f in model.faces.items():
        m = sub(mids[f["exit"]], mids[f["entry"]])
        G = sub(*reversed(model.hinge_points(f["entry"])))
        xi = tuple(g * dot(m, m) - dot(G, m) * c for g, c in zip(G, m))
        s = -dot(cross(m, xi), f["normal"])
        signs[fid] = (s > 0) - (s < 0)
    return {"all_hinge_midpoints_at_one_height": len(heights) == 1, "midpoint_height": str(next(iter(heights))),
            "all_hinge_z_extents_positive": all(x > 0 for x in extents),
            "chart_orientation_signs": signs, "uniform_orientation_preserving": set(signs.values()) == {1},
            "status": "exact hypotheses only; the L4 derivation (chart development = D) is not machine-checked"}


BUNDLE_SCHEMA = "stage4a.recheck_bundle/2"


def recheck_bundle(prepared, seams_to_export, delta=E11_DELTA):
    """Bound re-check bundle (repair A03): the three state records, and per seam the subject spec and ID, the
    128-bit boxes of the issued certificate's model, its rows and its declared verdict on D."""
    out = {"schema": BUNDLE_SCHEMA, "label": ISOLATED_LABEL, "bits": 128, "states": {}, "seams": {}}
    for seam in seams_to_export:
        subject = load_subject(prepared, seam, delta)
        cert = ideal_certificate(subject, schedule=(128,))
        if cert["status"] != "issued":
            raise RuntimeError(f"{seam}: certificate refused, nothing to export: {cert['refusal']}")
        spec = cert["subject"]["spec"]
        for key in ("source_state", "material_state", "cut_state"):
            out["states"][spec[key]] = prepared.run.get(spec[key])
        enc = enclose(subject.model, 128)       # bind() verified subject.model is the model of the named states
        out["seams"][seam] = {"subject": cert["subject"],
                              "boxes": {f: [[b[0].to_json(), b[1].to_json()] for b in boxes]
                                        for f, boxes in enc["boxes"].items()},
                              "rows": cert["classification"]["rows"], "verdict_on_D": cert["local_verdict_on_D"]}
    return to_json(out)


def _write(path: Path, obj):
    path.write_text(json.dumps(to_json(obj), indent=1, sort_keys=True) + "\n", encoding="ascii", newline="\n")


def main(out: Path):
    out.mkdir(parents=True, exist_ok=True)
    prepared = prepare(E11)
    _write(out / "targets.json", targets(prepared))
    _write(out / "square-prism.json", square_prism())
    seams, timing = scan(prepared)
    summary = {seam: {k: v for k, v in s.items() if k != "certificate"} for seam, s in seams.items()}
    _write(out / "scan-summary.json", {"label": ISOLATED_LABEL, "delta": E11_DELTA, "schedule": list(SCHEDULE),
                                       "seams": summary})
    _write(out / "scan-certificates.json", {"label": ISOLATED_LABEL,
                                            "certificates": {s: v["certificate"] for s, v in seams.items()}})
    _write(out / "historical-reference.json", historical_reference(prepared, seams))
    square = prepare(SQUARE)
    _write(out / "l4-hypotheses.json", {
        "label": ISOLATED_LABEL,
        "E11": l4_hypotheses(load_subject(prepared, "E9", E11_DELTA).model),
        "square_prism": l4_hypotheses(load_subject(square, "E0", "1/4").model)})
    _write(out / "recheck-bundle.json", recheck_bundle(prepared, sorted(prepared.cuts, key=lambda s: int(s[1:]))))
    (out / "timing.json").write_text(json.dumps({"label": ISOLATED_LABEL + "; wall-clock, not reproducible",
                                                 "seconds_per_seam_full_schedule": timing,
                                                 "total_seconds": sum(timing.values())}, indent=1) + "\n",
                                     encoding="ascii", newline="\n")
    manifest = {p.name: "sha256:" + hashlib.sha256(p.read_bytes()).hexdigest()
                for p in sorted(out.iterdir()) if p.name not in ("MANIFEST.json", "timing.json")}
    _write(out / "MANIFEST.json", manifest)
    return summary


if __name__ == "__main__":
    for seam, s in main(Path(sys.argv[1])).items():
        print(seam, s["seam_verdict"], "shared", s["shared_hinge_pass"], "axis", s["axis_pass"],
              "fail", s["witness_fail"], "unknown", len(s["unknown"]), "bits<=", s["max_bits_needed"])
