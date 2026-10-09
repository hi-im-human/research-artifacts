"""Derived display data from a SAVED run (a LoadedRun or its record); the viewer renders only this data.

Face images are evaluated here from the stored maps and exact coordinates (float64 display cache);
the viewer performs no geometry.
"""
from __future__ import annotations

from fractions import Fraction

__all__ = ["view_data"]


def _apply(m, p):
    return [sum(m["linear"][r][c] * p[c] for c in range(3)) + m["offset"][r] for r in range(2)]


def view_data(loaded, subject: str, statuses=None) -> dict:
    """statuses: optional {"local": ..., "source_linked": ...} totals from the search, shown as supplied."""
    record = loaded.record if hasattr(loaded, "record") else loaded
    states = record["states"]
    chain, h = [], subject
    while h is not None:
        chain.append(states[h])
        h = states[h]["parent"]
    kinds = {s["kind"]: s for s in chain}
    subj = states[subject]
    material = kinds["two_rim.material"]["payload"]
    cut = kinds["two_rim.cut"]["payload"]
    maps = {m["face"]: m for m in subj["payload"]["maps"]}
    xyz = {v["id"]: [float(Fraction(c)) for c in v["xyz"]] for v in material["vertices"]}
    faces = {f["id"]: f for f in material["faces"]}
    order = cut["face_order"]
    if subj["kind"] == "two_rim.trimmed_development":
        pts = {k: [float(Fraction(c)) for c in v["xyz"]] for k, v in subj["payload"]["trim_points"].items()}
        rings = {f["face"]: f["boundary"] for f in subj["payload"]["faces"]}
        seam_labels = (f"{cut['seam']}@lo", f"{cut['seam']}@hi")
    else:
        pts = xyz
        rings = {f: faces[f]["boundary"] for f in order}
        seam_e = next(e for e in material["hinges"] if e["id"] == cut["seam"])
        seam_labels = (seam_e["lower"], seam_e["upper"])
    planar = {f: {"labels": rings[f], "xy": [_apply(maps[f], pts[k]) for k in rings[f]]} for f in order}
    evidence = [e for e in record["evidence"] if e["subject"] == subject]
    pairs = next((e for e in evidence if e["claim"] == "two_rim.development.face_interiors_disjoint_all_pairs"), None)
    problem_pairs = [{"pair": r["pair"], "outcome": r["outcome"], "reason": r["reason"], "shared": r["shared"]}
                     for r in (pairs["receipt"]["rows"] if pairs else []) if r["outcome"] != "pass"]
    return {"schema": "geometry-lab.view/3",
            "derived": "display cache computed from the saved run's states; regenerate from the run file",
            "subject_state": subject, "state_kind": subj["kind"], "delta": subj["payload"].get("delta"),
            "material_identity": material["identity"], "height": material["height"], "face_order": order,
            "faces_3d": {f: {"boundary": faces[f]["boundary"], "shape": faces[f]["shape"],
                             "xyz": [xyz[v] for v in faces[f]["boundary"]]} for f in order},
            "planar": planar,
            "seam": {"id": cut["seam"], "entry_face": order[0], "exit_face": order[-1],
                     "copies": [[_apply(maps[order[0]], pts[k]) for k in seam_labels],
                                [_apply(maps[order[-1]], pts[k]) for k in seam_labels]],
                     "xyz": [xyz[v] for v in (next(e for e in material["hinges"] if e["id"] == cut["seam"])[k]
                                               for k in ("lower", "upper"))]},
            "evidence": [{"claim": e["claim"], "outcome": e["outcome"], "method": e["method"],
                          "coverage": e["coverage"]} for e in evidence],
            "problem_pairs": problem_pairs,
            "statuses": None if statuses is None else {"local": statuses["local"],
                                                       "source_linked": statuses["source_linked"]}}
