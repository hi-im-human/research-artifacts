"""Exact cut topology: open one original lateral hinge of a stored two-rim material (standard library only).

Glue classes follow the manuscript's CutRelated relation on vertices: for each material vertex,
the faces containing it are split into maximal runs of consecutive chain positions; each run
is one class. Coincident coordinates never glue anything.
"""
from __future__ import annotations

import copy

__all__ = ["DevelopmentInputError", "open_cut", "chain_order", "glue_classes"]


class DevelopmentInputError(ValueError):
    """A cut/development/trim request that cannot construct a result (reported, never repaired)."""


def chain_order(material: dict, seam: str) -> list:
    ids = [e["id"] for e in material["hinges"]]
    if seam not in ids:
        raise DevelopmentInputError(f"seam {seam!r} is not an original lateral hinge; valid: {ids}")
    k, n = ids.index(seam), len(ids)
    faces = [f["id"] for f in material["faces"]]
    if [f["entry"] for f in material["faces"]] != ids:
        raise DevelopmentInputError("material faces are not in hinge order")
    return [faces[(k + j) % n] for j in range(n)]


def glue_classes(material: dict, order: list) -> list:
    """CutRelated vertex runs, in material vertex order, then chain position."""
    boundary = {f["id"]: f["boundary"] for f in material["faces"]}
    classes = []
    for v in (v["id"] for v in material["vertices"]):
        run = []
        for fid in order:
            if v in boundary[fid]:
                run.append(f"{fid}@{v}")
            elif run:
                classes.append(run)
                run = []
        if run:
            classes.append(run)
    return classes


def open_cut(material: dict, seam: str) -> dict:
    """two_rim.cut/1 payload for one original seam; carries an exact copy of the material."""
    if material.get("schema") != "two_rim.material/1":
        raise DevelopmentInputError(f"unsupported material schema {material.get('schema')!r}")
    order = chain_order(material, seam)
    boundary = {f["id"]: f["boundary"] for f in material["faces"]}
    return {"schema": "two_rim.cut/1", "seam": seam, "face_order": order,
            "retained_hinges": [e["id"] for e in material["hinges"] if e["id"] != seam],
            "occurrences": [f"{fid}@{v}" for fid in order for v in boundary[fid]],
            "glue_classes": glue_classes(material, order),
            "seam_copies": {"entry": {"face": order[0], "hinge": seam}, "exit": {"face": order[-1], "hinge": seam}},
            "material": copy.deepcopy(material)}
