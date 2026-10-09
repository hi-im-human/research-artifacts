"""Exact positive trim that reuses the identical stored face maps (standard library only)."""
from __future__ import annotations

import copy
from fractions import Fraction

from ..core.numbers import ExactInputError, format_exact, parse_exact
from .cut import DevelopmentInputError

__all__ = ["apply_trim"]


def apply_trim(development: dict, delta) -> dict:
    """two_rim.trim/1 payload: exact band delta <= t <= 1-delta on every face; maps copied unchanged."""
    if development.get("schema") != "two_rim.development/1":
        raise DevelopmentInputError(f"unsupported development schema {development.get('schema')!r}")
    try:
        d = parse_exact(delta)
    except ExactInputError as exc:
        raise DevelopmentInputError(f"delta is not exact: {exc}") from None
    if not Fraction(0) < d < Fraction(1, 2):
        raise DevelopmentInputError(f"trim depth must satisfy 0 < delta < 1/2, got {format_exact(d)}")
    material = development["cut"]["material"]
    xyz = {v["id"]: [Fraction(c) for c in v["xyz"]] for v in material["vertices"]}
    points = {}
    for e in material["hinges"]:
        lo, hi = xyz[e["lower"]], xyz[e["upper"]]
        for tag, t in (("lo", d), ("hi", 1 - d)):
            points[f"{e['id']}@{tag}"] = {"hinge": e["id"], "t": format_exact(t),
                                          "xyz": [format_exact(a + t * (b - a)) for a, b in zip(lo, hi)]}
    faces = [{"face": f["id"], "boundary": [f"{f['entry']}@lo", f"{f['entry']}@hi", f"{f['exit']}@hi",
                                            f"{f['exit']}@lo"]} for f in material["faces"]]
    return {"schema": "two_rim.trim/1", "delta": format_exact(d),
            "height_parameter": "original normalized height t = z/h",
            "maps": copy.deepcopy(development["maps"]), "trim_points": points, "faces": faces}
