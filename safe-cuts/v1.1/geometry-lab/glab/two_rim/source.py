"""Exact two-rim source normalization. Standard library + glab.core only.

`hull2` is ported from the Observatory helper `normal_fan_inputs.py` (see PROVENANCE-STAGE-2.json):
same monotone-chain algorithm and the same removal of straight-through boundary points. Cyclic
input is validated by its own exact predicates here and is never repaired.
"""
from __future__ import annotations

import copy
from fractions import Fraction

from ..core.numbers import ExactInputError, format_exact, parse_exact

__all__ = ["SourceInputError", "INPUT_KINDS", "UNITS", "COORDINATE_CONVENTION", "normalize_source", "hull2"]

INPUT_KINDS = ("cyclic_boundary", "point_set_hull")
UNITS = "unitless"
COORDINATE_CONVENTION = ("right-handed xyz; bottom rim B at z = 0, top rim A at z = h; each normalized rim is "
                         "a strictly convex ring in clockwise order (negative signed area in the xy plane) "
                         "starting at its lexicographically smallest (x, then y) vertex")

Point = tuple  # (Fraction, Fraction)


class SourceInputError(ValueError):
    """The source input is malformed or violates a source condition; nothing is repaired."""


def _cross(o, a, b) -> Fraction:
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def hull2(points) -> list:
    """Ported monotone-chain convex hull (counterclockwise), straight-through boundary points removed.

    Original: normal_fan_inputs.hull2 (blob 5445ec10). Change: raises SourceInputError instead of
    ValueError and takes already-parsed Fraction pairs; the algorithm and tie rules are unchanged.
    """
    pts = sorted(set(points))
    if len(pts) < 3:
        raise SourceInputError("empty interior: a polygon needs at least three noncollinear points")
    lower: list = []
    upper: list = []
    for p in pts:
        while len(lower) >= 2 and _cross(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)
    for p in reversed(pts):
        while len(upper) >= 2 and _cross(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)
    hull = lower[:-1] + upper[:-1]
    if len(hull) < 3:
        raise SourceInputError("empty interior: all points are collinear")
    return hull


def _parse_points(raw, label) -> list:
    if not isinstance(raw, list):
        raise SourceInputError(f"{label} rim must be a list of points")
    out = []
    for i, p in enumerate(raw):
        if not isinstance(p, list) or len(p) != 2:
            raise SourceInputError(f"{label}[{i}] must be a point with exactly two coordinates, got {p!r}")
        try:
            out.append((parse_exact(p[0]), parse_exact(p[1])))
        except ExactInputError as exc:
            raise SourceInputError(f"{label}[{i}] is not exact: {exc}") from None
    return out


def _canonical_start(ring_cw: list) -> tuple[list, int]:
    k = ring_cw.index(min(ring_cw))
    return ring_cw[k:] + ring_cw[:k], k


def _turn_sign(ring) -> int:
    """+1 all strictly left turns, -1 all strictly right turns, 0 otherwise (collinear or reflex)."""
    n = len(ring)
    signs = {(_cross(ring[i], ring[(i + 1) % n], ring[(i + 2) % n]) > 0) -
             (_cross(ring[i], ring[(i + 1) % n], ring[(i + 2) % n]) < 0) for i in range(n)}
    return signs.pop() if len(signs) == 1 and 0 not in signs else 0


def _winds_once_clockwise(ring_cw) -> bool:
    """Every turn is clockwise and < pi, so edge directions pass angle 0 once per revolution."""
    n = len(ring_cw)
    edges = [(ring_cw[(i + 1) % n][0] - ring_cw[i][0], ring_cw[(i + 1) % n][1] - ring_cw[i][1]) for i in range(n)]
    return sum(1 for i in range(n) if edges[i][1] >= 0 and edges[(i + 1) % n][1] < 0) == 1


def _on_segment(p, a, b) -> bool:
    return _cross(a, b, p) == 0 and min(a[0], b[0]) <= p[0] <= max(a[0], b[0]) \
        and min(a[1], b[1]) <= p[1] <= max(a[1], b[1])


def _normalize_rim(raw, kind, label):
    pts = _parse_points(raw, label)
    if kind == "cyclic_boundary":
        if len(pts) < 3:
            raise SourceInputError(f"{label} rim needs at least 3 points, got {len(pts)}")
        if len(set(pts)) != len(pts):
            raise SourceInputError(f"{label} rim repeats a point; a cyclic boundary lists each vertex once")
        if all(_cross(pts[0], pts[1], p) == 0 for p in pts):
            raise SourceInputError(f"{label} rim has empty interior: all points are collinear")
        sign = _turn_sign(pts)
        if sign == 0:
            raise SourceInputError(f"{label} rim is not strictly convex in the given cyclic order "
                                   "(collinear or reflex turn); use point_set_hull to request a hull")
        ring_cw = pts if sign < 0 else pts[::-1]
        if not _winds_once_clockwise(ring_cw):
            raise SourceInputError(f"{label} rim is not a simple boundary: it winds more than once")
        canon, k = _canonical_start(ring_cw)
        start_input = k if sign < 0 else len(pts) - 1 - k
        decision = {"input_kind": kind, "input_count": len(pts),
                    "input_orientation": "clockwise" if sign < 0 else "counterclockwise",
                    "reversed": sign > 0, "start_input_index": start_input, "removed": []}
        return canon, decision
    if kind == "point_set_hull":
        ccw = hull2(pts)
        canon, _ = _canonical_start(ccw[::-1])
        vertices, seen, removed = set(canon), set(), []
        m = len(canon)
        for i, p in enumerate(pts):
            if p in seen:
                reason = "duplicate"
            elif p in vertices:
                reason = None
            elif any(_on_segment(p, canon[j], canon[(j + 1) % m]) for j in range(m)):
                reason = "boundary_non_vertex"
            else:
                reason = "interior"
            seen.add(p)
            if reason:
                removed.append({"input_index": i, "point": [format_exact(p[0]), format_exact(p[1])], "reason": reason})
        decision = {"input_kind": kind, "input_count": len(pts), "hull_vertex_count": m, "removed": removed}
        return canon, decision
    raise SourceInputError(f"input_kind must be one of {INPUT_KINDS}, got {kind!r}")


def normalize_source(top, bottom, height, input_kind) -> dict:
    """Source payload (schema two_rim.source/1). Raises SourceInputError; never repairs input."""
    if input_kind not in INPUT_KINDS:
        raise SourceInputError(f"input_kind must be one of {INPUT_KINDS}, got {input_kind!r}")
    try:
        h = parse_exact(height)
    except ExactInputError as exc:
        raise SourceInputError(f"height is not exact: {exc}") from None
    if h <= 0:
        raise SourceInputError(f"height must be positive, got {format_exact(h)}")
    a, da = _normalize_rim(top, input_kind, "top")
    b, db = _normalize_rim(bottom, input_kind, "bottom")

    def fmt(ring):
        return [[format_exact(x), format_exact(y)] for x, y in ring]
    return {"schema": "two_rim.source/1", "units": UNITS, "coordinate_convention": COORDINATE_CONVENTION,
            "number_domain": "exact_rational",
            "input": {"top": copy.deepcopy(top), "bottom": copy.deepcopy(bottom), "height": copy.deepcopy(height),
                      "input_kind": input_kind},
            "normalized": {"top": fmt(a), "bottom": fmt(b), "height": format_exact(h)},
            "normalization": {"top": da, "bottom": db}}
