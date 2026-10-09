"""Original maximal lateral facets, hinges, rim edges and caps from a normalized source. Exact only.

`splice_cycles` is ported from the Observatory helper `cyclic_normal_splice.py` (see
PROVENANCE-STAGE-2.json): same insertion of B-only normal rays into A's clockwise normal cones,
same scalar-only sorting inside one A corner, same primitive integer rays. No floats, angles,
trigonometry or hull oracle are used by the construction.
"""
from __future__ import annotations

from fractions import Fraction
from math import gcd, lcm

from ..core.numbers import format_exact
from ..core.records import content_hash

__all__ = ["SpliceError", "MaterialError", "splice_cycles", "build_material", "material_identity"]


class SpliceError(ArithmeticError):
    """An internal exact condition of the splice construction failed (reported, never patched)."""


class MaterialError(ValueError):
    """The normalized source does not yield a consistent original material (source-model contradiction)."""


# ------------------------------------------------------------------ ported exact helpers

def _cross2(a, b) -> Fraction:
    return a[0] * b[1] - a[1] * b[0]


def _dot(a, b) -> Fraction:
    return sum((Fraction(x) * Fraction(y) for x, y in zip(a, b)), Fraction(0))


def _primitive(values) -> tuple:
    """Primitive integer representative of a positive ray/plane (sign kept: opposite rays differ)."""
    q = tuple(Fraction(v) for v in values)
    den = lcm(*(v.denominator for v in q))
    ints = tuple(int(v * den) for v in q)
    g = gcd(*ints)
    if not g:
        raise SpliceError("zero does not determine a direction")
    return tuple(v // g for v in ints)


def _sub(a, b):
    return a[0] - b[0], a[1] - b[1]


def _raw_normals(v):
    """Actual Lean convention: rotate each clockwise edge by (-y, x); these point outward."""
    out = []
    for i, p in enumerate(v):
        e = _sub(v[(i + 1) % len(v)], p)
        out.append((-e[1], e[0]))
    return out


def _check_raw_polygon(v):
    for i, u in enumerate(_raw_normals(v)):
        if u == (0, 0):
            raise SpliceError("raw cyclic edges must be nonzero")
        for j, p in enumerate(v):
            z = _dot(u, _sub(p, v[i]))
            if z > 0 or (z == 0 and j not in (i, (i + 1) % len(v))):
                raise SpliceError("raw clockwise support/reducedness condition failed")


def _maximizers(v, w):
    values = [_dot(w, p) for p in v]
    m = max(values)
    return tuple(i for i, x in enumerate(values) if x == m)


def _blend(u, v, t):
    return (1 - t) * u[0] + t * v[0], (1 - t) * u[1] + t * v[1]


def splice_cycles(a, b) -> dict:
    """Ported from cyclic_normal_splice.splice_cycles (blob 314b1938).

    a, b: clockwise reduced rims (A top, B bottom) as Fraction pairs. Returns
    {"rays": [...], "support_pairs": [(top index, bottom index), ...]} where support pair t
    describes the open normal gap following ray t. Changes from the original: plain dict
    result instead of dataclasses, Fraction pairs in, SpliceError for internal failures.
    """
    _check_raw_polygon(a)
    _check_raw_polygon(b)
    na, nb = _raw_normals(a), _raw_normals(b)
    a_rays = {_primitive(u) for u in na}
    knots = [{Fraction(0), Fraction(1)} for _ in a]
    for w in nb:
        if _primitive(w) in a_rays:
            continue  # already owned by exactly one A-block left endpoint
        owners = _maximizers(a, w)
        if len(owners) != 1:
            raise SpliceError("a B-only ray did not have a unique A vertex")
        i = owners[0]
        back, ahead = _sub(a[i - 1], a[i]), _sub(a[(i + 1) % len(a)], a[i])
        d = _cross2(back, ahead)
        if d <= 0:
            raise SpliceError("derived clockwise corner determinant failed")
        lam, mu = -_dot(w, ahead) / d, -_dot(w, back) / d
        if lam <= 0 or mu <= 0:
            raise SpliceError("a B-only ray did not lie in a strict A cone")
        t = mu / (lam + mu)
        if _primitive(_blend(na[i - 1], na[i], t)) != _primitive(w):
            raise SpliceError("local positive-ray reconstruction failed")
        knots[i].add(t)
    rays, pairs = [], []
    for i, ks in enumerate(knots):
        ts = sorted(ks)  # scalar sort ONLY, within one already-ordered A corner
        for left, right in zip(ts, ts[1:]):
            w = _blend(na[i - 1], na[i], (left + right) / 2)
            ma, mb = _maximizers(a, w), _maximizers(b, w)
            if ma != (i,) or len(mb) != 1:
                raise SpliceError("an open merged subgap lacked unique support")
            rays.append(_primitive(_blend(na[i - 1], na[i], left)))
            pairs.append((i, mb[0]))
    return {"rays": rays, "support_pairs": pairs}


# ------------------------------------------------------------------ material construction

def _fr(pair):
    return Fraction(pair[0]), Fraction(pair[1])


def material_identity(payload: dict) -> str:
    """Content hash of the canonical material, excluding `identity` itself (never parent or presentation)."""
    return content_hash({k: v for k, v in payload.items() if k != "identity"})


def build_material(source: dict) -> dict:
    """Material payload (schema two_rim.material/1) from a two_rim.source/1 payload."""
    if source.get("schema") != "two_rim.source/1":
        raise MaterialError(f"unsupported source schema {source.get('schema')!r}")
    norm = source["normalized"]
    a = [_fr(p) for p in norm["top"]]
    b = [_fr(p) for p in norm["bottom"]]
    h = Fraction(norm["height"])
    spliced = splice_cycles(a, b)
    rays, pairs = spliced["rays"], spliced["support_pairs"]
    n = len(pairs)
    vertices = ([{"id": f"A{i}", "rim": "top", "xyz": [format_exact(x), format_exact(y), format_exact(h)]}
                 for i, (x, y) in enumerate(a)] +
                [{"id": f"B{j}", "rim": "bottom", "xyz": [format_exact(x), format_exact(y), "0"]}
                 for j, (x, y) in enumerate(b)])
    rim_edges = ([{"id": f"RA{i}", "rim": "top", "ends": [f"A{i}", f"A{(i + 1) % len(a)}"]} for i in range(len(a))] +
                 [{"id": f"RB{j}", "rim": "bottom", "ends": [f"B{j}", f"B{(j + 1) % len(b)}"]} for j in range(len(b))])
    hinges = [{"id": f"E{t}", "lower": f"B{j}", "upper": f"A{i}"} for t, (i, j) in enumerate(pairs)]
    faces = []
    for t in range(n):
        (i0, j0), (i1, j1) = pairs[t], pairs[(t + 1) % n]
        if i1 not in (i0, (i0 + 1) % len(a)) or j1 not in (j0, (j0 + 1) % len(b)) or (i0, j0) == (i1, j1):
            raise MaterialError(f"face {t}: consecutive hinges do not advance by one rim run")
        ring = [f"B{j0}", f"A{i0}", f"A{i1}", f"B{j1}"]
        edges = [f"E{t}", f"RA{i0}", f"E{(t + 1) % n}", f"RB{j0}"]
        if i1 == i0:        # top run vanishes: triangle with apex A{i0}
            ring, edges = [ring[0], ring[1], ring[3]], [edges[0], edges[2], edges[3]]
        elif j1 == j0:      # bottom run vanishes: triangle with apex B{j0}
            ring, edges = ring[:3], edges[:3]
        u = rays[(t + 1) % n]
        sigma_a = max(_dot(u, p) for p in a)
        sigma_b = max(_dot(u, p) for p in b)
        plane = _primitive((u[0], u[1], (sigma_b - sigma_a) / h, sigma_b))
        xyz = {v["id"]: tuple(Fraction(c) for c in v["xyz"]) for v in vertices}
        if any(_dot(plane[:3], xyz[v]) != plane[3] for v in ring):
            raise MaterialError(f"face {t}: ring vertices are not on the Proposition 3.1 supporting plane")
        faces.append({"id": f"F{t}", "entry": f"E{t}", "exit": f"E{(t + 1) % n}",
                      "shape": "triangle" if len(ring) == 3 else "trapezoid", "boundary": ring,
                      "boundary_edges": edges, "outward_ray": list(u), "plane": list(plane)})
    caps = [{"id": "C_TOP", "rim": "top", "boundary": [f"A{i}" for i in range(len(a))],
             "boundary_edges": [f"RA{i}" for i in range(len(a))], "plane": list(_primitive((0, 0, 1, h)))},
            {"id": "C_BOTTOM", "rim": "bottom", "boundary": [f"B{j}" for j in range(len(b))],
             "boundary_edges": [f"RB{j}" for j in range(len(b))], "plane": [0, 0, -1, 0]}]
    payload = {"schema": "two_rim.material/1", "units": source["units"],
               "coordinate_convention": source["coordinate_convention"], "number_domain": "exact_rational",
               "height": format_exact(h), "vertices": vertices, "rim_edges": rim_edges, "hinges": hinges,
               "faces": faces, "caps": caps}
    payload["identity"] = material_identity(payload)
    return payload
