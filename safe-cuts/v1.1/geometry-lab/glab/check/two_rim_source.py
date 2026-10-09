"""Independent exact checker for two-rim source and material states.

Imports only glab.core and the standard library; it never imports glab.two_rim or the ported
helpers. It re-derives everything from the stored exact strings with its own predicates and a
brute-force supporting-plane oracle: it enumerates vertex triples and scans every vertex for each,
so O(V^4) exact arithmetic operations before rational bit-complexity; fine for bounded fixtures.

Version 2 (Stage 2 repair D01-D03): each record's `record_schema` claim is checked first, on the
lists themselves, before any set or dict can hide a duplicate; if it fails, every other claim for
that record is `unknown` (not interpreted; an unknown schema is never read as the old one). The
material checker is a declared contextual checker and adds `two_rim.material.matches_parent_source`,
comparing the material with its actual immediate source parent read through the core's read-only
DependencyContext. A malformed payload yields a `fail` claim with the error in the receipt; a
context read error is an attempt failure, never a claim.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import combinations
from math import gcd
from pathlib import Path

from ..core.numbers import ExactInputError, format_exact, parse_exact
from ..core.records import content_hash
from ..core.registry import CheckerSpec, Claim, source_revision
from ..core.runfile import ContextError

__all__ = ["check_source", "check_material", "supporting_planes", "register_checkers", "CHECKER_REVISION",
           "SOURCE_CLAIMS", "MATERIAL_CLAIMS"]

CHECKER_REVISION = source_revision(Path(__file__).resolve().parent, Path(__file__).name)


def _claim(predicate, ok, receipt):
    return Claim(predicate, "pass" if ok else "fail", "exact_computation", "exact_rational", coverage="all",
                 receipt=receipt)


def _unknown(predicate, reason):
    return Claim(predicate, "unknown", "exact_computation", "exact_rational", coverage="all",
                 receipt={"not_interpreted": reason})


def _guarded(predicate, fn):
    try:
        ok, receipt = fn()
    except ContextError:
        raise  # an attempt failure, not evidence about the geometry
    except (KeyError, IndexError, TypeError, ValueError, ZeroDivisionError, ExactInputError) as exc:
        ok, receipt = False, {"malformed": f"{type(exc).__name__}: {exc}"}
    return _claim(predicate, ok, receipt)


# ------------------------------------------------------------------ exact planar predicates

def _pt(p):
    """A planar point: exactly two exact coordinates (a longer or shorter list is never truncated)."""
    if not isinstance(p, list) or len(p) != 2:
        raise ValueError(f"a planar point needs exactly two coordinates, got {p!r}")
    return parse_exact(p[0]), parse_exact(p[1])


def _cross(o, a, b):
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def _strictly_convex_clockwise(ring):
    n = len(ring)
    if n < 3 or len(set(ring)) != n:
        return False
    if any(_cross(ring[i], ring[(i + 1) % n], ring[(i + 2) % n]) >= 0 for i in range(n)):
        return False
    edges = [(ring[(i + 1) % n][0] - ring[i][0], ring[(i + 1) % n][1] - ring[i][1]) for i in range(n)]
    return sum(1 for i in range(n) if edges[i][1] >= 0 and edges[(i + 1) % n][1] < 0) == 1


def _between(p, a, b):
    return _cross(a, b, p) == 0 and min(a[0], b[0]) <= p[0] <= max(a[0], b[0]) \
        and min(a[1], b[1]) <= p[1] <= max(a[1], b[1])


def _in_closed_triangle(p, a, b, c):
    d = _cross(a, b, c)
    if d == 0:
        return False
    s = [_cross(a, b, p), _cross(b, c, p), _cross(c, a, p)]
    return all(x >= 0 for x in s) if d > 0 else all(x <= 0 for x in s)


def _extreme_points(points):
    """Brute force: p is extreme iff it is in no closed triangle or segment of the other points."""
    out = []
    for i, p in enumerate(points):
        others = points[:i] + points[i + 1:]
        inside = any(_between(p, a, b) for a, b in combinations(others, 2)) or \
            any(_in_closed_triangle(p, a, b, c) for a, b, c in combinations(others, 3))
        if not inside:
            out.append(p)
    return out


# ------------------------------------------------------------------ record schemas (D02, D03)

SOURCE_SCHEMA, MATERIAL_SCHEMA = "two_rim.source/1", "two_rim.material/1"
UNITS, NUMBER_DOMAIN = "unitless", "exact_rational"
CONVENTION_V1 = ("right-handed xyz; bottom rim B at z = 0, top rim A at z = h; each normalized rim is "
                 "a strictly convex ring in clockwise order (negative signed area in the xy plane) "
                 "starting at its lexicographically smallest (x, then y) vertex")
_SOURCE_KEYS = {"schema", "units", "coordinate_convention", "number_domain", "input", "normalized", "normalization"}
_MATERIAL_KEYS = {"schema", "identity", "units", "coordinate_convention", "number_domain", "height", "vertices",
                  "rim_edges", "hinges", "faces", "caps"}
_DECISION_KEYS = {"cyclic_boundary": {"input_kind", "input_count", "input_orientation", "reversed",
                                      "start_input_index", "removed"},
                  "point_set_hull": {"input_kind", "input_count", "hull_vertex_count", "removed"}}
_REASONS = ("duplicate", "boundary_non_vertex", "interior")


def _is_int(x):
    return type(x) is int


def _canonical(s):
    try:
        return isinstance(s, str) and format_exact(parse_exact(s)) == s
    except ExactInputError:
        return False


def _exact_given(x):
    try:
        parse_exact(x)
        return True
    except ExactInputError:
        return False


def _points_ok(rim, canonical):
    ok = _canonical if canonical else _exact_given
    return isinstance(rim, list) and all(isinstance(q, list) and len(q) == 2 and ok(q[0]) and ok(q[1]) for q in rim)


def _int_list(x, n):
    return isinstance(x, list) and len(x) == n and all(_is_int(v) for v in x)


def _metadata_problems(p, schema):
    out = []
    if p.get("schema") != schema:
        out.append(f"unsupported schema {p.get('schema')!r} (supported: {schema})")
    if p.get("units") != UNITS or p.get("number_domain") != NUMBER_DOMAIN:
        out.append("units/number_domain differ from the supported contract")
    if p.get("coordinate_convention") != CONVENTION_V1:
        out.append("coordinate_convention differs from the supported contract")
    return out


def _decision_problems(rim, kind, d):
    if not isinstance(d, dict) or set(d) != _DECISION_KEYS[kind]:
        return [f"normalization.{rim}: keys must be {sorted(_DECISION_KEYS[kind])}"]
    out = []
    ints = ("input_count", "start_input_index") if kind == "cyclic_boundary" else ("input_count", "hull_vertex_count")
    if not all(_is_int(d[k]) for k in ints) or not isinstance(d["removed"], list):
        out.append(f"normalization.{rim}: counts must be ints and removed a list")
    if kind == "cyclic_boundary" and (type(d["reversed"]) is not bool or
                                      d["input_orientation"] not in ("clockwise", "counterclockwise")):
        out.append(f"normalization.{rim}: reversed/input_orientation malformed")
    for r in d["removed"] if isinstance(d["removed"], list) else []:
        if not (isinstance(r, dict) and set(r) == {"input_index", "point", "reason"} and _is_int(r["input_index"])
                and r["reason"] in _REASONS and _points_ok([r["point"]], True)):
            out.append(f"normalization.{rim}: malformed removed entry {r!r}")
    return out


def _source_schema(p):
    if not isinstance(p, dict) or set(p) != _SOURCE_KEYS:
        return False, {"problems": [f"source keys must be {sorted(_SOURCE_KEYS)}"]}
    problems = _metadata_problems(p, SOURCE_SCHEMA)
    inp, norm, dec = p["input"], p["normalized"], p["normalization"]
    kind = inp.get("input_kind") if isinstance(inp, dict) else None
    if not isinstance(inp, dict) or set(inp) != {"top", "bottom", "height", "input_kind"} or kind not in _DECISION_KEYS:
        problems.append("input must hold top, bottom, height and a supported input_kind")
    else:
        for rim in ("top", "bottom"):
            if not _points_ok(inp[rim], canonical=False):
                problems.append(f"input.{rim}: every point needs exactly two exact coordinates")
        if not _exact_given(inp["height"]):
            problems.append("input.height is not exact")
    if not isinstance(norm, dict) or set(norm) != {"top", "bottom", "height"}:
        problems.append("normalized must hold top, bottom and height")
    else:
        for rim in ("top", "bottom"):
            if not _points_ok(norm[rim], canonical=True) or len(norm[rim]) < 3:
                problems.append(f"normalized.{rim}: needs >= 3 points of exactly two canonical exact strings")
        if not _canonical(norm["height"]):
            problems.append("normalized.height is not a canonical exact string")
    if not isinstance(dec, dict) or set(dec) != {"top", "bottom"}:
        problems.append("normalization must hold top and bottom decisions")
    elif kind in _DECISION_KEYS:
        for rim in ("top", "bottom"):
            problems += _decision_problems(rim, kind, dec[rim])
    return not problems, {"schema": p.get("schema"), "problems": problems}


def _face_problems(f, hinge_ids, edge_ids, vertex_ids):
    keys = {"id", "entry", "exit", "shape", "boundary", "boundary_edges", "outward_ray", "plane"}
    if set(f) != keys:
        return [f"{f['id']}: keys must be {sorted(keys)}"]
    ring, redges = f["boundary"], f["boundary_edges"]
    ok = (f["entry"] in hinge_ids and f["exit"] in hinge_ids and f["shape"] in ("triangle", "trapezoid")
          and isinstance(ring, list) and len(ring) in (3, 4) and len(set(ring)) == len(ring)
          and set(ring) <= vertex_ids and isinstance(redges, list) and len(redges) == len(ring)
          and set(redges) <= edge_ids and _int_list(f["outward_ray"], 2) and _int_list(f["plane"], 4))
    return [] if ok else [f"{f['id']}: malformed field or undeclared reference"]


def _material_schema(p):
    """Shapes, ID namespaces and uniqueness, counts and references, checked on the LISTS first."""
    if not isinstance(p, dict) or set(p) != _MATERIAL_KEYS:
        return False, {"problems": [f"material keys must be {sorted(_MATERIAL_KEYS)}"]}
    problems = _metadata_problems(p, MATERIAL_SCHEMA)
    if not (isinstance(p["identity"], str) and p["identity"].startswith("sha256:") and len(p["identity"]) == 71):
        problems.append("identity is not a sha256 content hash")
    if not _canonical(p["height"]):
        problems.append("height is not a canonical exact string")
    verts = p["vertices"]
    if not isinstance(verts, list) or not all(isinstance(v, dict) and set(v) == {"id", "rim", "xyz"} and
                                              isinstance(v["xyz"], list) and len(v["xyz"]) == 3 and
                                              all(_canonical(c) for c in v["xyz"]) for v in verts):
        return False, {"problems": problems + ["vertices must be {id, rim, xyz: 3 canonical exact strings}"]}
    m = sum(v["rim"] == "top" for v in verts)
    k = len(verts) - m
    expected_ids = [f"A{i}" for i in range(m)] + [f"B{j}" for j in range(k)]
    if [v["id"] for v in verts] != expected_ids or [v["rim"] for v in verts] != ["top"] * m + ["bottom"] * k \
            or m < 3 or k < 3:
        problems.append("vertex ids must be A0..A{m-1} (top) then B0..B{k-1} (bottom), unique, with m, k >= 3")
    expected_edges = ([{"id": f"RA{i}", "rim": "top", "ends": [f"A{i}", f"A{(i + 1) % m}"]} for i in range(m)] +
                      [{"id": f"RB{j}", "rim": "bottom", "ends": [f"B{j}", f"B{(j + 1) % k}"]} for j in range(k)])
    if p["rim_edges"] != expected_edges:
        problems.append("rim_edges must be exactly RA0..RA{m-1} then RB0..RB{k-1} with consecutive ends")
    hinges, faces, caps = p["hinges"], p["faces"], p["caps"]
    n = len(faces) if isinstance(faces, list) else -1
    tops, bottoms = set(expected_ids[:m]), set(expected_ids[m:])
    if not isinstance(hinges, list) or n < 3 or \
            [h.get("id") if isinstance(h, dict) else None for h in hinges] != [f"E{t}" for t in range(n)]:
        problems.append("hinges must be exactly E0..E{n-1}, one per face (n >= 3), unique")
    else:
        for h in hinges:
            if set(h) != {"id", "lower", "upper"} or h["lower"] not in bottoms or h["upper"] not in tops:
                problems.append(f"{h['id']}: must be {{id, lower: B*, upper: A*}} referencing declared vertices")
    hinge_ids = {f"E{t}" for t in range(n)}
    edge_ids = hinge_ids | {e["id"] for e in expected_edges}
    if n < 0 or [f.get("id") if isinstance(f, dict) else None for f in faces] != [f"F{t}" for t in range(n)]:
        problems.append("faces must be exactly F0..F{n-1}, unique")
    else:
        for f in faces:
            problems += _face_problems(f, hinge_ids, edge_ids, tops | bottoms)
    if not isinstance(caps, list) or \
            [(c.get("id"), c.get("rim")) if isinstance(c, dict) else None for c in caps] != \
            [("C_TOP", "top"), ("C_BOTTOM", "bottom")]:
        problems.append("caps must be exactly [C_TOP (top), C_BOTTOM (bottom)]")
    else:
        for c in caps:
            if set(c) != {"id", "rim", "boundary", "boundary_edges", "plane"} or not isinstance(c["boundary"], list) \
                    or not isinstance(c["boundary_edges"], list) or not set(c["boundary"]) <= tops | bottoms \
                    or not set(c["boundary_edges"]) <= edge_ids or not _int_list(c["plane"], 4):
                problems.append(f"{c['id']}: malformed field or undeclared reference")
    return not problems, {"schema": p.get("schema"), "problems": problems}


# ------------------------------------------------------------------ source checks

def _rims(payload):
    return {rim: [_pt(p) for p in payload["normalized"][rim]] for rim in ("top", "bottom")}


def _height_positive(p):
    h = Fraction(p["normalized"]["height"])
    given = parse_exact(p["input"]["height"])
    return h > 0 and h == given, {"height": format_exact(h), "matches_input": h == given}


def _rims_convex(p):
    rims = _rims(p)
    detail = {rim: {"vertices": len(r), "strictly_convex_clockwise": _strictly_convex_clockwise(r),
                    "starts_at_minimum": bool(r) and r[0] == min(r)} for rim, r in rims.items()}
    return all(d["strictly_convex_clockwise"] and d["starts_at_minimum"] for d in detail.values()), detail


def _accounts(p):
    kind = p["input"]["input_kind"]
    rims = _rims(p)
    detail = {}
    for rim, norm in rims.items():
        raw = [_pt(q) for q in p["input"][rim]]
        d = p["normalization"][rim]
        problems = []
        if d.get("input_kind") != kind or d.get("input_count") != len(raw):
            problems.append("input kind/count not recorded correctly")
        if kind == "cyclic_boundary":
            n = len(raw)
            rotations = [raw[k:] + raw[:k] for k in range(n)]
            rev = raw[::-1]
            rev_rotations = [rev[k:] + rev[:k] for k in range(n)]
            forward, backward = norm in rotations, norm in rev_rotations
            if not (forward or backward):
                problems.append("normalized ring is not a rotation or reversal of the input ring")
            if d.get("reversed") is not (backward and not forward):
                problems.append("reversed flag inconsistent")
            expected_orientation = "counterclockwise" if d.get("reversed") else "clockwise"
            if d.get("input_orientation") != expected_orientation:
                problems.append("input_orientation inconsistent")
            k = d.get("start_input_index")
            if type(k) is not int or not 0 <= k < n or raw[k] != norm[0]:
                problems.append("start_input_index does not name the canonical start")
            if d.get("removed") != []:
                problems.append("cyclic input must remove nothing")
        elif kind == "point_set_hull":
            distinct = list(dict.fromkeys(raw))
            extreme = set(_extreme_points(distinct))
            if set(norm) != extreme or len(norm) != len(extreme):
                problems.append("normalized ring is not exactly the extreme points of the input")
            if d.get("hull_vertex_count") != len(norm):
                problems.append("hull_vertex_count wrong")
            m, seen, expected = len(norm), set(), []
            for i, q in enumerate(raw):
                if q in seen:
                    reason = "duplicate"
                elif q in extreme:
                    reason = None
                elif any(_between(q, norm[j], norm[(j + 1) % m]) for j in range(m)):
                    reason = "boundary_non_vertex"
                else:
                    reason = "interior"
                seen.add(q)
                if reason:
                    expected.append({"input_index": i, "point": [format_exact(q[0]), format_exact(q[1])],
                                     "reason": reason})
            if d.get("removed") != expected:
                problems.append("removed points/reasons do not match an independent classification")
        else:
            problems.append(f"unknown input_kind {kind!r}")
        detail[rim] = problems
    return all(not v for v in detail.values()), {"input_kind": kind, "problems": detail}


SOURCE_CLAIMS = ("two_rim.source.record_schema", "two_rim.source.height_positive",
                 "two_rim.source.rims_strictly_convex_clockwise", "two_rim.source.normalization_accounts_for_input")


def check_source(state, params):
    p = state["payload"]
    schema = _guarded(SOURCE_CLAIMS[0], lambda: _source_schema(p))
    if schema.outcome != "pass":
        return [schema] + [_unknown(c, "source record schema invalid") for c in SOURCE_CLAIMS[1:]]
    return [schema,
            _guarded(SOURCE_CLAIMS[1], lambda: _height_positive(p)),
            _guarded(SOURCE_CLAIMS[2], lambda: _rims_convex(p)),
            _guarded(SOURCE_CLAIMS[3], lambda: _accounts(p))]


# ------------------------------------------------------------------ material checks

def _sub3(a, b):
    return tuple(x - y for x, y in zip(a, b))


def _dot3(a, b):
    return sum((x * y for x, y in zip(a, b)), Fraction(0))


def _cross3(u, v):
    return (u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0])


def _primitive_plane(n, d):
    vals = [Fraction(x) for x in (*n, d)]
    den = 1
    for v in vals:
        den = den * v.denominator // gcd(den, v.denominator)
    ints = [int(v * den) for v in vals]
    g = 0
    for v in ints:
        g = gcd(g, abs(v))
    return tuple(v // g for v in ints)


def supporting_planes(points: dict) -> dict:
    """{primitive (a,b,c,d) with a x + b y + c z <= d on all points: frozenset(ids on the plane)}."""
    ids = sorted(points)
    out = {}
    for a, b, c in combinations(ids, 3):
        n = _cross3(_sub3(points[b], points[a]), _sub3(points[c], points[a]))
        if n == (0, 0, 0):
            continue
        d = _dot3(n, points[a])
        vals = [_dot3(n, points[q]) - d for q in ids]
        if all(v <= 0 for v in vals):
            plane = _primitive_plane(n, d)
        elif all(v >= 0 for v in vals):
            plane = _primitive_plane(tuple(-x for x in n), -d)
        else:
            continue
        out[plane] = frozenset(q for q, v in zip(ids, vals) if v == 0)
    return out


def _xyz(payload):
    return {v["id"]: tuple(Fraction(c) for c in v["xyz"]) for v in payload["vertices"]}


def _identity(p):
    recomputed = content_hash({k: v for k, v in p.items() if k != "identity"})
    return recomputed == p["identity"], {"recorded": p["identity"], "recomputed": recomputed}


def _oracle(p):
    pts = _xyz(p)
    planes = supporting_planes(pts)
    lateral = {vs: pl for pl, vs in planes.items() if (pl[0], pl[1]) != (0, 0)}
    horizontal = {vs: pl for pl, vs in planes.items() if (pl[0], pl[1]) == (0, 0)}
    problems = []
    stored = [(f["id"], frozenset(f["boundary"]), tuple(f["plane"]), f) for f in p["faces"]]
    if len({s[1] for s in stored}) != len(stored):
        problems.append("duplicate face vertex sets")
    for fid, vs, plane, f in stored:
        if vs not in lateral:
            problems.append(f"{fid}: vertex set is not an original maximal lateral facet")
        elif lateral[vs] != plane:
            problems.append(f"{fid}: stored plane {list(plane)} != oracle {list(lateral[vs])}")
        if f["shape"] != ("triangle" if len(f["boundary"]) == 3 else "trapezoid") or len(f["boundary"]) not in (3, 4):
            problems.append(f"{fid}: shape label inconsistent with its ring")
        u = f["outward_ray"]
        if not (u[0] * plane[1] - u[1] * plane[0] == 0 and u[0] * plane[0] + u[1] * plane[1] > 0):
            problems.append(f"{fid}: outward_ray is not the positive horizontal direction of its plane")
    missing = [sorted(vs) for vs in lateral if vs not in {s[1] for s in stored}]
    if missing:
        problems.append(f"oracle lateral facets missing from material: {missing}")
    caps = {frozenset(c["boundary"]): tuple(c["plane"]) for c in p["caps"]}
    if caps != horizontal:
        problems.append("caps differ from the oracle's horizontal facets")
    return not problems, {"oracle_lateral_facets": len(lateral), "stored_faces": len(stored),
                          "oracle_caps": len(horizontal), "problems": problems}


def _incidence(p):
    problems = []
    pts = _xyz(p)
    h = Fraction(p["height"])
    ids = [v["id"] for v in p["vertices"]]
    if len(set(ids)) != len(ids):
        problems.append("duplicate vertex ids")
    rim = {v["id"]: v["rim"] for v in p["vertices"]}
    for v in p["vertices"]:
        if (v["rim"], v["id"][0]) not in (("top", "A"), ("bottom", "B")) or pts[v["id"]][2] != (h if v["rim"] == "top" else 0):
            problems.append(f"{v['id']}: rim label, prefix or height inconsistent")
    hinges = {e["id"]: e for e in p["hinges"]}
    for e in p["hinges"]:
        if rim.get(e["lower"]) != "bottom" or rim.get(e["upper"]) != "top":
            problems.append(f"{e['id']}: must join a bottom vertex (lower) to a top vertex (upper)")
    on_hinge = {e["lower"] for e in p["hinges"]} | {e["upper"] for e in p["hinges"]}
    if on_hinge != set(ids):
        problems.append(f"vertices on no hinge: {sorted(set(ids) - on_hinge)}")
    ends = {eid: {e["lower"], e["upper"]} for eid, e in hinges.items()}
    ends.update({r["id"]: set(r["ends"]) for r in p["rim_edges"]})
    faces = p["faces"]
    n = len(faces)
    if sorted(f["entry"] for f in faces) != sorted(hinges):
        problems.append("face entries are not each hinge exactly once")
    orientation = set()
    for t, f in enumerate(faces):
        nxt = faces[(t + 1) % n]
        if f["exit"] != nxt["entry"]:
            problems.append(f"{f['id']}: exit is not the next face's entry")
            continue
        a, b = hinges[f["entry"]], hinges[f["exit"]]
        # Ring starts at the entry hinge's lower vertex; a vanished run drops the SECOND copy.
        ring = [a["lower"], a["upper"]]
        if b["upper"] != a["upper"]:
            ring.append(b["upper"])
        if b["lower"] != a["lower"]:
            ring.append(b["lower"])
        if ring != f["boundary"]:
            problems.append(f"{f['id']}: boundary is not the entry/exit hinge ring")
        for k, eid in enumerate(f["boundary_edges"]):
            if ends.get(eid) != {f["boundary"][k], f["boundary"][(k + 1) % len(f["boundary"])]}:
                problems.append(f"{f['id']}: boundary edge {eid} does not join its ring vertices")
        if len(f["boundary_edges"]) != len(f["boundary"]):
            problems.append(f"{f['id']}: boundary_edges length differs from ring")
        if set(f["boundary"]) & set(nxt["boundary"]) != ends[f["exit"]]:
            problems.append(f"{f['id']}: shares more or less than its exit hinge with the next face")
        normal = tuple(Fraction(x) for x in f["plane"][:3])
        r3 = [pts[v] for v in f["boundary"]]
        signs = {(s > 0) - (s < 0) for s in
                 (_dot3(normal, _cross3(_sub3(r3[(k + 1) % len(r3)], r3[k]),
                                        _sub3(r3[(k + 2) % len(r3)], r3[(k + 1) % len(r3)])))
                  for k in range(len(r3)))}
        if len(signs) != 1 or 0 in signs:
            problems.append(f"{f['id']}: ring is not strictly convex in its plane")
        orientation |= signs
    if len(orientation) != 1:
        problems.append("lateral rings are not consistently oriented about their outward normals")
    for c in p["caps"]:
        prefix = "A" if c["rim"] == "top" else "B"
        order = [v["id"] for v in p["vertices"] if v["rim"] == c["rim"]]
        if c["boundary"] != order:
            problems.append(f"{c['id']}: boundary must be its rim in canonical clockwise source order {order}")
        if c["boundary_edges"] != [f"R{prefix}{i}" for i in range(len(order))]:
            problems.append(f"{c['id']}: boundary_edges must be R{prefix}0.. aligned with the ring")
        ring = c["boundary"]
        for k, eid in enumerate(c["boundary_edges"]):
            if ends.get(eid) != {ring[k % len(ring)], ring[(k + 1) % len(ring)]}:
                problems.append(f"{c['id']}: boundary edge {eid} does not join consecutive ring vertices")
        if not _strictly_convex_clockwise([pts[v][:2] for v in ring if v in pts]):
            problems.append(f"{c['id']}: ring is not a strictly convex clockwise rim path")
    for r in p["rim_edges"]:
        lateral_uses = sum(r["id"] in f["boundary_edges"] for f in faces)
        cap_uses = sum(r["id"] in c["boundary_edges"] and c["rim"] == r["rim"] for c in p["caps"])
        if lateral_uses != 1 or cap_uses != 1:
            problems.append(f"{r['id']}: on {lateral_uses} lateral faces and {cap_uses} caps (expected 1 and 1)")
    return not problems, {"faces": n, "hinges": len(hinges), "vertices": len(ids),
                          "ring_orientation_about_outward_normal": sorted(orientation), "problems": problems}


def _correspondence(state, context):
    """The material represents its actual immediate two_rim.source parent (independent comparison)."""
    parent_hash = state.get("parent")
    if parent_hash is None:
        return False, {"parent": None, "problems": ["no parent source: the material is a root state"]}
    parent = context.get(parent_hash)  # within the closure by construction; ContextError propagates
    if parent["kind"] != "two_rim.source":
        return False, {"parent": parent_hash, "problems": [f"parent kind {parent['kind']!r} is not two_rim.source"]}
    ok, rec = _source_schema(parent["payload"])
    if not ok:
        return False, {"parent": parent_hash, "problems": ["parent source record schema invalid", rec]}
    src, mat = parent["payload"], state["payload"]
    problems = [f"{k} differs from the source" for k in ("units", "coordinate_convention", "number_domain")
                if mat[k] != src[k]]
    h = Fraction(src["normalized"]["height"])
    if Fraction(mat["height"]) != h:
        problems.append(f"height {mat['height']} != source height {src['normalized']['height']}")
    for rim, prefix, z in (("top", "A", h), ("bottom", "B", Fraction(0))):
        verts = [v for v in mat["vertices"] if v["rim"] == rim]
        ring = [_pt(q) for q in src["normalized"][rim]]
        if len(verts) != len(ring):
            problems.append(f"{rim}: {len(verts)} material vertices vs {len(ring)} source vertices")
            continue
        for i, (v, q) in enumerate(zip(verts, ring)):
            xyz = tuple(Fraction(c) for c in v["xyz"])
            if v["id"] != f"{prefix}{i}" or xyz != (q[0], q[1], z):
                problems.append(f"{v['id']}: {v['xyz']} does not match source {rim}[{i}] at z = {format_exact(z)}")
    planes = {c["id"]: c["plane"] for c in mat["caps"]}
    if planes.get("C_TOP") != [0, 0, h.denominator, h.numerator] or planes.get("C_BOTTOM") != [0, 0, -1, 0]:
        problems.append("cap planes do not match the source height")
    return not problems, {"parent": parent_hash, "problems": problems}


MATERIAL_CLAIMS = ("two_rim.material.record_schema", "two_rim.material.identity_hash",
                   "two_rim.material.facets_match_supporting_plane_oracle", "two_rim.material.incidence_and_rings",
                   "two_rim.material.matches_parent_source")


def check_material(state, params, context=None):
    """Declared contextual checker (v2). Without a context, correspondence is `unknown`, never `pass`."""
    p = state["payload"]
    schema = _guarded(MATERIAL_CLAIMS[0], lambda: _material_schema(p))
    if schema.outcome != "pass":
        return [schema] + [_unknown(c, "material record schema invalid") for c in MATERIAL_CLAIMS[1:]]
    claims = [schema,
              _guarded(MATERIAL_CLAIMS[1], lambda: _identity(p)),
              _guarded(MATERIAL_CLAIMS[2], lambda: _oracle(p)),
              _guarded(MATERIAL_CLAIMS[3], lambda: _incidence(p))]
    if context is None:
        claims.append(_unknown(MATERIAL_CLAIMS[4], "no dependency context supplied; correspondence not evaluated"))
    else:
        claims.append(_guarded(MATERIAL_CLAIMS[4], lambda: _correspondence(state, context)))
    return claims


def register_checkers(registry) -> None:
    """v2 only: the claim sets changed in the D01-D03 repair; v1 is not registered."""
    registry.register_checker(CheckerSpec("two_rim.check.source", 2, "two_rim.source", {}, CHECKER_REVISION,
                                          check_source))
    registry.register_checker(CheckerSpec("two_rim.check.material", 2, "two_rim.material", {}, CHECKER_REVISION,
                                          check_material, uses_context=True))
