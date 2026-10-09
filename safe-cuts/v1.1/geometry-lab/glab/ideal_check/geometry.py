"""Checker-side geometry of the ideal trimmed development D: exact model, Theorem S, enclosures, certificates.

Package glab.ideal_check (checker side of the ideal lane). Standard library only: exact parsing from glab.core.numbers
and intervals from glab.rigorous.ratint. It never imports the generator package (two_rim) and never reads a float
state. (It lives outside glab/check because the inherited boundary tests keep every glab/check module to the
standard library and glab.core; this package additionally uses the shared arithmetic in glab.rigorous.)

Provenance (Stage 4B port of the accepted Stage 4A prototype; a test compares the ASTs):
- unchanged from probes/stage4a/ideal.py, Git blob de3cae44: sub, dot, cross, FrozenDict, freeze, thaw,
  ExactModel, model_from_payloads, face_checks, _face_ok, shared_hinge_decision, enclose;
- unchanged from probes/stage4a/classify.py, Git blob c82b5873: SCHEDULE, _mid, _dot, _signed_area2,
  certify_separation, _clip, certify_witness, point_in_both, decide_boxes, _Enclosures, classify_pair, seam_total,
  to_json;
- adapted: classify_seam (no isolated-prototype label);
- new: local_premises (the exact premises, coded like the re-checker's R02) and verify_certificate (the
  issuance-time self-check of every reported bound, R01 rules).
Not ported: Subject, load_subject, binding and anything that reads a Run; the registered checker reads its
ancestors through the core's DependencyContext instead. The written mathematics is IDEAL-DEVELOPMENT-CONTRACT.md.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations

from ..core.numbers import ExactInputError, format_exact, parse_exact
from ..rigorous.ratint import Interval, IntervalError, rsqrt, sqrt_enclosure

__all__ = ["sub", "dot", "cross", "FrozenDict", "freeze", "thaw", "ExactModel", "model_from_payloads",
           "face_checks", "shared_hinge_decision", "enclose", "SCHEDULE", "certify_separation", "certify_witness",
           "point_in_both", "decide_boxes", "classify_pair", "seam_total", "classify_seam", "to_json",
           "PREMISE_CODES", "local_premises", "verify_certificate"]


# ------------------------------------------------------------------ from ideal.py (unchanged)

def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def dot(a, b):
    return sum((x * y for x, y in zip(a, b)), Fraction(0))


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])


class FrozenDict(dict):
    """A dict that refuses mutation after construction; still a dict, so it serializes as JSON."""
    __slots__ = ()

    def _refuse(self, *args, **kwargs):
        raise TypeError("FrozenDict is immutable")

    __setitem__ = __delitem__ = _refuse
    clear = pop = popitem = setdefault = update = _refuse

    def __ior__(self, other):
        raise TypeError("FrozenDict is immutable")

    def __reduce__(self):
        return (FrozenDict, (dict(self),))


def freeze(x):
    if isinstance(x, dict):
        return FrozenDict({k: freeze(v) for k, v in x.items()})
    if isinstance(x, (list, tuple)):
        return tuple(freeze(v) for v in x)
    return x


def thaw(x):
    """Plain JSON-shaped copy (dict, list, str, int, Fraction kept)."""
    if isinstance(x, dict):
        return {k: thaw(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [thaw(v) for v in x]
    return x


@dataclass(frozen=True)
class ExactModel:
    vertices: FrozenDict    # id -> (x, y, z) Fractions
    faces: FrozenDict       # id -> FrozenDict {"id","entry","exit","boundary","normal","offset"}
    hinges: FrozenDict      # id -> (lower id, upper id)
    chain: tuple
    seam: str
    delta: Fraction
    trim: FrozenDict        # "E@lo"/"E@hi" -> xyz
    rings: FrozenDict       # face -> trimmed ring labels

    def hinge_points(self, hinge):
        lo, hi = self.hinges[hinge]
        return self.vertices[lo], self.vertices[hi]


def model_from_payloads(material: dict, cut: dict, delta) -> ExactModel:
    """Low-level constructor (synthetic experiments allowed); certificates re-check the domain and preconditions."""
    d = parse_exact(delta)
    vertices = {v["id"]: tuple(Fraction(c) for c in v["xyz"]) for v in material["vertices"]}
    faces = {f["id"]: {"id": f["id"], "entry": f["entry"], "exit": f["exit"], "boundary": tuple(f["boundary"]),
                       "normal": tuple(Fraction(c) for c in f["plane"][:3]), "offset": Fraction(f["plane"][3])}
             for f in material["faces"]}
    hinges = {e["id"]: (e["lower"], e["upper"]) for e in material["hinges"]}
    trim = {}
    for h, (lo, hi) in hinges.items():
        L, U = vertices[lo], vertices[hi]
        trim[f"{h}@lo"] = tuple(a + d * (b - a) for a, b in zip(L, U))
        trim[f"{h}@hi"] = tuple(a + (1 - d) * (b - a) for a, b in zip(L, U))
    rings = {fid: (f"{f['entry']}@lo", f"{f['entry']}@hi", f"{f['exit']}@hi", f"{f['exit']}@lo")
             for fid, f in faces.items()}
    return ExactModel(freeze(vertices), freeze(faces), freeze(hinges), tuple(cut["face_order"]), cut["seam"], d,
                      freeze(trim), freeze(rings))


def face_checks(model: ExactModel) -> dict:
    out = {}
    for fid, f in model.faces.items():
        n = f["normal"]
        planar = all(dot(n, model.vertices[v]) == f["offset"] for v in f["boundary"])
        hinges_in_plane = all(dot(n, sub(*reversed(model.hinge_points(h)))) == 0 for h in (f["entry"], f["exit"]))
        ring = [model.trim[k] for k in model.rings[fid]]
        turns = [dot(cross(sub(ring[(i + 1) % 4], ring[i]), sub(ring[(i + 2) % 4], ring[(i + 1) % 4])), n)
                 for i in range(4)]
        out[fid] = {"planar": planar, "hinges_in_plane": hinges_in_plane, "nonzero_normal": any(n),
                    "trimmed_ring_convex_counterclockwise": all(t > 0 for t in turns),
                    "turns": [str(t) for t in turns]}
    return out


def _face_ok(check):
    return check["planar"] and check["hinges_in_plane"] and check["nonzero_normal"] and \
        check["trimmed_ring_convex_counterclockwise"]


def shared_hinge_decision(model: ExactModel, a: str, b: str, hinge: str) -> dict:
    """Theorem S of the design: pass iff S1-S4 hold exactly; otherwise unknown with the failed preconditions."""
    row = {"pair": [a, b], "hinge": hinge, "method": "shared_hinge_exact", "problems": []}
    p = row["problems"]
    fa, fb = model.faces.get(a), model.faces.get(b)
    if fa is None or fb is None or hinge not in model.hinges:
        p.append("unknown face or hinge")
        return dict(row, outcome="unknown", reason="shared_hinge_preconditions_failed")
    # S1 identity: chain position, hinge roles, seam, endpoint IDs in both material rings.
    pos = {f: i for i, f in enumerate(model.chain)}
    if a not in pos or b not in pos or pos[b] != pos[a] + 1:
        p.append("faces are not consecutive in the cut's chain order")
    if hinge == model.seam:
        p.append("the seam is cut in D; it is not a retained hinge")
    if fa["exit"] != hinge or fb["entry"] != hinge:
        p.append("hinge is not the exit of the first face and the entry of the second")
    lo_id, hi_id = model.hinges[hinge]
    for f in (fa, fb):
        if lo_id not in f["boundary"] or hi_id not in f["boundary"]:
            p.append(f"{f['id']} ring lacks the hinge endpoint IDs {lo_id}, {hi_id}")
    for f, labels in ((fa, model.rings[a][2:]), (fb, model.rings[b][:2])):
        if sorted(labels) != sorted([f"{hinge}@lo", f"{hinge}@hi"]):
            p.append(f"{f['id']} trimmed ring does not use {hinge}'s trim points")
    L, U = model.hinge_points(hinge)
    e = sub(U, L)
    # S2 nondegeneracy, S3 planarity (exact).
    if not any(e):
        p.append("degenerate hinge (L = U)")
    for f in (fa, fb):
        n = f["normal"]
        if not any(n):
            p.append(f"{f['id']} has a zero normal")
        if not all(dot(n, model.vertices[v]) == f["offset"] for v in f["boundary"]):
            p.append(f"{f['id']} ring is not planar on its recorded plane")
        if dot(n, e) != 0:
            p.append(f"hinge {hinge} is not in the plane of {f['id']}")
    if p:
        return dict(row, outcome="unknown", reason="shared_hinge_preconditions_failed")
    # S4 exact side values of every trimmed-ring vertex.
    sig = {}
    for f in (fa, fb):
        sig[f["id"]] = {k: dot(cross(e, sub(model.trim[k], L)), f["normal"]) for k in model.rings[f["id"]]}
    row["sigma"] = {f: {k: str(v) for k, v in vals.items()} for f, vals in sig.items()}

    def side(vals):
        if all(v <= 0 for v in vals) and any(v < 0 for v in vals):
            return -1
        if all(v >= 0 for v in vals) and any(v > 0 for v in vals):
            return 1
        return 0
    sa, sb = side(sig[a].values()), side(sig[b].values())
    row["sides"] = {a: sa, b: sb}
    if sa == 0 or sb == 0 or sa == sb:
        p.append("side values are not on opposite closed sides of the shared hinge")
        return dict(row, outcome="unknown", reason="shared_hinge_preconditions_failed")
    return dict(row, outcome="pass",
                reason="opposite closed half-planes of the one shared planar hinge line (Theorem S); "
                       "conditional on the design's lemmas (O1)")


def enclose(model: ExactModel, bits: int) -> dict:
    """Interval boxes of Phi_t(trimmed ring vertices) for every chain face; raises IntervalError on refusal.

    Rounding policy (refinement of design 5.2, found by the square-prism target): exact (zero-width)
    intermediate values are kept exact; only intervals that already have width are rounded outward to
    multiples of 2^-bits. Both choices preserve containment; this one keeps exact specimens exact.
    """
    records = []

    def rnd(iv):
        return iv if iv.lo == iv.hi else iv.rounded(bits)

    def rs(a):
        iv, rec = rsqrt(a, bits)
        records.append(rec)
        return rnd(iv)

    C, S = Interval.exact(1), Interval.exact(0)
    O = None
    boxes = {}
    chain = model.chain
    for idx, t in enumerate(chain):
        f = model.faces[t]
        L, U = model.hinge_points(f["entry"])
        e, n = sub(U, L), f["normal"]
        ee = dot(e, e)
        r_e = rs(ee)                      # 1/|e|
        r_ne = rs(dot(n, n) * ee)          # 1/(|n||e|)
        ne = cross(n, e)
        if idx == 0:
            root_e, rec = sqrt_enclosure(ee, bits)
            records.append(rec)
            O = (rnd(-(model.delta * root_e)), Interval.exact(0))

        def phi(x, O=O, C=C, S=S, L=L, e=e, ne=ne, r_e=r_e, r_ne=r_ne):
            v = sub(x, L)
            a = rnd(dot(e, v) * r_e)
            b = rnd(dot(ne, v) * r_ne)
            return (rnd(O[0] + C * a - S * b), rnd(O[1] + S * a + C * b))
        boxes[t] = [phi(model.trim[k]) for k in model.rings[t]]
        if idx + 1 < len(chain):
            nxt = model.faces[chain[idx + 1]]
            if nxt["entry"] != f["exit"]:
                raise IntervalError("unsupported_input", f"{t} exit {f['exit']} != {nxt['id']} entry {nxt['entry']}")
            L2, U2 = model.hinge_points(nxt["entry"])
            e2 = sub(U2, L2)
            r_e2 = rs(dot(e2, e2))
            c = rnd(dot(e, e2) * r_e * r_e2)
            s = rnd(dot(n, cross(e, e2)) * r_ne * r_e2)
            O = phi(L2)
            C, S = rnd(C * c - S * s), rnd(S * c + C * s)
    return {"bits": bits, "boxes": boxes, "sqrt_records": records}


# ------------------------------------------------------------------ from classify.py (unchanged)

SCHEDULE = (16, 32, 64, 128, 256, 512)


def _mid(poly):
    return [(x.mid(), y.mid()) for x, y in poly]


def _dot(d, v):
    return v[0] * d[0] + v[1] * d[1]


def _signed_area2(pts):
    return sum(pts[i][0] * pts[(i + 1) % len(pts)][1] - pts[i][1] * pts[(i + 1) % len(pts)][0]
               for i in range(len(pts)))


def certify_separation(P, Q):
    """Best certified axis (exact rational d) with max sup(d.P) <= min inf(d.Q), or symmetric; else None."""
    Pm, Qm = _mid(P), _mid(Q)
    cands = []
    for poly in (Pm, Qm):
        k = len(poly)
        for i in range(k):
            dx, dy = poly[(i + 1) % k][0] - poly[i][0], poly[(i + 1) % k][1] - poly[i][1]
            if dx or dy:
                cands.append((-dy, dx))
    cP = (sum(p[0] for p in Pm) / len(Pm), sum(p[1] for p in Pm) / len(Pm))
    cQ = (sum(p[0] for p in Qm) / len(Qm), sum(p[1] for p in Qm) / len(Qm))
    if cP != cQ:
        cands.append((cQ[0] - cP[0], cQ[1] - cP[1]))
    best = None
    for d in cands:
        pp, qq = [_dot(d, v) for v in P], [_dot(d, v) for v in Q]
        for gap, order in ((min(q.lo for q in qq) - max(p.hi for p in pp), "P_below_Q"),
                           (min(p.lo for p in pp) - max(q.hi for q in qq), "Q_below_P")):
            if gap >= 0:
                norm_hi = sqrt_enclosure(d[0] * d[0] + d[1] * d[1], 64)[0].hi
                euclid = gap / norm_hi
                if best is None or euclid > best["euclidean_gap_lower_bound"]:
                    best = {"method": "separating_axis", "axis": d, "order": order, "axis_gap": gap,
                            "euclidean_gap_lower_bound": euclid}
    return best


def _clip(subject, clipper):
    """Sutherland-Hodgman on exact rational points (both counterclockwise); a proposal only."""
    out = list(subject)
    k = len(clipper)
    for i in range(k):
        a, b = clipper[i], clipper[(i + 1) % k]
        inp, out = out, []

        def side(p):
            return (b[0] - a[0]) * (p[1] - a[1]) - (b[1] - a[1]) * (p[0] - a[0])
        for j in range(len(inp)):
            cur, prev = inp[j], inp[j - 1]
            sc, sp = side(cur), side(prev)
            if sc >= 0:
                if sp < 0:
                    t = sp / (sp - sc)
                    out.append((prev[0] + t * (cur[0] - prev[0]), prev[1] + t * (cur[1] - prev[1])))
                out.append(cur)
            elif sp >= 0:
                t = sp / (sp - sc)
                out.append((prev[0] + t * (cur[0] - prev[0]), prev[1] + t * (cur[1] - prev[1])))
        if not out:
            return []
    return out


def certify_witness(P, Q):
    """A rational point certified strictly inside both (counterclockwise, strictly convex) polygons; else None."""
    Pm, Qm = _mid(P), _mid(Q)
    if _signed_area2(Pm) <= 0 or _signed_area2(Qm) <= 0:
        return None
    region = _clip(Pm, Qm)
    if len(region) < 3:
        return None
    # Exact centroid of the proposal region (no coarsening: a thin overlap must not be rounded onto an edge).
    y = (sum(p[0] for p in region) / len(region), sum(p[1] for p in region) / len(region))
    margin = point_in_both(P, Q, y)
    return None if margin is None else {"method": "interior_witness", "witness": y, "cross_lower_bound": margin}


def point_in_both(P, Q, y):
    """Smallest certified lower bound of cross2(v_{i+1}-v_i, y-v_i) over both counterclockwise polygons, or None.

    A positive result certifies y strictly inside both (given exact strict convexity and orientation)."""
    margins = []
    for poly in (P, Q):
        k = len(poly)
        for i in range(k):
            ex, ey = poly[(i + 1) % k][0] - poly[i][0], poly[(i + 1) % k][1] - poly[i][1]
            wx, wy = Interval.exact(y[0]) - poly[i][0], Interval.exact(y[1]) - poly[i][1]
            cr = ex * wy - ey * wx
            if cr.lo <= 0:
                return None
            margins.append(cr.lo)
    return min(margins)


def decide_boxes(P, Q, orientation_certified: bool):
    """(outcome, detail) for one pair of enclosed convex polygons."""
    sep = certify_separation(P, Q)
    wit = certify_witness(P, Q) if orientation_certified else None
    if sep and wit:
        raise AssertionError("both a separating axis and an interior witness certified: implementation error")
    if sep:
        return "pass", sep
    if wit:
        return "fail", wit
    reason = "no_certified_axis_or_witness"
    if not orientation_certified:
        reason += "; witness not attempted (ring convexity/orientation not certified exactly)"
    return "unknown", {"reason": reason}


class _Enclosures:
    def __init__(self, model):
        self.model, self.cache = model, {}

    def get(self, bits):
        if bits not in self.cache:
            try:
                self.cache[bits] = ("ok", enclose(self.model, bits))
            except IntervalError as exc:
                self.cache[bits] = ("error", f"{exc.kind}: {exc.detail}")
        return self.cache[bits]


def classify_pair(model, a, b, schedule=SCHEDULE, encl=None, checks=None, try_shared=True):
    """One pair row. Consecutive faces try Theorem S first; intervals otherwise or on refusal."""
    encl = encl or _Enclosures(model)
    checks = checks or face_checks(model)
    pos = {f: i for i, f in enumerate(model.chain)}
    row = {"pair": [a, b], "positions": [pos[a], pos[b]]}
    if try_shared and pos[b] == pos[a] + 1:
        sh = shared_hinge_decision(model, a, b, model.faces[a]["exit"])
        row["shared_hinge"] = sh
        if sh["outcome"] == "pass":
            return dict(row, outcome="pass", method="shared_hinge_exact")
    oriented = _face_ok(checks[a]) and _face_ok(checks[b])
    attempts = []
    for bits in schedule:
        status, enc = encl.get(bits)
        if status == "error":
            attempts.append({"bits": bits, "outcome": "unknown", "error": enc})
            continue
        out, detail = decide_boxes(enc["boxes"][a], enc["boxes"][b], oriented)
        attempts.append({"bits": bits, "outcome": out})
        if out != "unknown":
            return dict(row, outcome=out, method=detail["method"], bits=bits, certificate=detail, attempts=attempts)
    reason = "budget_exhausted" if all("error" not in x for x in attempts) else \
        "error: " + "; ".join(sorted({x["error"] for x in attempts if "error" in x}))
    return dict(row, outcome="unknown", reason=reason, attempts=attempts)


def seam_total(rows):
    outs = {r["outcome"] for r in rows}
    return "fail" if "fail" in outs else ("pass" if outs == {"pass"} else "unknown")


def to_json(x):
    if isinstance(x, Fraction):
        return str(x)
    if isinstance(x, Interval):
        return x.to_json()
    if isinstance(x, dict):
        return {str(k): to_json(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [to_json(v) for v in x]
    return x


def classify_seam(model, schedule=SCHEDULE):
    """Every pair of the chain (Theorem S first for consecutive faces, then intervals). Adapted from the prototype:
    no isolated-prototype label. The registered checker splits the same rows into its claims instead."""
    encl, checks = _Enclosures(model), face_checks(model)
    rows = [classify_pair(model, a, b, schedule, encl, checks)
            for a, b in combinations(model.chain, 2)]
    return {"face_checks": checks, "rows": rows, "total": seam_total(rows), "pairs": len(rows),
            "shared_hinge_rows": sum(r.get("method") == "shared_hinge_exact" for r in rows),
            "enclosure_attempts": {str(b): s for b, (s, _) in sorted(encl.cache.items())}}


# ------------------------------------------------------------------ local premises (new in Stage 4B)

PREMISE_CODES = ("shape", "number_domain", "identity_ambiguous", "noncanonical_number", "reference_missing",
                 "plane_shape", "incidence", "chain", "hinge_degenerate", "normal_zero", "ring_not_on_plane",
                 "orientation_not_outward", "trimmed_ring_not_convex_ccw")


def _canonical_exact(s):
    if not isinstance(s, str):
        return False
    try:
        return format_exact(parse_exact(s)) == s
    except ExactInputError:
        return False


def local_premises(material, cut, delta) -> dict:
    """The exact local premises of D's construction and certificates, on the ACTUAL material and cut.

    Stage 4B, with the prototype's issuance preconditions (A01) and the re-checker's R02 checks as prior art:
    exact number domain and canonical coordinates; unique IDs and existing references; every hinge the entry of
    exactly one face and the exit of exactly one face, the chain re-derived from the material hinge order and the
    cut's seam and equal to the cut's face_order, each ring holding its hinge endpoints; nondegenerate hinges;
    nonzero normals; every ring vertex and hinge endpoint exactly on the stated plane; outward orientation (every
    material vertex satisfies n.v <= d); trimmed rings strictly convex and counterclockwise about n.
    delta is an exact Fraction. Returns {"ok", "problems": [{"code", "detail"}], "chain", "faces"}; a malformed
    record is a coded problem, never an exception.
    """
    problems = []

    def fail(code, detail):
        problems.append({"code": code, "detail": detail})
    out = {"ok": False, "problems": problems, "chain": None, "faces": {}}
    if not isinstance(material, dict) or not isinstance(cut, dict):
        fail("shape", "material and cut must be objects")
        return out
    if material.get("number_domain") != "exact_rational":
        fail("number_domain", f"number_domain {material.get('number_domain')!r} is not exact_rational")
    verts, faces, hinges = material.get("vertices"), material.get("faces"), material.get("hinges")
    if not all(isinstance(x, list) and x and all(isinstance(y, dict) for y in x) for x in (verts, faces, hinges)):
        fail("shape", "material vertices, faces and hinges must be nonempty lists of objects")
        return out
    for label, items in (("vertex", verts), ("face", faces), ("hinge", hinges)):
        ids = [x.get("id") for x in items]
        if any(not isinstance(i, str) for i in ids) or len(set(ids)) != len(ids):
            fail("identity_ambiguous", f"{label} IDs must be unique strings")
    if any(p["code"] == "identity_ambiguous" for p in problems):
        return out
    V = {}
    for v in verts:
        xyz = v.get("xyz")
        if isinstance(xyz, list) and len(xyz) == 3 and all(_canonical_exact(c) for c in xyz):
            V[v["id"]] = tuple(Fraction(c) for c in xyz)
        else:
            fail("noncanonical_number", f"vertex {v['id']}: coordinates must be three canonical exact strings")
    if len(V) != len(verts):
        return out
    H, Fc = {}, {}
    for e in hinges:
        if e.get("lower") in V and e.get("upper") in V:
            H[e["id"]] = (e["lower"], e["upper"])
        else:
            fail("reference_missing", f"hinge {e['id']} refers to a missing vertex")
    for f in faces:
        ring, plane = f.get("boundary"), f.get("plane")
        if f.get("entry") not in H or f.get("exit") not in H:
            fail("reference_missing", f"face {f['id']} refers to a missing hinge")
        elif not (isinstance(ring, list) and all(isinstance(x, str) and x in V for x in ring)):
            fail("reference_missing", f"face {f['id']} ring refers to a missing vertex")
        elif len(set(ring)) < 3:
            fail("incidence", f"face {f['id']} ring has fewer than three distinct vertices")
        elif not (isinstance(plane, list) and len(plane) == 4 and all(type(x) is int for x in plane)):
            fail("plane_shape", f"face {f['id']}: plane must be four integers")
        else:
            Fc[f["id"]] = f
    if len(H) != len(hinges) or len(Fc) != len(faces):
        return out
    order = [e["id"] for e in hinges]
    entries, exits = {}, {}
    for f in faces:
        entries.setdefault(f["entry"], []).append(f["id"])
        exits.setdefault(f["exit"], []).append(f["id"])
    if len(order) < 3 or any(len(entries.get(h, [])) != 1 or len(exits.get(h, [])) != 1 for h in order):
        fail("incidence", "at least three hinges, each the entry of exactly one face and the exit of exactly one face")
        return out
    seam = cut.get("seam")
    if seam not in H:
        fail("chain", f"the cut's seam {seam!r} is not a hinge of the material")
        return out
    n, k = len(order), order.index(seam)
    chain = [entries[order[(k + j) % n]][0] for j in range(n)]
    out["chain"] = chain
    for j, fid in enumerate(chain):
        if Fc[fid]["exit"] != order[(k + j + 1) % n]:
            fail("incidence", f"{fid}: exit hinge does not continue the chain opened at {seam}")
    if cut.get("face_order") != chain:
        fail("chain", "the cut's face_order is not the chain opened at its seam")
    for fid in chain:
        ring = set(Fc[fid]["boundary"])
        for h in (Fc[fid]["entry"], Fc[fid]["exit"]):
            if not set(H[h]) <= ring:
                fail("incidence", f"{fid}: ring lacks an endpoint of hinge {h}")
    if problems:
        return out
    for h, (lo, hi) in H.items():
        if V[lo] == V[hi]:
            fail("hinge_degenerate", f"hinge {h} has coincident endpoints")

    def trim(h, t):
        L, U = V[H[h][0]], V[H[h][1]]
        return tuple(a + t * (b - a) for a, b in zip(L, U))
    for fid in chain:
        f = Fc[fid]
        nrm, off = tuple(Fraction(x) for x in f["plane"][:3]), Fraction(f["plane"][3])
        if not any(nrm):
            fail("normal_zero", f"{fid}: zero plane normal")
            out["faces"][fid] = {"nonzero_normal": False}
            continue
        on_plane = set(f["boundary"]) | set(H[f["entry"]]) | set(H[f["exit"]])
        planar = all(dot(nrm, V[x]) == off for x in on_plane)
        outward = all(dot(nrm, v) <= off for v in V.values())
        r = [trim(f["entry"], delta), trim(f["entry"], 1 - delta), trim(f["exit"], 1 - delta), trim(f["exit"], delta)]
        turns = [dot(cross(sub(r[(i + 1) % 4], r[i]), sub(r[(i + 2) % 4], r[(i + 1) % 4])), nrm) for i in range(4)]
        convex = all(t > 0 for t in turns)
        if not planar:
            fail("ring_not_on_plane", f"{fid}: a ring vertex or hinge endpoint is not on the stated plane")
        if not outward:
            fail("orientation_not_outward", f"{fid}: some material vertex lies outside the stated plane")
        if not convex:
            fail("trimmed_ring_not_convex_ccw", f"{fid}: trimmed ring not strictly counterclockwise convex about n")
        out["faces"][fid] = {"nonzero_normal": True, "on_plane": planar, "outward": outward,
                             "trimmed_ring_convex_counterclockwise": convex, "turns": [str(t) for t in turns]}
    out["ok"] = not problems
    return out


# ------------------------------------------------------------------ certificate self-check (new in Stage 4B)

def verify_certificate(row, P, Q, orientation_certified) -> tuple:
    """(ok, reason): exact re-verification of a decided row's certificate on the boxes it used.

    Independent code path from the proposal functions, with the R01 rules: the separating axis is nonzero with a
    supported order, its gap is recomputed and equal to axis_gap >= 0, and euclidean_gap_lower_bound b satisfies
    b >= 0 and b^2 (d.d) <= axis_gap^2; an interior witness needs exact convexity and orientation of both rings and
    0 < cross_lower_bound <= the recomputed smallest lower bound. Rows without a certificate are not checked here.
    """
    method, cert = row.get("method"), row.get("certificate")
    if method == "separating_axis":
        d = cert["axis"]
        if d[0] == 0 and d[1] == 0:
            return False, "zero axis"

        def sup(poly):
            return max(max(d[0] * x.lo, d[0] * x.hi) + max(d[1] * y.lo, d[1] * y.hi) for x, y in poly)

        def inf(poly):
            return min(min(d[0] * x.lo, d[0] * x.hi) + min(d[1] * y.lo, d[1] * y.hi) for x, y in poly)
        if cert["order"] == "P_below_Q":
            gap = inf(Q) - sup(P)
        elif cert["order"] == "Q_below_P":
            gap = inf(P) - sup(Q)
        else:
            return False, f"unsupported order {cert['order']!r}"
        if gap < 0 or gap != cert["axis_gap"]:
            return False, "axis gap not reproduced on the recorded boxes"
        b = cert["euclidean_gap_lower_bound"]
        if b < 0 or b * b * (d[0] * d[0] + d[1] * d[1]) > gap * gap:
            return False, "euclidean_gap_lower_bound is negative or exceeds axis_gap/|d|"
        return True, ""
    if method == "interior_witness":
        if not orientation_certified:
            return False, "witness without exact convexity and orientation of both rings"
        y = cert["witness"]
        lows = []
        for poly in (P, Q):
            k = len(poly)
            for i in range(k):
                (x0, y0), (x1, y1) = poly[i], poly[(i + 1) % k]
                ex, ey = (x1.lo - x0.hi, x1.hi - x0.lo), (y1.lo - y0.hi, y1.hi - y0.lo)
                wx, wy = (y[0] - x0.hi, y[0] - x0.lo), (y[1] - y0.hi, y[1] - y0.lo)
                lows.append(min(p * q for p in ex for q in wy) - max(p * q for p in ey for q in wx))
        margin = min(lows)
        b = cert["cross_lower_bound"]
        if not (margin > 0 and Fraction(0) < b <= margin):
            return False, "cross_lower_bound is not within (0, recomputed smallest lower bound]"
        return True, ""
    return True, ""
