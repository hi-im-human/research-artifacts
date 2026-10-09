"""ISOLATED STAGE 4A PROTOTYPE: independent re-checker (standard library + mpmath iv; imports neither glab nor the probe).

Run only in a throwaway environment (never the maintained .venv):
    <throwaway-venv>/Scripts/python -I -B recheck_mpmath.py BUNDLE.json OUT.json
Exit code 0 means every seam was VERIFIED; anything else (rejection, failure, empty bundle) exits 1.

Input contract (Stage 4A repair A03), schema "stage4a.recheck_bundle/2":
 1. binding: the subject spec has exactly the expected keys and fixed definitions, its ID is the sha256 of its
    canonical JSON, the three state records hash to their keys with the right kinds and parent links, the material
    identity recomputes, the cut's seam and material copy match, delta is canonical in (0, 1/2), and the chain is
    re-derived from the material hinge order and the seam (never taken from the bundle);
 2. shape and coverage, BEFORE any geometry: boxes for exactly the chain faces, each 4 x 2 canonical [lo, hi] with
    lo <= hi; rows covering every unordered pair of chain faces exactly once, in chain order, with valid IDs; method,
    outcome and certificate shape consistent (shared hinge -> pass on a consecutive pair; separating axis -> pass with
    a nonzero rational axis and a supported order token; interior witness -> fail; no method -> unknown, counted);
 3. geometry: its own mpmath enclosure of D (a different construction) must lie inside every recorded box; Theorem S
    side values, axis gaps and witness margins are re-verified exactly;
 4. the verdict on D is recomputed from the confirmed rows and must equal the declared one.
A seam is "verified", "rejected" (binding or shape; geometry not attempted) or "failed" (geometry or verdict).
mpmath's interval support is documented as experimental; only + - * / and sqrt are used here.

Re-check repair (System review of commit-62):
 R02 before any geometric confirmation, this program independently checks the LOCAL assumptions its own construction
     uses: unambiguous vertex/face/hinge IDs and references, chain and hinge incidence, nondegenerate hinges and
     nonzero normals, every ring vertex and hinge endpoint exactly on the stated plane, outward orientation, and
     strictly counterclockwise convex clipped rings. It does NOT re-run Stage 2 source correspondence or check Run
     evidence (in-Run issuance does); the report states that scope.
 R01 the quantitative bounds that remain in a certificate are verified: a witness's cross_lower_bound must satisfy
     0 < recorded <= this program's recomputed lower bound; an axis's euclidean_gap_lower_bound b must satisfy
     b >= 0 and b^2 (d.d) <= g^2 exactly, g the verified projected gap. Every other field is verified or listed as
     an unverified diagnostic; unrecognized fields are rejected, never ignored.
 verified: true means the bundle's certificates and declared verdicts were confirmed. It is not a safety statement;
 each seam's recomputed verdict on D is.
"""
from __future__ import annotations

import hashlib
import json
import platform
import re
import sys
from fractions import Fraction as Q
from itertools import combinations

import mpmath
from mpmath import iv
from mpmath.libmp import to_rational

PREC = 400
BUNDLE_SCHEMA = "stage4a.recheck_bundle/2"
DEFINITION = "stage4a.ideal_development/1"
ORIENTATION = "outward: each face map preserves orientation with respect to that face's outward normal"
NORMALIZATION = "N0: first chain face's entry-hinge low trim point at (0, 0); that hinge along +x"
SPEC_KEYS = {"kind", "definition", "material_state", "material_identity", "source_state", "cut_state", "seam",
             "delta", "orientation", "normalization"}
STATE_KINDS = {"source_state": "two_rim.source", "material_state": "two_rim.material", "cut_state": "two_rim.cut"}
ORDERS = {"P_below_Q", "Q_below_P"}
CANON = re.compile(r"-?(0|[1-9][0-9]*)(/[1-9][0-9]*)?")
COUNTERS = ("theorem_s_rows", "theorem_s_confirmed", "coordinates_checked", "coordinates_contained", "axis_rows",
            "axis_confirmed", "witness_rows", "witness_confirmed", "unknown_rows", "rows_checked", "expected_pairs",
            "euclidean_bounds_confirmed", "witness_bounds_confirmed")
ROW_KEYS = {"pair", "positions", "method", "outcome", "certificate", "shared_hinge", "bits", "attempts", "reason"}
CERT_KEYS = {"separating_axis": {"method", "axis", "order", "axis_gap", "euclidean_gap_lower_bound"},
             "interior_witness": {"method", "witness", "cross_lower_bound"}}
SHARED_KEYS = {"pair", "hinge", "method", "outcome", "reason", "problems", "sides", "sigma"}
DIAGNOSTIC_FIELDS = ["bits", "attempts", "reason", "shared_hinge.reason", "shared_hinge (on unknown rows)"]
SCOPE = {
    "local_geometry_preconditions": "checked independently before geometry: unique IDs and references, chain and hinge "
                                    "incidence, nondegenerate hinges and normals, rings and hinges on their stated "
                                    "planes, outward orientation, strictly counterclockwise convex clipped rings",
    "stage2_source_correspondence_and_run_evidence": "not re-verified here; established at in-Run certificate issuance",
    "meaning_of_verified": "the bundle's certificates, bounds and declared verdicts were confirmed; it is not a safety "
                           "statement - each seam's recomputed verdict on D is (pass, fail, or unknown, which is never "
                           "a safety pass)",
}


def canonical_json(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False)


def chash(obj):
    return "sha256:" + hashlib.sha256(canonical_json(obj).encode("ascii")).hexdigest()


def exact_str(s):
    return isinstance(s, str) and CANON.fullmatch(s) is not None and str(Q(s)) == s


def I(q):
    q = Q(q)
    return iv.mpf(q.numerator) / iv.mpf(q.denominator)


def endpoints(x):
    a, b = x._mpi_
    (pa, qa), (pb, qb) = to_rational(a), to_rational(b)
    return Q(pa, qa), Q(pb, qb)


def sub3(a, b):
    return tuple(x - y for x, y in zip(a, b))


def dot3(a, b):
    return sum((x * y for x, y in zip(a, b)), Q(0))


def cross3(a, b):
    return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])


def ivmul(a, b):
    p = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return (min(p), max(p))


def ivsub(a, b):
    return (a[0] - b[1], a[1] - b[0])


class Data:
    """Trusted exact geometry, read from the bound material state payload (never from bundle-level copies)."""

    def __init__(self, material, delta):
        self.delta = Q(delta)
        self.v = {x["id"]: tuple(Q(c) for c in x["xyz"]) for x in material["vertices"]}
        self.faces = {f["id"]: f for f in material["faces"]}
        self.hinges = {e["id"]: (e["lower"], e["upper"]) for e in material["hinges"]}
        self.hinge_order = [e["id"] for e in material["hinges"]]
        d = self.delta
        self.lo, self.hi = {}, {}
        for h, (a, b) in self.hinges.items():
            L, U = self.v[a], self.v[b]
            self.lo[h] = tuple(x + d * (y - x) for x, y in zip(L, U))
            self.hi[h] = tuple(x + (1 - d) * (y - x) for x, y in zip(L, U))

    def chain(self, seam):
        n, k = len(self.hinge_order), self.hinge_order.index(seam)
        by_entry = {f["entry"]: f["id"] for f in self.faces.values()}
        return [by_entry[self.hinge_order[(k + j) % n]] for j in range(n)]

    def normal(self, f):
        return tuple(Q(c) for c in self.faces[f]["plane"][:3])

    def ring(self, f):
        F = self.faces[f]
        return [self.lo[F["entry"]], self.hi[F["entry"]], self.hi[F["exit"]], self.lo[F["exit"]]]

    def ring_labels(self, f):
        F = self.faces[f]
        return [f"{F['entry']}@lo", f"{F['entry']}@hi", f"{F['exit']}@hi", f"{F['exit']}@lo"]


# ------------------------------------------------------------------ geometry (unchanged arithmetic)

def theorem_s(data, chain, row):
    a, b = row["pair"]
    h = data.faces[a]["exit"]
    L, U = (data.v[x] for x in data.hinges[h])
    e = sub3(U, L)
    sig = {f: [dot3(cross3(e, sub3(w, L)), data.normal(f)) for w in data.ring(f)] for f in (a, b)}

    def side(vals):
        if all(x <= 0 for x in vals) and any(x < 0 for x in vals):
            return -1
        if all(x >= 0 for x in vals) and any(x > 0 for x in vals):
            return 1
        return 0
    sa, sb = side(sig[a]), side(sig[b])
    recorded = row["shared_hinge"]["sigma"]
    same = all([str(x) for x in sig[f]] == [recorded[f][k] for k in data.ring_labels(f)] for f in (a, b))
    return (sa * sb == -1 and same), f"sides {sa},{sb}; recorded sigma equal: {same}", {a: sa, b: sb}


def own_enclosure(data, chain):
    """Historical-style unfolding in mpmath iv; returns {face: [(x_iv, y_iv) x4]} in ring order."""
    boxes = {}
    b2 = (iv.mpf(0), iv.mpf(0))
    first = data.faces[chain[0]]["entry"]
    H0 = sub3(data.hi[first], data.lo[first])
    a2 = (iv.sqrt(I(dot3(H0, H0))), iv.mpf(0))
    for f in chain:
        F = data.faces[f]
        Bi, Ai = data.lo[F["entry"]], data.hi[F["entry"]]
        Bj, Aj = data.lo[F["exit"]], data.hi[F["exit"]]
        H = sub3(Ai, Bi)
        HH = dot3(H, H)
        lenH = iv.sqrt(I(HH))
        V = sub3(Bj, Bi)
        w = tuple(x - dot3(V, H) / HH * y for x, y in zip(V, H))        # exact Gram-Schmidt
        lenw = iv.sqrt(I(dot3(w, w)))
        s = dot3(cross3(H, V), data.normal(f))
        if s == 0:
            raise ArithmeticError(f"{f}: undecided side (exact zero)")
        sgn = 1 if s > 0 else -1
        e = ((a2[0] - b2[0]) / lenH, (a2[1] - b2[1]) / lenH)
        perp = (-sgn * e[1], sgn * e[0])

        def project(p):
            r = sub3(p, Bi)
            cu, cv = I(dot3(r, H)) / lenH, I(dot3(r, w)) / lenw
            return (b2[0] + cu * e[0] + cv * perp[0], b2[1] + cu * e[1] + cv * perp[1])
        an, bn = project(Aj), project(Bj)
        boxes[f] = [b2, a2, an, bn]
        b2, a2 = bn, an
    return boxes


def parse_box(pb):
    return [((Q(x[0]), Q(x[1])), (Q(y[0]), Q(y[1]))) for x, y in pb]


def axis_ok(P, Qb, cert):
    d = (Q(cert["axis"][0]), Q(cert["axis"][1]))

    def sup(poly):
        return max(max(d[0] * x[0], d[0] * x[1]) + max(d[1] * y[0], d[1] * y[1]) for x, y in poly)

    def inf(poly):
        return min(min(d[0] * x[0], d[0] * x[1]) + min(d[1] * y[0], d[1] * y[1]) for x, y in poly)
    gap = inf(Qb) - sup(P) if cert["order"] == "P_below_Q" else inf(P) - sup(Qb)
    return gap >= 0 and gap == Q(cert["axis_gap"]), gap


def witness_ok(data, faces, P, Qb, cert):
    y = (Q(cert["witness"][0]), Q(cert["witness"][1]))
    for f in faces:   # exact strict convexity and counterclockwise orientation about the outward normal
        r, n = data.ring(f), data.normal(f)
        if not all(dot3(cross3(sub3(r[(i + 1) % 4], r[i]), sub3(r[(i + 2) % 4], r[(i + 1) % 4])), n) > 0
                   for i in range(4)):
            return False, None
    lows = []
    for poly in (P, Qb):
        for i in range(4):
            (x0, y0), (x1, y1) = poly[i], poly[(i + 1) % 4]
            ex, ey = ivsub(x1, x0), ivsub(y1, y0)
            wx, wy = ivsub((y[0], y[0]), x0), ivsub((y[1], y[1]), y0)
            c = ivsub(ivmul(ex, wy), ivmul(ey, wx))
            lows.append(c[0])
    m = min(lows)
    return m > 0, m


# ------------------------------------------------------------------ contract checks (A03)

def _binding(bundle, seam, S, fail):
    subj = S.get("subject")
    spec = subj.get("spec") if isinstance(subj, dict) else None
    if not isinstance(spec, dict) or set(spec) != SPEC_KEYS:
        fail("subject_spec", "subject spec missing or with unexpected keys")
        return None
    if (spec["kind"], spec["definition"], spec["orientation"], spec["normalization"]) != \
            ("ideal_trimmed_development", DEFINITION, ORIENTATION, NORMALIZATION):
        fail("subject_constants", "unsupported kind, definition, orientation or normalization")
    if spec["seam"] != seam:
        fail("subject_seam", f"spec seam {spec['seam']!r} under bundle key {seam!r}")
    if chash(spec) != subj.get("id"):
        fail("subject_id", "subject ID is not the sha256 of the spec's canonical JSON")
    if not exact_str(spec["delta"]) or not Q(0) < Q(spec["delta"]) < Q(1, 2):
        fail("delta_domain", f"delta {spec['delta']!r} is not canonical in (0, 1/2)")
    states = bundle.get("states") if isinstance(bundle.get("states"), dict) else {}
    recs = {}
    for key, kind in STATE_KINDS.items():
        h, rec = spec[key], states.get(spec[key])
        if not isinstance(rec, dict):
            fail("state_missing", f"{key} {h!r} has no record")
            continue
        if chash(rec) != h:
            fail("state_hash", f"{key} record does not hash to {h}")
            continue
        if rec.get("kind") != kind:
            fail("state_kind", f"{key} has kind {rec.get('kind')!r}")
            continue
        recs[key] = rec
    if len(recs) < 3:
        return None
    mat, cut = recs["material_state"]["payload"], recs["cut_state"]["payload"]
    if recs["cut_state"]["parent"] != spec["material_state"] or recs["material_state"]["parent"] != spec["source_state"]:
        fail("parent_link", "cut -> material -> source parent links do not match the spec")
    if chash({k: v for k, v in mat.items() if k != "identity"}) != mat.get("identity") or \
            mat.get("identity") != spec["material_identity"]:
        fail("material_identity", "material identity does not recompute to the spec's material_identity")
    if cut.get("seam") != spec["seam"]:
        fail("cut_seam", "cut seam differs from the spec")
    if cut.get("material") != mat:
        fail("cut_material_copy", "cut's material copy differs from the material state")
    return spec, mat, cut


def _local_geometry(mat, cut, seam, delta, fail):
    """R02: the local assumptions this program's own construction relies on, checked with its own exact code.

    Independent of glab and of the probe. Not the Stage 2 oracle: source correspondence is out of scope here.
    """
    verts, faces, hinges = mat.get("vertices"), mat.get("faces"), mat.get("hinges")
    if not all(isinstance(x, list) and all(isinstance(y, dict) for y in x) for x in (verts, faces, hinges)):
        fail("reference_missing", "material vertices, faces and hinges must be lists of objects")
        return False
    ok = True
    for label, items in (("vertex", verts), ("face", faces), ("hinge", hinges)):
        ids = [x.get("id") for x in items]
        if any(not isinstance(i, str) for i in ids) or len(set(ids)) != len(ids):
            fail("identity_ambiguous", f"{label} IDs must be unique strings")
            ok = False
    if not ok:
        return False
    V = {}
    for v in verts:
        xyz = v.get("xyz")
        if not (isinstance(xyz, list) and len(xyz) == 3 and all(exact_str(c) for c in xyz)):
            fail("noncanonical_number", f"vertex {v['id']}: coordinates must be three canonical exact strings")
            return False
        V[v["id"]] = tuple(Q(c) for c in xyz)
    H, Fc = {}, {}
    for e in hinges:
        if e.get("lower") not in V or e.get("upper") not in V:
            fail("reference_missing", f"hinge {e['id']} refers to a missing vertex")
            ok = False
            continue
        H[e["id"]] = (e["lower"], e["upper"])
    for f in faces:
        ring, plane = f.get("boundary"), f.get("plane")
        if f.get("entry") not in H or f.get("exit") not in H:
            fail("reference_missing", f"face {f['id']} refers to a missing hinge")
            ok = False
        elif not (isinstance(ring, list) and all(x in V for x in ring)):
            fail("reference_missing", f"face {f['id']} ring refers to a missing vertex")
            ok = False
        elif len(set(ring)) < 3:
            fail("incidence", f"face {f['id']} ring has fewer than three distinct vertices")
            ok = False
        elif not (isinstance(plane, list) and len(plane) == 4 and
                  all(isinstance(x, int) and not isinstance(x, bool) for x in plane)):
            fail("plane_shape", f"face {f['id']}: plane must be four integers")
            ok = False
        else:
            Fc[f["id"]] = f
    if not ok:
        return False
    order = [e["id"] for e in hinges]
    entries, exits = {}, {}
    for f in faces:
        entries.setdefault(f["entry"], []).append(f["id"])
        exits.setdefault(f["exit"], []).append(f["id"])
    if seam not in H or any(len(entries.get(h, [])) != 1 or len(exits.get(h, [])) != 1 for h in order):
        fail("incidence", "every hinge must be the entry of exactly one face and the exit of exactly one face")
        return False
    n, k = len(order), order.index(seam)
    for j in range(n):
        fid = entries[order[(k + j) % n]][0]
        if Fc[fid]["exit"] != order[(k + j + 1) % n]:
            fail("incidence", f"{fid}: exit hinge does not continue the chain opened at {seam}")
            ok = False
    for fid, f in Fc.items():
        ring = set(f["boundary"])
        for h in (f["entry"], f["exit"]):
            if not set(H[h]) <= ring:
                fail("incidence", f"{fid}: ring lacks an endpoint of hinge {h}")
                ok = False
    if not ok:
        return False
    for h, (lo, hi) in H.items():
        if V[lo] == V[hi]:
            fail("hinge_degenerate", f"hinge {h} has coincident endpoints")
            ok = False
    d = Q(delta)
    for fid, f in Fc.items():
        nrm, off = tuple(Q(x) for x in f["plane"][:3]), Q(f["plane"][3])
        if nrm == (0, 0, 0):
            fail("normal_zero", f"{fid}: zero plane normal")
            ok = False
            continue
        on_plane = set(f["boundary"]) | set(H[f["entry"]]) | set(H[f["exit"]])
        if any(dot3(nrm, V[x]) != off for x in on_plane):
            fail("ring_not_on_plane", f"{fid}: a ring vertex or hinge endpoint is not on the stated plane")
            ok = False
        if any(dot3(nrm, V[x]) > off for x in V):
            fail("orientation_not_outward", f"{fid}: some material vertex lies outside the stated plane")
            ok = False

        def trim(h, t):
            L, U = V[H[h][0]], V[H[h][1]]
            return tuple(a + t * (b - a) for a, b in zip(L, U))
        r = [trim(f["entry"], d), trim(f["entry"], 1 - d), trim(f["exit"], 1 - d), trim(f["exit"], d)]
        turns = [dot3(cross3(sub3(r[(i + 1) % 4], r[i]), sub3(r[(i + 2) % 4], r[(i + 1) % 4])), nrm)
                 for i in range(4)]
        if not all(t > 0 for t in turns):
            fail("trimmed_ring_not_convex_ccw", f"{fid}: clipped ring not strictly counterclockwise convex")
            ok = False
    return ok


def _shape(S, chain, data, fail, counters):
    boxes = S.get("boxes")
    if not isinstance(boxes, dict):
        fail("box_shape", "boxes must be an object keyed by face")
        boxes = {}
    missing, extra = sorted(set(chain) - set(boxes)), sorted(set(boxes) - set(chain))
    if missing or extra:
        fail("box_coverage", f"missing faces {missing}, extra faces {extra}")
    for f in chain:
        verts = boxes.get(f)
        if f not in boxes:
            continue
        if not isinstance(verts, list) or len(verts) != 4:
            fail("box_shape", f"{f}: expected 4 vertex boxes, got {len(verts) if isinstance(verts, list) else '-'}")
            continue
        for k, vert in enumerate(verts):
            if not isinstance(vert, list) or len(vert) != 2 or \
                    not all(isinstance(c, list) and len(c) == 2 for c in vert):
                fail("box_shape", f"{f}[{k}]: expected [[lo, hi], [lo, hi]]")
                continue
            for c in vert:
                if not all(exact_str(x) for x in c):
                    fail("noncanonical_number", f"{f}[{k}]: interval endpoints must be canonical exact strings")
                elif Q(c[0]) > Q(c[1]):
                    fail("interval_bounds", f"{f}[{k}]: lo > hi")
    rows = S.get("rows")
    if not isinstance(rows, list):
        fail("pair_coverage", "rows must be a list")
        rows = []
    pos = {f: i for i, f in enumerate(chain)}
    seen = {}
    for idx, r in enumerate(rows):
        pair = r.get("pair") if isinstance(r, dict) else None
        if not (isinstance(pair, list) and len(pair) == 2 and all(p in pos for p in pair) and pair[0] != pair[1]):
            fail("pair_ids", f"row {idx}: pair {pair!r} is not two distinct chain faces")
            continue
        a, b = pair
        if pos[a] > pos[b]:
            fail("pair_order", f"row {idx}: pair {pair} is not in chain order")
            continue
        if (a, b) in seen:
            fail("pair_duplicate", f"row {idx}: pair {pair} appears twice")
            continue
        seen[(a, b)] = r
        m, o, cert = r.get("method"), r.get("outcome"), r.get("certificate")
        extra = sorted(set(r) - ROW_KEYS)
        if extra:
            fail("unrecognized_field", f"{a}/{b}: unrecognized row fields {extra}")
        if "positions" in r and r["positions"] != [pos[a], pos[b]]:
            fail("positions", f"{a}/{b}: recorded positions {r['positions']!r} are not the chain positions")
        if m in CERT_KEYS:
            if not isinstance(cert, dict):
                fail("axis_shape" if m == "separating_axis" else "witness_shape", f"{a}/{b}: no certificate")
                continue
            unknown_keys = sorted(set(cert) - CERT_KEYS[m])
            if unknown_keys:
                fail("unrecognized_field", f"{a}/{b}: unrecognized certificate fields {unknown_keys}")
            if cert.get("method") != m:
                fail("certificate_method", f"{a}/{b}: certificate method {cert.get('method')!r} differs from {m!r}")
        if m == "shared_hinge_exact":
            if o != "pass":
                fail("method_outcome", f"{a}/{b}: shared hinge row with outcome {o!r}")
            if pos[b] != pos[a] + 1:
                fail("shared_hinge_pair", f"{a}/{b}: shared hinge claimed for non-consecutive faces")
            sh = r.get("shared_hinge") if isinstance(r.get("shared_hinge"), dict) else {}
            sig = sh.get("sigma")
            if not (isinstance(sig, dict) and set(sig) == {a, b} and
                    all(isinstance(sig[f], dict) and set(sig[f]) == set(data.ring_labels(f)) and
                        all(exact_str(x) for x in sig[f].values()) for f in (a, b))):
                fail("sigma_shape", f"{a}/{b}: side values missing or malformed")
            extra_sh = sorted(set(sh) - SHARED_KEYS)
            if extra_sh:
                fail("unrecognized_field", f"{a}/{b}: unrecognized shared-hinge fields {extra_sh}")
            sides = sh.get("sides")
            if sh.get("pair") != [a, b] or sh.get("method") != "shared_hinge_exact" or sh.get("outcome") != "pass" \
                    or sh.get("hinge") != data.faces[a]["exit"] or sh.get("problems", []) != [] \
                    or not (isinstance(sides, dict) and set(sides) == {a, b} and
                            all(sides[f] in (-1, 1) and not isinstance(sides[f], bool) for f in (a, b))):
                fail("shared_hinge_record", f"{a}/{b}: shared-hinge record inconsistent with the row")
        elif m == "separating_axis":
            if o != "pass":
                fail("method_outcome", f"{a}/{b}: separating axis row with outcome {o!r}")
            axis = cert.get("axis")
            if not (isinstance(axis, list) and len(axis) == 2 and all(exact_str(x) for x in axis)):
                fail("noncanonical_number", f"{a}/{b}: axis must be two canonical exact strings")
            elif Q(axis[0]) == 0 and Q(axis[1]) == 0:
                fail("axis_zero", f"{a}/{b}: the zero vector is not an axis")
            if cert.get("order") not in ORDERS:
                fail("axis_order", f"{a}/{b}: unsupported order token {cert.get('order')!r}")
            if not exact_str(cert.get("axis_gap")):
                fail("noncanonical_number", f"{a}/{b}: axis_gap must be a canonical exact string")
            eb = cert.get("euclidean_gap_lower_bound")
            if "euclidean_gap_lower_bound" not in cert or eb is None:
                fail("euclidean_gap_bound_shape", f"{a}/{b}: euclidean_gap_lower_bound is required")
            elif not exact_str(eb):
                fail("noncanonical_number", f"{a}/{b}: euclidean_gap_lower_bound must be a canonical exact string")
            elif Q(eb) < 0:
                fail("euclidean_gap_bound_shape", f"{a}/{b}: euclidean_gap_lower_bound must be nonnegative")
        elif m == "interior_witness":
            if o != "fail":
                fail("method_outcome", f"{a}/{b}: interior witness row with outcome {o!r}")
            w, lb = cert.get("witness"), cert.get("cross_lower_bound")
            if not (isinstance(w, list) and len(w) == 2 and all(exact_str(x) for x in w) and exact_str(lb)
                    and Q(lb) > 0):
                fail("witness_shape", f"{a}/{b}: witness must be a rational point with a positive bound")
        elif m is None:
            if o != "unknown":
                fail("method_outcome", f"{a}/{b}: no certificate method but outcome {o!r}")
            if cert is not None:
                fail("method_outcome", f"{a}/{b}: an unknown row carries a certificate")
        else:
            fail("method_unknown", f"{a}/{b}: unsupported method {m!r}")
    expected = {(chain[i], chain[j]) for i, j in combinations(range(len(chain)), 2)}
    counters["expected_pairs"] += len(expected)
    counters["rows_checked"] += len(seen)
    lacking = expected - set(seen)
    if lacking:
        fail("pair_coverage", f"{len(lacking)} of {len(expected)} pairs have no row")
    if S.get("verdict_on_D") not in ("pass", "fail", "unknown"):
        fail("verdict_shape", f"declared verdict_on_D {S.get('verdict_on_D')!r}")
    return seen


def check_seam(bundle, seam, S, counters):
    failures = []

    def fail(code, detail):
        failures.append({"code": code, "detail": detail})
    out = {"status": "rejected", "failures": failures, "recomputed_verdict": None}
    if not isinstance(S, dict):
        fail("seam_shape", "seam entry must be an object")
        return out
    out["local_preconditions"] = "not_reached"
    bound = _binding(bundle, seam, S, fail)
    if bound is None or failures:
        return out
    spec, mat, cut = bound
    # R02: the local assumptions of this program's own construction, before any geometric confirmation.
    if not _local_geometry(mat, cut, seam, spec["delta"], fail):
        out["local_preconditions"] = "failed"
        return out
    out["local_preconditions"] = "checked"
    data = Data(mat, spec["delta"])
    if seam not in data.hinges:
        fail("subject_seam", f"{seam} is not a hinge of the bound material")
        return out
    chain = data.chain(seam)
    if cut.get("face_order") != chain:
        fail("chain", "the cut's face_order is not the chain opened at the seam")
    seen = _shape(S, chain, data, fail, counters)
    if failures:
        return out
    # ---- geometry (only after binding, shape and coverage passed)
    probe = {f: parse_box(S["boxes"][f]) for f in chain}
    mine = own_enclosure(data, chain)
    for f in chain:
        for (px, py), (mx, my) in zip(probe[f], mine[f]):
            for (plo, phi), m in ((px, mx), (py, my)):
                mlo, mhi = endpoints(m)
                counters["coordinates_checked"] += 1
                if plo <= mlo and mhi <= phi:
                    counters["coordinates_contained"] += 1
                else:
                    fail("containment", f"{f}: independent enclosure not inside the recorded box")
    confirmed = {}
    for (a, b), r in seen.items():
        m = r.get("method")
        if m == "shared_hinge_exact":
            counters["theorem_s_rows"] += 1
            ok, why, sides = theorem_s(data, chain, r)
            if not ok:
                fail("theorem_s", f"{a}/{b}: {why}")
            elif r["shared_hinge"]["sides"] != sides:
                fail("shared_hinge_record", f"{a}/{b}: recorded sides {r['shared_hinge']['sides']} != {sides}")
                ok = False
            counters["theorem_s_confirmed"] += ok
            confirmed[(a, b)] = "pass" if ok else None
        elif m == "separating_axis":
            counters["axis_rows"] += 1
            cert = r["certificate"]
            ok, gap = axis_ok(probe[a], probe[b], cert)
            if not ok:
                fail("axis_certificate", f"{a}/{b}: axis certificate not confirmed")
            else:
                # R01: the reported Euclidean bound b must satisfy b^2 (d.d) <= g^2, exactly (no square root).
                d0, d1 = Q(cert["axis"][0]), Q(cert["axis"][1])
                eb = Q(cert["euclidean_gap_lower_bound"])
                if eb * eb * (d0 * d0 + d1 * d1) > gap * gap:
                    fail("euclidean_gap_bound", f"{a}/{b}: euclidean_gap_lower_bound exceeds gap/|d|")
                    ok = False
                else:
                    counters["euclidean_bounds_confirmed"] += 1
            counters["axis_confirmed"] += ok
            confirmed[(a, b)] = "pass" if ok else None
        elif m == "interior_witness":
            counters["witness_rows"] += 1
            ok, margin = witness_ok(data, (a, b), probe[a], probe[b], r["certificate"])
            if not ok:
                fail("witness_certificate", f"{a}/{b}: witness certificate not confirmed")
            elif not Q(0) < Q(r["certificate"]["cross_lower_bound"]) <= margin:
                # R01: the recorded bound may be smaller than the recomputed one, never larger.
                fail("witness_bound", f"{a}/{b}: cross_lower_bound exceeds the recomputed lower bound")
                ok = False
            else:
                counters["witness_bounds_confirmed"] += 1
            counters["witness_confirmed"] += ok
            confirmed[(a, b)] = "fail" if ok else None
        else:
            counters["unknown_rows"] += 1
            confirmed[(a, b)] = "unknown"
    vals = set(confirmed.values())
    recomputed = "fail" if "fail" in vals else ("pass" if vals == {"pass"} else "unknown")
    out["recomputed_verdict"] = recomputed
    if recomputed != S["verdict_on_D"]:
        fail("verdict", f"declared verdict_on_D {S['verdict_on_D']!r}, recomputed {recomputed!r}")
    out["status"] = "failed" if failures else "verified"
    return out


def main(bundle_path, out_path):
    iv.prec = PREC
    counters = {k: 0 for k in COUNTERS}
    report = {"label": "isolated Stage 4A prototype: independent re-check; not glab evidence",
              "environment": {"python": sys.version, "platform": platform.platform(), "mpmath": mpmath.__version__,
                              "iv_prec_bits": PREC},
              "contract": BUNDLE_SCHEMA, "scope": SCOPE, "diagnostic_fields_not_verified": DIAGNOSTIC_FIELDS,
              "bundle_failures": [], "seams": {}}
    try:
        with open(bundle_path, encoding="ascii") as fh:
            bundle = json.loads(fh.read())
    except (OSError, ValueError) as exc:
        bundle = None
        report["bundle_failures"].append({"code": "bundle_unreadable", "detail": str(exc)})
    if isinstance(bundle, dict) and bundle.get("schema") != BUNDLE_SCHEMA:
        report["bundle_failures"].append({"code": "bundle_schema",
                                          "detail": f"schema {bundle.get('schema')!r}; binding to source/cut/delta/"
                                                    f"definition/normalization is required"})
    elif isinstance(bundle, dict) and not isinstance(bundle.get("seams"), dict):
        report["bundle_failures"].append({"code": "bundle_shape", "detail": "seams must be an object"})
    elif isinstance(bundle, dict):
        if not bundle["seams"]:
            report["bundle_failures"].append({"code": "bundle_empty", "detail": "no seams to verify"})
        for seam, S in bundle["seams"].items():
            try:
                report["seams"][seam] = check_seam(bundle, seam, S, counters)
            except (KeyError, TypeError, ValueError, ZeroDivisionError, ArithmeticError) as exc:
                report["seams"][seam] = {"status": "rejected", "recomputed_verdict": None,
                                         "failures": [{"code": "malformed", "detail": f"{type(exc).__name__}: {exc}"}]}
    elif bundle is not None:
        report["bundle_failures"].append({"code": "bundle_shape", "detail": "bundle must be an object"})
    statuses = [s["status"] for s in report["seams"].values()]
    totals = dict(counters)
    totals["failures"] = len(report["bundle_failures"]) + sum(len(s["failures"]) for s in report["seams"].values())
    totals["verified_seams"] = statuses.count("verified")
    totals["rejected_seams"] = statuses.count("rejected")
    totals["failed_seams"] = statuses.count("failed")
    totals["verified"] = bool(statuses) and not report["bundle_failures"] and all(s == "verified" for s in statuses)
    report["totals"] = totals
    with open(out_path, "w", encoding="ascii", newline="\n") as fh:
        fh.write(json.dumps(report, indent=1, sort_keys=True) + "\n")
    print(json.dumps(totals, indent=1, sort_keys=True))
    return totals


if __name__ == "__main__":
    sys.exit(0 if main(sys.argv[1], sys.argv[2])["verified"] else 1)
