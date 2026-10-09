"""ISOLATED STAGE 4A PROTOTYPE: the ideal trimmed development D (STAGE-4A-DESIGN.md sections 2, 4, 5).

- ExactModel: exact rational data of one (material, cut, delta) read from real Run states; deeply immutable
  (frozen dataclass, FrozenDict maps, tuples) since the Stage 4A repair A02.
- require_supported_delta / preconditions: the supported positive-trim domain and the face, orientation and chain
  conditions the construction and classification need (repair A01); checked again at certificate issuance.
- face_checks: exact planarity, hinge-in-plane and strict counterclockwise convexity of trimmed rings.
- shared_hinge_decision: Theorem S (exact rational side values sigma; no numerics, no boxes, no tolerance).
- enclose: outward rational-interval enclosures of the ideal face maps Phi_t (entry-hinge frames, 5.1).
Float states are never read here.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction

from glab.core.numbers import ExactInputError, format_exact, parse_exact
from glab.core.records import content_hash

from .ratint import Interval, IntervalError, rsqrt, sqrt_enclosure

__all__ = ["DEFINITION", "ORIENTATION", "NORMALIZATION", "ISOLATED_LABEL", "FrozenDict", "freeze", "thaw",
           "UnsupportedSubject", "require_supported_delta", "ExactModel", "model_from_payloads", "Subject",
           "load_subject", "preconditions", "face_checks", "shared_hinge_decision", "enclose", "sub", "dot", "cross"]

DEFINITION = "stage4a.ideal_development/1"
ORIENTATION = "outward: each face map preserves orientation with respect to that face's outward normal"
NORMALIZATION = "N0: first chain face's entry-hinge low trim point at (0, 0); that hinge along +x"
ISOLATED_LABEL = ("isolated Stage 4A prototype; not glab evidence; no rigorous_enclosure or formal_proof claim "
                  "issued")


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def dot(a, b):
    return sum((x * y for x, y in zip(a, b)), Fraction(0))


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])


# ------------------------------------------------------------------ immutability (A02)

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


# ------------------------------------------------------------------ domain (A01)

class UnsupportedSubject(ValueError):
    """The requested ideal subject is outside the supported positive-trim domain; no D is defined."""


def require_supported_delta(delta) -> Fraction:
    """delta must be a canonical exact string with 0 < delta < 1/2 (manuscript (2.3)); anything else is refused."""
    if not isinstance(delta, str):
        raise UnsupportedSubject(f"delta must be a canonical exact string, got {type(delta).__name__}")
    try:
        d = parse_exact(delta)
    except ExactInputError as exc:
        raise UnsupportedSubject(f"delta is not an exact rational: {exc}") from None
    if format_exact(d) != delta:
        raise UnsupportedSubject(f"delta {delta!r} is not in canonical form {format_exact(d)!r}")
    if not Fraction(0) < d < Fraction(1, 2):
        raise UnsupportedSubject(f"delta {delta} is outside the supported domain 0 < delta < 1/2")
    return d


# ------------------------------------------------------------------ the exact model

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


@dataclass(frozen=True)
class Subject:
    spec: FrozenDict
    id: str
    model: ExactModel
    run: object = field(compare=False, repr=False)
    source_linked: bool = False          # informational at load time; certificates recompute it
    problems: tuple = ()
    prerequisites: FrozenDict = field(default_factory=FrozenDict)


def load_subject(prepared, seam: str, delta) -> Subject:
    """The ideal subject for (source, material, cut, delta), read from the Run; never from float states.

    Raises UnsupportedSubject before any D exists when delta is outside 0 < delta < 1/2 or not canonical.
    """
    from .binding import prerequisite_status
    d = require_supported_delta(delta)
    run = prepared.run
    cut_hash = prepared.cuts[seam]
    cut_state = run.get(cut_hash)
    material_hash = cut_state["parent"]
    material_state = run.get(material_hash)
    problems = []
    if material_state["kind"] != "two_rim.material":
        problems.append("cut parent is not a two_rim.material state")
    source_hash = material_state["parent"]
    if source_hash is None or run.get(source_hash)["kind"] != "two_rim.source":
        problems.append("material parent is not a two_rim.source state")
    if cut_state["payload"]["material"] != material_state["payload"]:
        problems.append("the cut's material copy differs from its parent material")
    spec = {"kind": "ideal_trimmed_development", "definition": DEFINITION, "material_state": material_hash,
            "material_identity": material_state["payload"]["identity"], "source_state": source_hash,
            "cut_state": cut_hash, "seam": seam, "delta": format_exact(d),
            "orientation": ORIENTATION, "normalization": NORMALIZATION}
    status = prerequisite_status(run, spec)
    problems += status["problems"]
    model = model_from_payloads(material_state["payload"], cut_state["payload"], format_exact(d))
    by_role = {}
    for row in status["rows"]:
        by_role.setdefault(row["role"], []).append(row)
    return Subject(freeze(spec), content_hash(spec), model, run, not problems, tuple(problems), freeze(by_role))


def preconditions(model: ExactModel, material: dict) -> dict:
    """Exact conditions D's construction and classification need (A01). Returns {"checks", "problems"}."""
    problems = []
    checks = {"delta_in_domain": Fraction(0) < model.delta < Fraction(1, 2)}
    if not checks["delta_in_domain"]:
        problems.append(f"delta {format_exact(model.delta)} is outside 0 < delta < 1/2")
    face_ids = set(model.faces)
    chain_ok = sorted(model.chain) == sorted(face_ids) and len(model.chain) == len(face_ids) and len(model.chain) >= 3
    if chain_ok:
        chain_ok = model.faces[model.chain[0]]["entry"] == model.seam and \
            model.faces[model.chain[-1]]["exit"] == model.seam and \
            all(model.faces[a]["exit"] == model.faces[b]["entry"] for a, b in zip(model.chain, model.chain[1:]))
    checks["chain_consistent"] = chain_ok
    if not chain_ok:
        problems.append("the cut's chain is not the face cycle opened at the seam (entry/exit mismatch)")
    all_vertices = [tuple(Fraction(c) for c in v["xyz"]) for v in material["vertices"]]
    fc = face_checks(model)
    for fid, f in model.faces.items():
        n = f["normal"]
        outward = any(n) and all(dot(n, v) <= f["offset"] for v in all_vertices)
        degenerate = [h for h in (f["entry"], f["exit"]) if not any(sub(*reversed(model.hinge_points(h))))]
        c = fc[fid]
        for name, ok, msg in (("nonzero_normal", c["nonzero_normal"], "zero normal"),
                              ("planar", c["planar"], "ring not on its recorded plane"),
                              ("outward_normal", outward, "recorded normal is not outward (orientation)"),
                              ("hinges_nondegenerate", not degenerate, f"degenerate hinge {degenerate}"),
                              ("hinges_in_plane", c["hinges_in_plane"], "hinge not in the face plane"),
                              ("trimmed_ring_convex_counterclockwise", c["trimmed_ring_convex_counterclockwise"],
                               "trimmed ring not strictly convex counterclockwise about the normal")):
            checks[f"{fid}.{name}"] = bool(ok)
            if not ok:
                problems.append(f"{fid}: {msg}")
    return {"checks": checks, "problems": problems}


# ------------------------------------------------------------------ exact face checks (O5)

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


# ------------------------------------------------------------------ Theorem S (exact)

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


# ------------------------------------------------------------------ enclosures of D (section 5)

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
