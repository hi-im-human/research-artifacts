"""Independent Stage 3 checkers for cut, static development and trimmed development states.

Contextual checkers: every ancestor (cut, material, development) is read through the core's
read-only DependencyContext. This module never imports glab.two_rim; cut topology, glue classes,
trim points and face images are reconstructed here from the ACTUAL material ancestor.
NumPy (pinned 2.4.4) is the numerical backend. Numerical claims are `numerical_diagnostic` and carry
NUMERICAL_TOLERANCE_POLICY in Claim.tolerances (a heuristic policy, not an error bound); no claim uses
`rigorous_enclosure` (reserved for Stage 4).

Versions: two_rim.check.cut v1 (claim contract unchanged); two_rim.check.development and
two_rim.check.trimmed_development v2 (Stage 3 repair S02-S04: record schemas enforce the declared map and
height conventions and canonical exact strings; the holonomy diagnostic separates the principal rotation
from the checker's own lifted total turn; numerical claims carry the tolerance policy). v1 is not registered.

Pair policy (every pair, no adjacency skip; tau = 1e-9 * scale):
  SAT depth < -tau                      -> pass  "separated"
  SAT depth > +tau                      -> fail  "interior_overlap"
  exact SAT on the represented rational
  values of the float images decides    -> pass  (exactness concerns only those represented coordinates)
  anything else                         -> unknown "near_contact_unresolved"
Shared glued material (retained hinge / glued vertex) is recorded as information only
(opposite-sides margin, tangent-cone gap); it never upgrades an unresolved pair.
"""
from __future__ import annotations

import copy
import math
from fractions import Fraction
from itertools import combinations
from pathlib import Path

import numpy as np

from ..core.numbers import ExactInputError, format_exact, parse_exact
from ..core.registry import CheckerSpec, Claim, source_revision
from ..core.runfile import ContextError

__all__ = ["register_development_checkers", "classify_pair", "check_cut", "check_development",
           "check_trimmed", "lifted_turn_summary", "CUT_CLAIMS", "DEV_EXACT", "TRIM_EXACT", "NUMERICAL",
           "DIAGNOSTICS", "NUMERICAL_TOLERANCE_POLICY", "SUPPORTED_MAP_CONVENTION", "SUPPORTED_HEIGHT_PARAMETER",
           "DEVELOPMENT_CHECKER_REVISION"]

DEVELOPMENT_CHECKER_REVISION = source_revision(Path(__file__).resolve().parent, Path(__file__).name)
REL = 1e-9
RIGIDITY = 10 * REL
ANGLE_DECIDED = 1e-9  # radians: sign threshold and branch margin (no epsilon sign choice)

# The one policy every numerical claim declares (instance-independent; effective values are in receipts).
NUMERICAL_TOLERANCE_POLICY = {
    "policy": "two_rim.development.numerical/1",
    "status": "heuristic tolerance, not a rigorous error bound",
    "scale_rule": "scale = max(1, largest absolute float64 coordinate among material points and face images)",
    "length_tolerance": {"units": "length", "relative": REL, "rule": "tau = relative * scale",
                         "applies_to": ["glued point agreement", "pair separation depth (SAT)"]},
    "rigidity_threshold": {"units": "dimensionless", "value": RIGIDITY,
                           "applies_to": ["relative squared-distance error", "Gram matrix deviation"]},
    "area_threshold": {"units": "area", "rule": "tau * scale", "applies_to": ["nonempty face images"]},
    "angle_threshold": {"units": "radian", "value": ANGLE_DECIDED,
                        "applies_to": ["holonomy branch margin", "holonomy sign", "rotation agreement modulo 2pi"]},
}
# The only conventions this checker interprets (its own literals; never imported from the generator).
SUPPORTED_MAP_CONVENTION = ("image = linear @ [x, y, z] + offset; linear is 2x3 row-major; x, y, z are the exact "
                            "material coordinates converted to float64")
SUPPORTED_HEIGHT_PARAMETER = "original normalized height t = z/h"

CUT_CLAIMS = ("two_rim.cut.record_schema", "two_rim.cut.material_copy_matches_parent",
              "two_rim.cut.exactly_one_original_seam_open", "two_rim.cut.face_coverage_complete_unique",
              "two_rim.cut.glue_classes_match_cut_relation")
DEV_EXACT = ("two_rim.development.record_schema", "two_rim.development.cut_copy_matches_parent")
TRIM_EXACT = ("two_rim.trim.record_schema", "two_rim.trim.maps_identical_to_parent",
              "two_rim.trim.domain_is_exact_band")
NUMERICAL = ("two_rim.development.face_maps_rigid", "two_rim.development.no_reflected_face",
             "two_rim.development.nonempty_face_images", "two_rim.development.retained_hinges_and_glued_vertices_agree",
             "two_rim.development.face_interiors_disjoint_all_pairs")
DIAGNOSTICS = ("two_rim.development.diagnostic.unglued_pairs_disjoint",
               "two_rim.development.diagnostic.float_representability",
               "two_rim.development.diagnostic.circuit_holonomy")


# ------------------------------------------------------------------ claim helpers

_NUMERIC_CLAIMS = NUMERICAL + (DIAGNOSTICS[0], DIAGNOSTICS[2])


def _claim(pred, outcome, method, receipt, coverage="all"):
    numeric = method == "numerical_diagnostic"
    return Claim(pred, outcome, method, "float64" if numeric else "exact_rational", coverage=coverage,
                 tolerances=copy.deepcopy(NUMERICAL_TOLERANCE_POLICY) if numeric else None, receipt=receipt)


def _exact(pred, ok, receipt):
    return _claim(pred, "pass" if ok else "fail", "exact_computation", receipt)


def _unknown(pred, reason, method="exact_computation", coverage="all"):
    return _claim(pred, "unknown", method, {"not_interpreted": reason}, coverage)


def _guard(fn):
    try:
        return fn()
    except ContextError:
        raise
    except (KeyError, IndexError, TypeError, ValueError, ZeroDivisionError, ExactInputError) as exc:
        return False, {"malformed": f"{type(exc).__name__}: {exc}"}


def _worst(outcomes):
    rank = {"pass": 0, "unknown": 1, "fail": 2}
    return max(outcomes, key=rank.__getitem__, default="pass")


# ------------------------------------------------------------------ independent topology

def _expected_chain(material, seam):
    ids = [e["id"] for e in material["hinges"]]
    k, n = ids.index(seam), len(ids)
    by_entry = {f["entry"]: f["id"] for f in material["faces"]}
    return [by_entry[ids[(k + j) % n]] for j in range(n)]


def _expected_classes(material, order):
    boundary = {f["id"]: f["boundary"] for f in material["faces"]}
    classes = []
    for v in material["vertices"]:
        vid, run = v["id"], []
        for pos, fid in enumerate(order):
            if vid in boundary[fid]:
                run.append(f"{fid}@{vid}")
            else:
                if run:
                    classes.append(run)
                run = []
        if run:
            classes.append(run)
    return classes


def _material_of_parent(context):
    parent = context.parent()
    if parent is None or parent["kind"] != "two_rim.material":
        return None
    return parent["payload"]


_CUT_KEYS = {"schema", "seam", "face_order", "retained_hinges", "occurrences", "glue_classes", "seam_copies",
             "material"}


def _cut_schema(p):
    problems = []
    if not isinstance(p, dict) or set(p) != _CUT_KEYS:
        return False, {"problems": [f"cut keys must be {sorted(_CUT_KEYS)}"]}
    if p["schema"] != "two_rim.cut/1":
        problems.append(f"unsupported schema {p['schema']!r}")
    for key in ("face_order", "retained_hinges", "occurrences"):
        if not isinstance(p[key], list) or not all(isinstance(x, str) for x in p[key]):
            problems.append(f"{key} must be a list of strings")
    if not isinstance(p["glue_classes"], list) or not all(isinstance(c, list) and c and all(isinstance(x, str) for x in c)
                                                          for c in p["glue_classes"]):
        problems.append("glue_classes must be nonempty lists of occurrence strings")
    if not isinstance(p["seam"], str) or not isinstance(p["material"], dict):
        problems.append("seam must be a string and material an object")
    return not problems, {"problems": problems}


def check_cut(state, params, context):
    p = state["payload"]
    schema_ok, schema_rec = _guard(lambda: _cut_schema(p))
    claims = [_exact(CUT_CLAIMS[0], schema_ok, schema_rec)]
    if not schema_ok:
        return claims + [_unknown(c, "cut record schema invalid") for c in CUT_CLAIMS[1:]]
    material = _material_of_parent(context)
    if material is None:
        return claims + [_exact(CUT_CLAIMS[1], False, {"problems": ["parent is not a two_rim.material"]})] + \
            [_unknown(c, "no two_rim.material parent to reconstruct from") for c in CUT_CLAIMS[2:]]
    claims.append(_exact(CUT_CLAIMS[1], p["material"] == material,
                         {"parent_identity": material.get("identity"), "copy_identity": p["material"].get("identity")}))
    hinge_ids = [e["id"] for e in material["hinges"]]

    def seam_open():
        problems = []
        if p["seam"] not in hinge_ids:
            return False, {"problems": [f"seam {p['seam']!r} is not an original hinge"]}
        if p["retained_hinges"] != [h for h in hinge_ids if h != p["seam"]]:
            problems.append("retained hinges must be every original hinge except the seam, in material order")
        order = _expected_chain(material, p["seam"])
        if p["seam_copies"] != {"entry": {"face": order[0], "hinge": p["seam"]},
                                "exit": {"face": order[-1], "hinge": p["seam"]}}:
            problems.append("seam copies must be the entry of the first and exit of the last chain face")
        return not problems, {"seam": p["seam"], "problems": problems}

    def coverage():
        if p["seam"] not in hinge_ids:
            return False, {"problems": ["seam is not an original hinge"]}
        order = _expected_chain(material, p["seam"])
        ok = p["face_order"] == order and len(set(p["face_order"])) == len(material["faces"])
        return ok, {"expected": order, "recorded": p["face_order"]}

    def classes():
        if p["seam"] not in hinge_ids:
            return False, {"problems": ["seam is not an original hinge"]}
        order = _expected_chain(material, p["seam"])
        boundary = {f["id"]: f["boundary"] for f in material["faces"]}
        occ = [f"{fid}@{v}" for fid in order for v in boundary[fid]]
        expected = _expected_classes(material, order)
        seam = next(e for e in material["hinges"] if e["id"] == p["seam"])
        copies = {v: sum(1 for c in expected if c[0].endswith(f"@{v}")) for v in (seam["lower"], seam["upper"])}
        ok = p["glue_classes"] == expected and p["occurrences"] == occ and all(c == 2 for c in copies.values())
        return ok, {"seam_endpoint_copies": copies, "classes": len(expected)}

    claims += [_exact(CUT_CLAIMS[2], *_guard(seam_open)), _exact(CUT_CLAIMS[3], *_guard(coverage)),
               _exact(CUT_CLAIMS[4], *_guard(classes))]
    return claims


# ------------------------------------------------------------------ numerical geometry

def _area(P):
    x, y = P[:, 0], P[:, 1]
    return 0.5 * float(np.dot(x, np.roll(y, -1)) - np.dot(np.roll(x, -1), y))


def _sat_depth(P, Q):
    best = math.inf
    for poly in (P, Q):
        e = np.roll(poly, -1, axis=0) - poly
        axes = np.stack([-e[:, 1], e[:, 0]], axis=1)
        axes = axes / np.linalg.norm(axes, axis=1)[:, None]
        p, q = P @ axes.T, Q @ axes.T
        best = min(best, float(np.min(np.minimum(p.max(0), q.max(0)) - np.maximum(p.min(0), q.min(0)))))
    return best


def _exact_separated(P, Q):
    """Exact on the represented rational values of the float coordinates only."""
    Pe = [(Fraction(float(x)), Fraction(float(y))) for x, y in P]
    Qe = [(Fraction(float(x)), Fraction(float(y))) for x, y in Q]
    for poly in (Pe, Qe):
        m = len(poly)
        for i in range(m):
            ax = (-(poly[(i + 1) % m][1] - poly[i][1]), poly[(i + 1) % m][0] - poly[i][0])
            p = [ax[0] * v[0] + ax[1] * v[1] for v in Pe]
            q = [ax[0] * v[0] + ax[1] * v[1] for v in Qe]
            if min(max(p), max(q)) - max(min(p), min(q)) <= 0:
                return True
    return False


def _clip_area(P, Q):
    out = [tuple(v) for v in P]
    for i in range(len(Q)):
        a, b = Q[i], Q[(i + 1) % len(Q)]
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
            return 0.0
    return abs(_area(np.array(out))) if len(out) >= 3 else 0.0


def _ccw(P):
    return P if _area(P) >= 0 else P[::-1]


def _arc(ring, i):
    v = ring[i]
    a1 = math.atan2(*(ring[(i + 1) % len(ring)] - v)[::-1])
    a2 = math.atan2(*(ring[i - 1] - v)[::-1])
    e = (a2 - a1) % (2 * math.pi)
    return (a1, e) if e < math.pi else (a2, 2 * math.pi - e)


def _shared_info(P, Q, shared):
    if not shared:
        return {}
    if shared["kind"] == "retained_hinge":
        i, j = shared["P"]
        k, l = shared["Q"]
        a, b = P[i], P[j]
        d = b - a
        nrm = np.array([-d[1], d[0]]) / np.linalg.norm(d)
        p_other = [float(np.dot(P[t] - a, nrm)) for t in range(len(P)) if t not in (i, j)]
        q_other = [float(np.dot(Q[t] - a, nrm)) for t in range(len(Q)) if t not in (k, l)]
        s = -1.0 if (p_other and np.mean(p_other) > 0) else 1.0
        margin = min([-s * x for x in p_other] + [s * x for x in q_other]) if p_other and q_other else None
        mismatch = max(float(np.linalg.norm(P[i] - Q[k])), float(np.linalg.norm(P[j] - Q[l])))
        return {"opposite_sides_margin": margin, "glued_point_mismatch": mismatch}
    gaps, mism = [], []
    for iP, iQ in zip(shared["P"], shared["Q"]):
        (s1, w1), (s2, w2) = _arc(P, iP), _arc(Q, iQ)
        gaps.append(min((s2 - s1) % (2 * math.pi) - w1, (s1 - s2) % (2 * math.pi) - w2))
        mism.append(float(np.linalg.norm(P[iP] - Q[iQ])))
    return {"tangent_cone_gap": min(gaps), "glued_point_mismatch": max(mism)}


def classify_pair(P, Q, tau, *, shared=None):
    """(outcome, reason, info) for two convex face images; boundary contact allowed."""
    P, Q = np.asarray(P, dtype=float), np.asarray(Q, dtype=float)
    info = _shared_info(P, Q, shared)
    Pc, Qc = _ccw(P), _ccw(Q)
    depth = _sat_depth(Pc, Qc)
    info["sat_depth"] = depth
    if depth < -tau:
        return "pass", "separated", info
    if depth > tau:
        info["overlap_area"] = _clip_area(Pc, Qc)
        return "fail", "interior_overlap", info
    if _exact_separated(Pc, Qc):
        info["exactness_scope"] = "exact only for the represented float64 image coordinates, not the exact source"
        return "pass", "boundary_contact_or_gap_exact_on_represented_coordinates", info
    return "unknown", "near_contact_unresolved", info


def _face_normal_sign(ring3, plane):
    n = np.array(plane[:3], dtype=float)
    v0, v1, v2 = ring3[0], ring3[1], ring3[2]
    return float(np.sign(np.dot(n, np.cross(v1 - v0, v2 - v1))))


def _numerical(order, rings, maps, glue, shared, planes, scale_pts):
    """The five numerical obligations plus the unglued diagnostic.

    rings[face] = list of (label, exact xyz Fractions); maps[face] = (L 2x3, o 2);
    glue = list of [(face, label), ...] groups that must coincide; shared[(a, b)] = shared dict or None.
    """
    P3 = {f: np.array([[float(c) for c in xyz] for _, xyz in rings[f]]) for f in order}
    img = {f: P3[f] @ maps[f][0].T + maps[f][1] for f in order}
    scale = max(1.0, max(float(np.max(np.abs(v))) for v in list(img.values()) + list(P3.values())))
    tau = REL * scale
    tol = {"relative": REL, "scale": scale, "tau": tau, "status": "heuristic tolerance, not a rigorous error bound"}
    out = []
    # rigidity
    worst, bad = 0.0, []
    for f in order:
        ring = rings[f]
        for a, b in combinations(range(len(ring)), 2):
            d3 = float(sum((x - y) ** 2 for x, y in zip(ring[a][1], ring[b][1])))
            d2 = float(np.sum((img[f][a] - img[f][b]) ** 2))
            err = abs(d3 - d2) / max(1.0, d3)
            worst = max(worst, err)
            if err > RIGIDITY:
                bad.append(f)
        L = maps[f][0]
        e1 = P3[f][1] - P3[f][0]
        e1 = e1 / np.linalg.norm(e1)
        w = P3[f][2] - P3[f][0] - np.dot(P3[f][2] - P3[f][0], e1) * e1
        e2 = w / np.linalg.norm(w)
        G = np.array([[np.dot(L @ e1, L @ e1), np.dot(L @ e1, L @ e2)], [np.dot(L @ e1, L @ e2), np.dot(L @ e2, L @ e2)]])
        gerr = float(np.max(np.abs(G - np.eye(2))))
        worst = max(worst, gerr)
        if gerr > RIGIDITY:
            bad.append(f)
    out.append(_claim(NUMERICAL[0], "fail" if bad else "pass", "numerical_diagnostic",
                      {"max_relative_error": worst, "threshold": RIGIDITY, "failing_faces": sorted(set(bad)), **tol}))
    # reflection
    signs = {f: int(np.sign(_area(img[f]))) * int(_face_normal_sign(P3[f], planes[f])) for f in order}
    uniform = len(set(signs.values())) == 1 and 0 not in signs.values()
    out.append(_claim(NUMERICAL[1], "pass" if uniform else "fail", "numerical_diagnostic",
                      {"relative_orientation": signs, **tol}))
    # nonempty
    areas = {f: abs(_area(img[f])) for f in order}
    small = [f for f, a in areas.items() if a <= tau * scale]
    out.append(_claim(NUMERICAL[2], "fail" if small else "pass", "numerical_diagnostic",
                      {"min_area": min(areas.values()), "degenerate": small, **tol}))
    # agreement
    index = {f: {label: t for t, (label, _) in enumerate(rings[f])} for f in order}
    worst, bad = 0.0, []
    for group in glue:
        pts = [img[f][index[f][label]] for f, label in group]
        for q in pts[1:]:
            d = float(np.linalg.norm(q - pts[0]))
            worst = max(worst, d)
            if d > tau:
                bad.append(group[0][1])
    out.append(_claim(NUMERICAL[3], "fail" if bad else "pass", "numerical_diagnostic",
                      {"max_mismatch": worst, "groups": len(glue), "failing": sorted(set(bad)), **tol}))
    # all pairs, no adjacency skip
    rows = []
    for a, b in combinations(order, 2):
        sh = shared.get((a, b))
        res, why, info = classify_pair(img[a], img[b], tau, shared=sh)
        rows.append({"pair": [a, b], "outcome": res, "reason": why, "shared": sh["kind"] if sh else None, **info})
    adjacent = sum(1 for r in rows if r["shared"] == "retained_hinge")
    receipt = {"pairs_checked": len(rows), "adjacent_pairs_checked": adjacent, "adjacent_pairs_skipped": 0,
               "counts": {k: sum(r["reason"] == k for r in rows) for k in
                          ("separated", "interior_overlap", "boundary_contact_or_gap_exact_on_represented_coordinates",
                           "near_contact_unresolved")},
               "policy": "separated/overlap beyond tau decide; else exact SAT on represented coordinates; else unknown. "
                         "Shared glued material is information only.", "rows": rows, **tol}
    out.append(_claim(NUMERICAL[4], _worst(r["outcome"] for r in rows), "numerical_diagnostic", receipt))
    unglued = [r for r in rows if r["shared"] is None]
    out.append(_claim(DIAGNOSTICS[0], _worst(r["outcome"] for r in unglued), "numerical_diagnostic",
                      {"pairs_checked": len(unglued), "failing_or_unknown": [r["pair"] for r in unglued
                                                                              if r["outcome"] != "pass"], **tol},
                      coverage="pairs_without_glued_material"))
    return out, img, tol


def _sign(x):
    return "unknown" if abs(x) <= ANGLE_DECIDED else ("negative" if x < 0 else "positive")


def lifted_turn_summary(increments, principal_rotation, generator_sum_q):
    """(outcome, receipt) for the circuit rotation diagnostic.

    increments: the checker's own per-face principal angles from each face's entry-hinge image to its
    exit-hinge image, in chain order; their sum is the lifted total turn. The lift is decided only when
    every increment stays ANGLE_DECIDED away from the branch at +-pi. principal_rotation (in (-pi, pi]) comes
    from the two seam-copy images; it is compared with the lift modulo 2pi, never by absolute value.
    generator_sum_q is the generator's recorded lift: compared and reported, never used as evidence
    (None when the generator record does not supply a finite value).
    """
    lift = math.fsum(increments)
    margin = math.pi - max((abs(x) for x in increments), default=0.0)
    decided = margin > ANGLE_DECIDED
    wrapped = (lift - principal_rotation + math.pi) % (2 * math.pi) - math.pi
    agree_mod = abs(wrapped) <= ANGLE_DECIDED
    gen_ok = None if generator_sum_q is None else abs(lift - generator_sum_q) <= ANGLE_DECIDED
    if not decided:
        outcome = "unknown"
    else:
        outcome = "pass" if agree_mod and gen_ok is not False else "fail"
    return outcome, {
        "principal_rotation": principal_rotation, "principal_rotation_sign": _sign(principal_rotation),
        "principal_rotation_source": "angle in (-pi, pi] between the two seam-copy images",
        "lifted_total_turn": lift, "lift_decided": decided,
        "lifted_total_turn_sign": _sign(lift) if decided else "unknown",
        "lift_method": "checker: sum over chain faces of the principal angle from the entry-hinge image to the "
                       "exit-hinge image within that face's own image",
        "increments": len(increments), "min_branch_margin": margin,
        "rotations_agree_mod_2pi": agree_mod, "wrapped_difference": wrapped,
        "generator_sum_q": {"value": generator_sum_q, "attributed_to": "generator",
                            "note": "recorded by the generator; compared, never used as evidence"},
        "generator_agrees_with_checker_lift": gen_ok,
        "note": "diagnostic, not a safety obligation; signs within the angle threshold are unknown "
                "(no epsilon sign choice); a principal angle never determines the lifted sign"}


def _holonomy(img_of, order, hinge_labels, seam_labels, generator_sum_q, tol):
    """hinge_labels(face) = ((entry_lo, entry_hi), (exit_lo, exit_hi)) labels in that face's ring."""
    def angle(g0, g1):
        return math.atan2(g0[0] * g1[1] - g0[1] * g1[0], float(np.dot(g0, g1)))
    increments = []
    for f in order:
        (a_lo, a_hi), (b_lo, b_hi) = hinge_labels(f)
        increments.append(angle(img_of(f, a_hi) - img_of(f, a_lo), img_of(f, b_hi) - img_of(f, b_lo)))
    first, last = order[0], order[-1]
    lo, hi = seam_labels
    ang = angle(img_of(first, hi) - img_of(first, lo), img_of(last, hi) - img_of(last, lo))
    c, s = math.cos(ang), math.sin(ang)
    trans = img_of(last, lo) - np.array([[c, -s], [s, c]]) @ img_of(first, lo)
    outcome, receipt = lifted_turn_summary(increments, ang, generator_sum_q)
    receipt.update({"translation_norm": float(np.linalg.norm(trans)),
                    "pole_condition_1_over_2sin_half_rotation":
                        None if abs(ang) <= ANGLE_DECIDED else 1 / abs(2 * math.sin(ang / 2)), **tol})
    return _claim(DIAGNOSTICS[2], outcome, "numerical_diagnostic", receipt)


def _finite(x):
    return isinstance(x, (int, float)) and not isinstance(x, bool) and math.isfinite(x)


def _representable(pred_values):
    errs = [abs(Fraction(float(x)) - x) for x in pred_values]
    worst = max(errs) if errs else Fraction(0)
    return _exact(DIAGNOSTICS[1], worst == 0,
                  {"max_abs_rounding": float(worst), "meaning": "fail = the float images use rounded coordinates, "
                                                                "not the exact source"})


def _maps_arrays(maps):
    return {m["face"]: (np.array(m["linear"], dtype=float), np.array(m["offset"], dtype=float)) for m in maps}


_DEV_KEYS = {"schema", "numeric_domain", "map_convention", "maps", "cut", "generator"}


def _maps_ok(maps, order):
    if not isinstance(maps, list) or [m.get("face") if isinstance(m, dict) else None for m in maps] != order:
        return False
    for m in maps:
        if set(m) != {"face", "linear", "offset"} or not (isinstance(m["linear"], list) and len(m["linear"]) == 2):
            return False
        vals = [x for row in m["linear"] for x in (row if isinstance(row, list) and len(row) == 3 else [None] * 4)]
        vals += list(m["offset"]) if isinstance(m["offset"], list) and len(m["offset"]) == 2 else [None]
        if len(vals) != 8 or not all(_finite(x) for x in vals):
            return False
    return True


_GENERATOR_KEYS = {"name", "port_of", "turns_q", "sum_q"}


def _dev_schema(p, order):
    """Declared two_rim.development/1 contract, including the map convention and the generator block's shape.

    The generator's values are shape-checked only; they are never used as evidence.
    """
    if not isinstance(p, dict) or set(p) != _DEV_KEYS:
        return False, {"problems": [f"development keys must be {sorted(_DEV_KEYS)}"]}
    problems = []
    if p["schema"] != "two_rim.development/1":
        problems.append(f"unsupported schema {p['schema']!r}")
    if p["numeric_domain"] != "float64":
        problems.append(f"unsupported numeric_domain {p['numeric_domain']!r}")
    if p["map_convention"] != SUPPORTED_MAP_CONVENTION:
        problems.append("unsupported map_convention (only 'image = linear @ [x, y, z] + offset' is interpreted)")
    if not _maps_ok(p["maps"], order):
        problems.append("maps must be finite 2x3 linear parts and 2-vector offsets, one per face in chain order")
    if not isinstance(p["cut"], dict):
        problems.append("cut must be an object")
    g = p["generator"]
    if not isinstance(g, dict) or set(g) != _GENERATOR_KEYS:
        problems.append(f"generator must be an object with keys {sorted(_GENERATOR_KEYS)}")
    else:
        if not isinstance(g["name"], str) or not isinstance(g["port_of"], str):
            problems.append("generator name and port_of must be strings")
        if not isinstance(g["turns_q"], list) or len(g["turns_q"]) != len(order) or \
                not all(_finite(x) for x in g["turns_q"]):
            problems.append("generator turns_q must be one finite number per face")
        if not _finite(g["sum_q"]):
            problems.append("generator sum_q must be a finite number")
    return not problems, {"supported": {"schema": "two_rim.development/1", "numeric_domain": "float64",
                                        "map_convention": SUPPORTED_MAP_CONVENTION}, "problems": problems}


def _canonical_exact(s):
    """A canonical exact string ('n' or 'n/d' in lowest terms); bools, ints, floats and other spellings are not."""
    if not isinstance(s, str):
        return False
    try:
        return format_exact(parse_exact(s)) == s
    except ExactInputError:
        return False


def _trim_schema(p, order, keys, expected_faces):
    """Declared two_rim.trim/1 contract, including the height convention and canonical exact trim points."""
    if not isinstance(p, dict) or set(p) != _TRIM_KEYS:
        return False, {"problems": [f"trim keys must be {sorted(_TRIM_KEYS)}"]}
    problems = []
    if p["schema"] != "two_rim.trim/1":
        problems.append(f"unsupported schema {p['schema']!r}")
    if not _canonical_exact(p["delta"]):
        problems.append("delta must be a canonical exact string")
    if p["height_parameter"] != SUPPORTED_HEIGHT_PARAMETER:
        problems.append(f"unsupported height_parameter (only {SUPPORTED_HEIGHT_PARAMETER!r} is interpreted)")
    if not _maps_ok(p["maps"], order):
        problems.append("maps must be finite 2x3 linear parts and 2-vector offsets, one per face in chain order")
    if p["faces"] != expected_faces:
        problems.append("faces must be the material faces with boundary [entry@lo, entry@hi, exit@hi, exit@lo]")
    pts = p["trim_points"]
    if not isinstance(pts, dict) or set(pts) != keys:
        problems.append("trim_points must have exactly the keys <hinge>@lo and <hinge>@hi for every hinge")
    else:
        for k in sorted(pts):
            pt = pts[k]
            if not isinstance(pt, dict) or set(pt) != {"hinge", "t", "xyz"}:
                problems.append(f"{k}: a trim point is an object with exactly hinge, t, xyz")
            elif not isinstance(pt["hinge"], str) or not _canonical_exact(pt["t"]) or \
                    not isinstance(pt["xyz"], list) or len(pt["xyz"]) != 3 or \
                    not all(_canonical_exact(c) for c in pt["xyz"]):
                problems.append(f"{k}: hinge must be a string, t and exactly three xyz coordinates canonical "
                                "exact strings")
    return not problems, {"supported": {"schema": "two_rim.trim/1", "height_parameter": SUPPORTED_HEIGHT_PARAMETER},
                          "problems": problems}


def _ancestors(context, kinds):
    """Walk parents from the subject; return payloads for the requested kinds in order, or None."""
    out, state = [], context.get(context.subject)
    for kind in kinds:
        parent_hash = state["parent"]
        if parent_hash is None:
            return None
        state = context.get(parent_hash)
        if state["kind"] != kind:
            return None
        out.append(state["payload"])
    return out


def _full_rings(material):
    xyz = {v["id"]: tuple(Fraction(c) for c in v["xyz"]) for v in material["vertices"]}
    return {f["id"]: [(v, xyz[v]) for v in f["boundary"]] for f in material["faces"]}


def _full_shared(material, order, classes):
    ring = {f["id"]: f["boundary"] for f in material["faces"]}
    pos = {f: i for i, f in enumerate(order)}
    shared = {}
    for a, b in combinations(order, 2):
        glued = [c for c in classes if any(o.startswith(f"{a}@") for o in c) and any(o.startswith(f"{b}@") for o in c)]
        verts = [c[0].split("@")[1] for c in glued]
        if abs(pos[a] - pos[b]) == 1 and len(verts) == 2:
            first, second = (a, b) if pos[a] < pos[b] else (b, a)
            hinge = next(f for f in material["faces"] if f["id"] == first)["exit"]
            e = next(h for h in material["hinges"] if h["id"] == hinge)
            shared[(a, b)] = {"kind": "retained_hinge",
                              "P": (ring[a].index(e["lower"]), ring[a].index(e["upper"])),
                              "Q": (ring[b].index(e["lower"]), ring[b].index(e["upper"]))}
        elif verts:
            shared[(a, b)] = {"kind": "glued_vertex", "P": [ring[a].index(v) for v in verts],
                              "Q": [ring[b].index(v) for v in verts]}
    return shared


def _schema_invalid(first_claims, rest, reason):
    return first_claims + [_unknown(c, reason, "numerical_diagnostic" if c in _NUMERIC_CLAIMS else "exact_computation")
                           for c in rest]


def _generator_sum(dev):
    g = dev.get("generator") if isinstance(dev, dict) else None
    return g["sum_q"] if isinstance(g, dict) and _finite(g.get("sum_q")) else None


def check_development(state, params, context):
    p = state["payload"]
    anc = _ancestors(context, ["two_rim.cut", "two_rim.material"])
    if anc is None:
        return _schema_invalid([_exact(DEV_EXACT[0], False, {"problems": ["ancestors must be two_rim.cut then "
                                                                          "two_rim.material"]})],
                               DEV_EXACT[1:] + NUMERICAL + DIAGNOSTICS, "missing cut/material ancestors")
    cut, material = anc
    order = cut["face_order"]
    schema_ok, rec = _guard(lambda: _dev_schema(p, order))
    claims = [_exact(DEV_EXACT[0], schema_ok, rec)]
    if not schema_ok:
        return _schema_invalid(claims, DEV_EXACT[1:] + NUMERICAL + DIAGNOSTICS, "development record schema invalid")
    claims.append(_exact(DEV_EXACT[1], p["cut"] == cut, {"seam": cut["seam"]}))
    classes = _expected_classes(material, order)
    rings = _full_rings(material)
    glue = [[(o.split("@")[0], o.split("@")[1]) for o in c] for c in classes if len(c) > 1]
    planes = {f["id"]: f["plane"] for f in material["faces"]}
    num, img, tol = _numerical(order, rings, _maps_arrays(p["maps"]), glue, _full_shared(material, order, classes),
                               planes, None)
    claims += num
    claims.append(_representable([c for v in material["vertices"] for c in map(Fraction, v["xyz"])]))
    hinges = {e["id"]: (e["lower"], e["upper"]) for e in material["hinges"]}
    faces = {f["id"]: f for f in material["faces"]}
    idx = {f: {label: t for t, (label, _) in enumerate(rings[f])} for f in order}
    claims.append(_holonomy(lambda f, label: img[f][idx[f][label]], order,
                            lambda f: (hinges[faces[f]["entry"]], hinges[faces[f]["exit"]]),
                            hinges[cut["seam"]], p["generator"]["sum_q"], tol))
    return claims


_TRIM_KEYS = {"schema", "delta", "height_parameter", "maps", "trim_points", "faces"}


def check_trimmed(state, params, context):
    p = state["payload"]
    anc = _ancestors(context, ["two_rim.development", "two_rim.cut", "two_rim.material"])
    if anc is None:
        return _schema_invalid([_exact(TRIM_EXACT[0], False, {"problems": ["ancestors must be development, cut, "
                                                                           "material"]})],
                               TRIM_EXACT[1:] + NUMERICAL + DIAGNOSTICS, "missing ancestors")
    dev, cut, material = anc
    order = cut["face_order"]
    hinge_ids = [e["id"] for e in material["hinges"]]
    expected_faces = [{"face": f["id"], "boundary": [f"{f['entry']}@lo", f"{f['entry']}@hi", f"{f['exit']}@hi",
                                                     f"{f['exit']}@lo"]} for f in material["faces"]]
    keys = {f"{h}@{t}" for h in hinge_ids for t in ("lo", "hi")}
    schema_ok, rec = _guard(lambda: _trim_schema(p, order, keys, expected_faces))
    claims = [_exact(TRIM_EXACT[0], schema_ok, rec)]
    if not schema_ok:
        return _schema_invalid(claims, TRIM_EXACT[1:] + NUMERICAL + DIAGNOSTICS, "trim record schema invalid")
    claims.append(_exact(TRIM_EXACT[1], p["maps"] == dev["maps"], {"parent_maps": len(dev["maps"])}))
    d = parse_exact(p["delta"])
    xyz = {v["id"]: [Fraction(c) for c in v["xyz"]] for v in material["vertices"]}

    def band():
        problems = []
        if not Fraction(0) < d < Fraction(1, 2):
            problems.append("delta outside (0, 1/2)")
        for e in material["hinges"]:
            lo, hi = xyz[e["lower"]], xyz[e["upper"]]
            for tag, t in (("lo", d), ("hi", 1 - d)):
                pt = p["trim_points"][f"{e['id']}@{tag}"]
                want = [a + t * (b - a) for a, b in zip(lo, hi)]
                if pt["hinge"] != e["id"] or parse_exact(pt["t"]) != t or [parse_exact(c) for c in pt["xyz"]] != want:
                    problems.append(f"{e['id']}@{tag} is not L + t G with t = {format_exact(t)}")
        return not problems, {"delta": p["delta"], "problems": problems}
    claims.append(_exact(TRIM_EXACT[2], *_guard(band)))
    pts = {k: tuple(parse_exact(c) for c in v["xyz"]) for k, v in p["trim_points"].items()}
    rings = {f["face"]: [(k, pts[k]) for k in f["boundary"]] for f in p["faces"]}
    pos = {f: i for i, f in enumerate(order)}
    glue, shared = [], {}
    by_id = {f["id"]: f for f in material["faces"]}
    for a, b in zip(order, order[1:]):
        h = by_id[a]["exit"]
        glue += [[(a, f"{h}@lo"), (b, f"{h}@lo")], [(a, f"{h}@hi"), (b, f"{h}@hi")]]
        pair = (a, b) if pos[a] < pos[b] else (b, a)
        ra, rb = [k for k, _ in rings[pair[0]]], [k for k, _ in rings[pair[1]]]
        shared[pair] = {"kind": "retained_hinge", "P": (ra.index(f"{h}@lo"), ra.index(f"{h}@hi")),
                        "Q": (rb.index(f"{h}@lo"), rb.index(f"{h}@hi"))}
    ordered_shared = {}
    for a, b in combinations(order, 2):
        if (a, b) in shared:
            ordered_shared[(a, b)] = shared[(a, b)]
        elif (b, a) in shared:
            s = shared[(b, a)]
            ordered_shared[(a, b)] = {"kind": s["kind"], "P": s["Q"], "Q": s["P"]}
    planes = {f["id"]: f["plane"] for f in material["faces"]}
    num, img, tol = _numerical(order, rings, _maps_arrays(p["maps"]), glue, ordered_shared, planes, None)
    claims += num
    claims.append(_representable([c for v in pts.values() for c in v]))
    idx = {f: {label: t for t, (label, _) in enumerate(rings[f])} for f in order}
    ends = lambda h: (f"{h}@lo", f"{h}@hi")  # noqa: E731
    claims.append(_holonomy(lambda f, label: img[f][idx[f][label]], order,
                            lambda f: (ends(by_id[f]["entry"]), ends(by_id[f]["exit"])),
                            ends(cut["seam"]), _generator_sum(dev), tol))
    return claims


def register_development_checkers(registry) -> None:
    """two_rim.check.cut v1 (unchanged claim contract); development and trimmed checkers v2 only."""
    rev = DEVELOPMENT_CHECKER_REVISION
    registry.register_checker(CheckerSpec("two_rim.check.cut", 1, "two_rim.cut", {}, rev, check_cut, uses_context=True))
    registry.register_checker(CheckerSpec("two_rim.check.development", 2, "two_rim.development", {}, rev,
                                          check_development, uses_context=True))
    registry.register_checker(CheckerSpec("two_rim.check.trimmed_development", 2, "two_rim.trimmed_development", {},
                                          rev, check_trimmed, uses_context=True))
