"""ISOLATED STAGE 4A PROTOTYPE: pair decisions for the ideal trimmed development D (design sections 4, 5.4, 5.5).

Consecutive chain faces: Theorem S (exact). Every other pair (and a consecutive pair whose Theorem S
preconditions fail): interval certificates on enclosures of D, over a precision schedule.
  certified separating axis  -> pass  (D only; boundary contact allowed)
  certified interior witness -> fail  (D only; needs exact strict convexity + orientation of both rings)
  otherwise / any refusal    -> unknown (never converted into pass or fail)
Candidate axes and witnesses are PROPOSALS computed from exact box midpoints; only certification counts.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import combinations

from .ideal import ISOLATED_LABEL, _face_ok, enclose, face_checks, shared_hinge_decision
from .ratint import Interval, IntervalError, sqrt_enclosure

__all__ = ["SCHEDULE", "certify_separation", "certify_witness", "decide_boxes", "classify_pair",
           "classify_seam", "seam_total", "applies_to", "to_json"]

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


def classify_seam(model, schedule=SCHEDULE):
    encl, checks = _Enclosures(model), face_checks(model)
    rows = [classify_pair(model, a, b, schedule, encl, checks)
            for a, b in combinations(model.chain, 2)]
    return {"label": ISOLATED_LABEL, "face_checks": checks, "rows": rows, "total": seam_total(rows),
            "pairs": len(rows), "shared_hinge_rows": sum(r.get("method") == "shared_hinge_exact" for r in rows),
            "enclosure_attempts": {str(b): s for b, (s, _) in sorted(encl.cache.items())}}


def applies_to(certificate: dict, subject) -> bool:
    """A certificate applies only to the identical ideal-subject spec; never to any Run state (float or exact)."""
    if not isinstance(subject, dict) or "payload" in subject or "kind" not in subject:
        return False
    return subject.get("kind") == "ideal_trimmed_development" and subject == certificate["subject"]["spec"]


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
