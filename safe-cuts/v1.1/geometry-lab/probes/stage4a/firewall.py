"""ISOLATED STAGE 4A PROTOTYPE: certificates name only the ideal subject; float placements are compared, never trusted.

ideal_certificate: issued only after bind() (repairs A01/A02) has recomputed the subject ID, re-read and verified
the named states, rebuilt the exact model, checked the supported domain and every face precondition, and
recomputed source linkage from the Run's actual evidence. Otherwise it returns a structured REFUSAL (status
"refused", seam_verdict "refused"): a refusal is never an overlap verdict. aligned_distance_to_enclosure: a
DIAGNOSTIC distance between a Stage 3 float placement (rigidly aligned to normalization N0) and the enclosure of
D; it never changes any verdict and no verdict is transferred through it.
"""
from __future__ import annotations

import math
from fractions import Fraction

from glab.core.records import content_hash

from .binding import bind, prerequisite_status
from .classify import SCHEDULE, classify_seam, to_json
from .ideal import ISOLATED_LABEL

__all__ = ["ideal_certificate", "aligned_distance_to_enclosure"]

SCOPE = ("verdicts concern only the ideal trimmed development D named by subject.spec; they do not apply to any "
         "Stage 3 float state")


def ideal_certificate(subject, schedule=SCHEDULE) -> dict:
    model, material, pre, refusal = bind(subject)
    spec = to_json(subject.spec)
    status = prerequisite_status(subject.run, spec)
    common = {"label": ISOLATED_LABEL, "subject": {"spec": spec, "id": subject.id}, "scope": SCOPE,
              "prerequisites": {"source_linked": status["source_linked"], "rows": status["rows"],
                                "problems": status["problems"]}}
    if refusal is not None:
        body = to_json(dict(common, status="refused", refusal=refusal, source_linked=False, seam_verdict="refused",
                            local_verdict_on_D=None, classification=None, preconditions=pre))
        return dict(body, digest=content_hash(body))
    result = classify_seam(model, schedule)
    classification = to_json(result)
    linked = status["source_linked"]
    body = to_json(dict(common, status="issued", source_linked=linked, source_link_problems=status["problems"],
                        preconditions=pre, seam_verdict=result["total"] if linked else "not_source_linked",
                        local_verdict_on_D=result["total"], classification=classification,
                        # Verdicts about D alone (independent of which Run holds the prerequisite evidence).
                        classification_digest=content_hash({"subject": spec, "classification": classification})))
    return dict(body, digest=content_hash(body))


def aligned_distance_to_enclosure(model, enclosure, trimmed_payload) -> dict:
    """Max Euclidean distance from aligned float images to the ideal boxes (0 inside a box). Diagnostic only."""
    maps = {m["face"]: m for m in trimmed_payload["maps"]}
    pts = {k: [float(Fraction(c)) for c in v["xyz"]] for k, v in trimmed_payload["trim_points"].items()}

    def image(face, key):
        m = maps[face]
        return [sum(m["linear"][r][c] * pts[key][c] for c in range(3)) + m["offset"][r] for r in range(2)]
    first = model.chain[0]
    ring = model.rings[first]
    b0, a0 = image(first, ring[0]), image(first, ring[1])
    L = math.hypot(a0[0] - b0[0], a0[1] - b0[1])
    ex = ((a0[0] - b0[0]) / L, (a0[1] - b0[1]) / L)
    ey = (-ex[1], ex[0])
    probe = image(first, ring[2])
    mirror = (probe[0] - b0[0]) * ey[0] + (probe[1] - b0[1]) * ey[1] < 0
    if mirror:
        ey = (-ey[0], -ey[1])
    worst = 0.0
    for face in model.chain:
        for k, (bx, by) in zip(model.rings[face], enclosure["boxes"][face]):
            p = image(face, k)
            x = (p[0] - b0[0]) * ex[0] + (p[1] - b0[1]) * ex[1]
            y = (p[0] - b0[0]) * ey[0] + (p[1] - b0[1]) * ey[1]
            dx = max(float(bx.lo) - x, 0.0, x - float(bx.hi))
            dy = max(float(by.lo) - y, 0.0, y - float(by.hi))
            worst = max(worst, math.hypot(dx, dy))
    return {"label": "diagnostic only: float placement vs enclosure of D; never a verdict",
            "alignment": "first chain face entry-hinge trim points; " + ("mirror needed" if mirror else "rotation"),
            "mirror": mirror, "max_distance": worst}
