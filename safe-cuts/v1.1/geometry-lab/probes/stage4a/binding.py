"""ISOLATED STAGE 4A PROTOTYPE: bind a certificate to its subject and to actual prerequisite evidence at use time.

Stage 4A repair A02 (with A01's issuance-time preconditions):
- bind(subject): recompute the subject ID from its spec, check the spec's fixed definitions, read the three named
  states from the Run and verify their content hashes, kinds, parent links, material identity and cut copy, REBUILD
  the exact model from those states and compare it with the carried one, then check the domain and preconditions.
  Any failure is a structured refusal; nothing carried by the caller is trusted.
- prerequisite_status(run, spec): the complete expected Stage 2 / cut claim sets on their actual subject hashes,
  summarized by the core (fresh validate_evidence: current chain, representation, registered checker revision;
  method exact_computation; coverage all; tolerances null), with every covering evidence ID resolved to its record
  and its checker name and version checked. Cached summaries (Prepared.prerequisites) are never consulted.
"""
from __future__ import annotations

from glab.check.two_rim_development import CUT_CLAIMS
from glab.check.two_rim_source import MATERIAL_CLAIMS, SOURCE_CLAIMS
from glab.core.evidence import Requirement, evidence_id
from glab.core.records import RecordError, content_hash
from glab.two_rim.material import material_identity

from .ideal import (DEFINITION, NORMALIZATION, ORIENTATION, UnsupportedSubject, model_from_payloads, preconditions,
                    require_supported_delta)

__all__ = ["EXPECTED_PREREQUISITES", "SPEC_KEYS", "prerequisite_status", "bind"]

EXPECTED_PREREQUISITES = (("source", "source_state", "two_rim.check.source", 2, SOURCE_CLAIMS),
                          ("material", "material_state", "two_rim.check.material", 2, MATERIAL_CLAIMS),
                          ("cut", "cut_state", "two_rim.check.cut", 1, CUT_CLAIMS))
SPEC_KEYS = frozenset({"kind", "definition", "material_state", "material_identity", "source_state", "cut_state",
                       "seam", "delta", "orientation", "normalization"})
STATE_KINDS = {"source_state": "two_rim.source", "material_state": "two_rim.material", "cut_state": "two_rim.cut"}


def prerequisite_status(run, spec) -> dict:
    rows, problems = [], []
    records = {evidence_id(e): e for e in run.evidence}
    for role, key, checker, version, claims in EXPECTED_PREREQUISITES:
        subject = spec.get(key)
        if not isinstance(subject, str):
            for claim in claims:
                rows.append({"role": role, "claim": claim, "subject": subject, "checker": checker,
                             "checker_version": version, "outcome": "not_run", "reason": "no subject hash",
                             "evidence": [], "invalid": [], "problems": ["no subject hash in the spec"]})
                problems.append(f"{role}: {claim} has no subject")
            continue
        reqs = [Requirement(c, subject, methods=("exact_computation",), coverage="all") for c in claims]
        summary = run.summarize(reqs, expected_tolerances=None)
        for req in summary["requirements"]:
            row = {"role": role, "claim": req["claim"], "subject": subject, "checker": checker,
                   "checker_version": version, "outcome": req["outcome"], "reason": req["reason"],
                   "evidence": req["evidence"], "invalid": req["invalid"], "problems": []}
            for eid in req["evidence"]:
                rec = records.get(eid)
                if rec is None:
                    row["problems"].append(f"evidence {eid} is not a record of this Run")
                elif rec["checker"] != checker or rec["checker_version"] != version:
                    row["problems"].append(f"evidence {eid} came from {rec['checker']} v{rec['checker_version']}, "
                                           f"not {checker} v{version}")
            if row["outcome"] != "pass" or row["problems"]:
                problems.append(f"{role}: {row['claim']} is {row['outcome']}"
                                + (f" ({'; '.join(row['problems'])})" if row["problems"] else ""))
            rows.append(row)
    return {"source_linked": not problems, "rows": rows, "problems": problems}


def _refusal(kind, problems):
    return {"kind": kind, "problems": list(problems)}


def bind(subject):
    """(model, material_payload, preconditions, refusal). refusal is None only when everything binds."""
    run = subject.run
    spec = dict(subject.spec)
    if set(spec) != SPEC_KEYS:
        return None, None, None, _refusal("subject_binding", [f"spec keys must be {sorted(SPEC_KEYS)}"])
    if content_hash(spec) != subject.id:
        return None, None, None, _refusal("subject_binding", ["subject ID does not match its spec"])
    fixed = {"kind": "ideal_trimmed_development", "definition": DEFINITION, "orientation": ORIENTATION,
             "normalization": NORMALIZATION}
    wrong = [k for k, v in fixed.items() if spec[k] != v]
    if wrong:
        return None, None, None, _refusal("subject_binding", [f"unsupported {k}: {spec[k]!r}" for k in wrong])
    try:
        require_supported_delta(spec["delta"])
    except UnsupportedSubject as exc:
        return None, None, None, _refusal("unsupported_subject", [f"delta: {exc}"])
    states, problems = {}, []
    for key, kind in STATE_KINDS.items():
        h = spec[key]
        try:
            rec = run.get(h)
        except (RecordError, KeyError, TypeError) as exc:
            problems.append(f"{key} {h!r} is not a state of this Run ({exc})")
            continue
        if content_hash(rec) != h:
            problems.append(f"{key}: stored content does not match its hash")
        if rec.get("kind") != kind:
            problems.append(f"{key} has kind {rec.get('kind')!r}, not {kind}")
        states[key] = rec
    if problems:
        return None, None, None, _refusal("subject_binding", problems)
    material, cut = states["material_state"]["payload"], states["cut_state"]["payload"]
    if states["cut_state"]["parent"] != spec["material_state"]:
        problems.append("cut state's parent is not the spec's material state")
    if states["material_state"]["parent"] != spec["source_state"]:
        problems.append("material state's parent is not the spec's source state")
    if material_identity(material) != material.get("identity") or material.get("identity") != spec["material_identity"]:
        problems.append("material identity does not recompute to the spec's material_identity")
    if cut.get("seam") != spec["seam"]:
        problems.append("cut seam differs from the spec's seam")
    if cut.get("material") != material:
        problems.append("the cut's material copy differs from its parent material")
    if problems:
        return None, None, None, _refusal("subject_binding", problems)
    model = model_from_payloads(material, cut, spec["delta"])
    if model != subject.model:
        return None, None, None, _refusal("subject_model_mismatch",
                                          ["the carried model is not the model of the named exact inputs "
                                           "(seam, delta, coordinates, rings, chain, normals or normalization)"])
    pre = preconditions(model, material)
    if pre["problems"]:
        return model, material, pre, _refusal("unsupported_subject", pre["problems"])
    return model, material, pre, None
