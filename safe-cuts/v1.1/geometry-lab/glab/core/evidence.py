"""Per-claim evidence records, reuse validation, and conservative summaries. Standard library only.

A recorded outcome is what a checker reported. Validation status says whether
that record still applies to the stored subject, dependencies, checker revision,
and tolerance policy. "Reproduced" says whether this process produced or
re-executed an identical record. Loading a record never endorses its outcome.
"""
from __future__ import annotations

from dataclasses import dataclass

from .records import RecordError, StateStore, canonical_json, content_hash, is_hash, strict_loads
from .registry import Claim, Registry, RegistryError

__all__ = ["EVIDENCE_SCHEMA", "OUTCOMES", "METHODS", "SUPPORTED_METHODS", "EvidenceError", "make_evidence",
           "evidence_id", "check_evidence_structure", "validate_evidence", "Requirement", "summarize", "UNSET"]

EVIDENCE_SCHEMA = "glab.evidence/2"
OUTCOMES = ("pass", "fail", "unknown", "not_run")
METHODS = ("numerical_diagnostic", "exact_computation", "rigorous_enclosure", "formal_proof")
SUPPORTED_METHODS = ("numerical_diagnostic", "exact_computation", "rigorous_enclosure")
_KEYS = {"schema", "seq", "attempt", "claim", "subject", "dependencies", "outcome", "method", "numeric_domain",
         "representation", "checker", "checker_version", "checker_revision", "params", "tolerances",
         "coverage", "receipt"}
_WORST = {"pass": 0, "not_run": 1, "unknown": 2, "fail": 3}
UNSET = object()


class EvidenceError(ValueError):
    """An evidence record is malformed or claims something this core cannot support."""


def make_evidence(*, seq, attempt, claim: Claim, subject, dependencies, representation, checker, checker_version,
                  checker_revision, params) -> dict:
    if claim.method == "formal_proof":
        raise EvidenceError("formal_proof evidence needs a supported formal verifier; none exists in this core "
                            "(a theorem reference is not a verifier)")
    record = {"schema": EVIDENCE_SCHEMA, "seq": seq, "attempt": attempt, "claim": claim.predicate, "subject": subject,
              "dependencies": list(dependencies), "outcome": claim.outcome, "method": claim.method,
              "numeric_domain": claim.numeric_domain, "representation": representation, "checker": checker,
              "checker_version": checker_version, "checker_revision": checker_revision, "params": params,
              "tolerances": claim.tolerances, "coverage": claim.coverage, "receipt": claim.receipt}
    try:
        # Detach at the capture boundary: nothing the checker still holds can reach the record.
        record = strict_loads(canonical_json(record))
    except RecordError as exc:
        raise EvidenceError(f"evidence content is not JSON: {exc}") from None
    check_evidence_structure(record)
    return record


def evidence_id(record) -> str:
    return content_hash(record)


def check_evidence_structure(record) -> None:
    """Shape and vocabulary only; says nothing about whether the claim holds or still applies."""
    if not isinstance(record, dict) or set(record) != _KEYS:
        raise EvidenceError(f"evidence keys must be {sorted(_KEYS)}")
    if record["schema"] != EVIDENCE_SCHEMA:
        raise EvidenceError(f"unsupported evidence schema {record['schema']!r}")
    for key in ("seq", "attempt"):
        if type(record[key]) is not int or record[key] < 0:
            raise EvidenceError(f"{key} must be a nonnegative int (not bool)")
    if not isinstance(record["claim"], str) or not record["claim"]:
        raise EvidenceError("claim must be a nonempty string")
    if record["outcome"] not in OUTCOMES:
        raise EvidenceError(f"outcome must be one of {OUTCOMES}, got {record['outcome']!r}")
    if record["method"] not in METHODS:
        raise EvidenceError(f"method must be one of {METHODS}, got {record['method']!r}")
    if not is_hash(record["subject"]) or not isinstance(record["dependencies"], list) or \
            not all(is_hash(d) for d in record["dependencies"]):
        raise EvidenceError("subject and dependencies must be state hashes")
    if not record["dependencies"] or record["dependencies"][0] != record["subject"]:
        raise EvidenceError("dependencies must start with the subject")
    for key in ("numeric_domain", "representation", "checker", "checker_revision", "coverage"):
        if not isinstance(record[key], str) or not record[key]:
            raise EvidenceError(f"{key} must be a nonempty string")
    if type(record["checker_version"]) is not int or record["checker_version"] < 1:
        raise EvidenceError("checker_version must be a positive int")
    if not isinstance(record["params"], dict):
        raise EvidenceError("params must be an object")
    try:
        canonical_json(record)
    except RecordError as exc:
        raise EvidenceError(str(exc)) from None


def validate_evidence(record, store: StateStore, registry: Registry, *, expected_tolerances=UNSET,
                      reproduced=frozenset()) -> dict:
    """Whether a recorded claim still applies here. Does not re-run the checker."""
    check_evidence_structure(record)
    rid = evidence_id(record)
    result = {"id": rid, "reproduced": rid in reproduced}
    if record["method"] == "formal_proof":
        return {**result, "status": "unsupported_method", "reason": "no supported formal verifier"}
    try:
        chain = store.validate_chain(record["subject"])
    except RecordError as exc:
        return {**result, "status": "stale_subject", "reason": str(exc)}
    if chain != record["dependencies"]:
        return {**result, "status": "stale_subject", "reason": "dependency closure differs from the stored chain"}
    if store.get(record["subject"])["representation"] != record["representation"]:
        return {**result, "status": "stale_subject", "reason": "subject representation differs"}
    try:
        spec = registry.checker(record["checker"], record["checker_version"])
    except RegistryError as exc:
        return {**result, "status": "checker_mismatch", "reason": str(exc)}
    if spec.revision != record["checker_revision"]:
        return {**result, "status": "checker_mismatch",
                "reason": f"checker revision {record['checker_revision']} != registered {spec.revision}"}
    if expected_tolerances is not UNSET and record["tolerances"] != expected_tolerances:
        return {**result, "status": "policy_mismatch", "reason": "tolerance policy differs"}
    return {**result, "status": "current", "reason": ""}


@dataclass(frozen=True)
class Requirement:
    """A claim required about one exact subject hash. Evidence never transfers between states.

    coverage: exact token the evidence must carry; default "all". None accepts any recorded
    coverage (the caller then owns that choice). Tokens are compared literally; nothing is inferred.
    """
    claim: str
    subject: str
    methods: tuple | None = None
    representations: tuple | None = None
    params: dict | None = None
    coverage: str | None = "all"


def summarize(evidence, requirements, store, registry, *, reproduced=frozenset(),
              expected_tolerances=UNSET) -> dict:
    """Conservative aggregation: fail > unknown > not_run > pass; 'verified' needs in-process reproduction."""
    rows = []
    for req in requirements:
        matching = [e for e in evidence if e["claim"] == req.claim and e["subject"] == req.subject
                    and (req.params is None or e["params"] == req.params)]
        checks = [validate_evidence(e, store, registry, expected_tolerances=expected_tolerances,
                                    reproduced=reproduced) for e in matching]
        usable = [(e, c) for e, c in zip(matching, checks) if c["status"] == "current"]
        invalid = [{"id": c["id"], "status": c["status"], "reason": c["reason"]}
                   for c in checks if c["status"] != "current"]
        outcomes = sorted({e["outcome"] for e, _ in usable})
        covering = [(e, c) for e, c in usable if req.coverage is None or e["coverage"] == req.coverage]
        row = {"claim": req.claim, "subject": req.subject, "required_coverage": req.coverage,
               "evidence": [c["id"] for _, c in covering], "invalid": invalid,
               "reproduced": bool(covering) and all(c["reproduced"] for _, c in covering)}
        if not matching:
            row.update(outcome="not_run", reason="no evidence recorded for this claim and subject")
        elif not usable:
            row.update(outcome="unknown", reason="only invalid or non-current evidence")
        elif len(outcomes) > 1:
            row.update(outcome="unknown", reason=f"conflict between recorded outcomes {outcomes}")
        elif not covering:
            row.update(outcome="unknown", reason=f"no evidence with required coverage {req.coverage!r}; "
                                                 f"recorded {sorted({e['coverage'] for e, _ in usable})}")
        elif req.methods is not None and any(e["method"] not in req.methods for e, _ in covering):
            row.update(outcome="unknown", reason=f"method not in required {list(req.methods)}")
        elif req.representations is not None and any(e["representation"] not in req.representations
                                                     for e, _ in covering):
            row.update(outcome="unknown", reason=f"representation not in required {list(req.representations)}")
        else:
            row.update(outcome=outcomes[0], reason="")
        rows.append(row)
    overall = max((r["outcome"] for r in rows), key=_WORST.__getitem__, default="not_run")
    verified = overall == "pass" and all(r["reproduced"] for r in rows)
    return {"outcome": overall, "verified": verified, "requirements": rows}
