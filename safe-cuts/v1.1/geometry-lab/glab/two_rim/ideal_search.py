"""Ideal-lane search entry point and the aggregate source_linked_ideal_trimmed_obligations (orchestration).

A separate entry point from search.enumerated_candidate_search: the float lane, its totals and its unknowns are not
changed or called here. For every original hinge it opens the cut, defines the ideal state (two_rim.ideal.define
v1), runs the independent checkers, and then evaluates from evidence only:

- the aggregate `source_linked_ideal_trimmed_obligations`: every source (two_rim.check.source v2), material
  (two_rim.check.material v2, including matches_parent_source), cut (two_rim.check.cut v1) and ideal
  (two_rim.check.ideal_trimmed_development v1) claim on its own subject hash, current, with the expected method,
  coverage and parameters. Exact claims must declare no policy; the two pair claims must declare `expected_policy`.
  Every covering evidence record is resolved and must come from the expected checker name and version.
  Conservative: fail > unknown > not_run > pass.
- the geometric verdict on D (`ideal_geometric_verdict`): pass; fail (a certified interior witness); unknown (valid
  evidence that leaves a pair undecided, never a safety pass); or not_determined (missing, stale, failing, foreign or
  policy-mismatched evidence, or unsupported input). No source-linked geometric verdict is made without complete
  prerequisites, and an unsupported input is never an overlap.

Claim names are literals kept in step with the checkers by tests; this module never imports a checker. This is a
finite scan over the original hinges, not the manuscript's seam selector; a verdict concerns D only, never a float
state.
"""
from __future__ import annotations

from ..core.evidence import Requirement, evidence_id, summarize
from ..core.registry import RegistryError

__all__ = ["AGGREGATE", "SOURCE_OBLIGATIONS", "MATERIAL_OBLIGATIONS", "CUT_OBLIGATIONS", "IDEAL_OBLIGATIONS",
           "IDEAL_POLICY_OBLIGATIONS", "CHECKERS", "VERDICTS", "AGGREGATE_DEFINITION", "ideal_obligations",
           "loaded_ideal_obligations", "ideal_candidate_search"]

AGGREGATE = "source_linked_ideal_trimmed_obligations"
SOURCE_OBLIGATIONS = ("two_rim.source.record_schema", "two_rim.source.height_positive",
                      "two_rim.source.rims_strictly_convex_clockwise", "two_rim.source.normalization_accounts_for_input")
MATERIAL_OBLIGATIONS = ("two_rim.material.record_schema", "two_rim.material.identity_hash",
                        "two_rim.material.facets_match_supporting_plane_oracle", "two_rim.material.incidence_and_rings",
                        "two_rim.material.matches_parent_source")
CUT_OBLIGATIONS = ("two_rim.cut.record_schema", "two_rim.cut.material_copy_matches_parent",
                   "two_rim.cut.exactly_one_original_seam_open", "two_rim.cut.face_coverage_complete_unique",
                   "two_rim.cut.glue_classes_match_cut_relation")
IDEAL_OBLIGATIONS = ("two_rim.ideal.record_schema", "two_rim.ideal.cut_copy_matches_parent",
                     "two_rim.ideal.delta_in_supported_domain", "two_rim.ideal.local_premises",
                     "two_rim.ideal.retained_hinge_sides_opposite",
                     "two_rim.ideal.retained_neighbours_interiors_disjoint",
                     "two_rim.ideal.remaining_pairs_interiors_disjoint", "two_rim.ideal.pair_coverage_complete")
_THEOREM_S, _REMAINING = IDEAL_OBLIGATIONS[5], IDEAL_OBLIGATIONS[6]
IDEAL_POLICY_OBLIGATIONS = (_THEOREM_S, _REMAINING)
_COVERAGE = {IDEAL_OBLIGATIONS[4]: "retained_hinge_pairs", _THEOREM_S: "retained_hinge_pairs",
             _REMAINING: "pairs_not_decided_by_theorem_s"}
CHECKERS = {"source": ("two_rim.check.source", 2), "material": ("two_rim.check.material", 2),
            "cut": ("two_rim.check.cut", 1), "ideal": ("two_rim.check.ideal_trimmed_development", 1)}
_ROLES = (("source", SOURCE_OBLIGATIONS), ("material", MATERIAL_OBLIGATIONS), ("cut", CUT_OBLIGATIONS),
          ("ideal", IDEAL_OBLIGATIONS))
_KINDS = (("ideal", "two_rim.ideal_trimmed_development"), ("cut", "two_rim.cut"), ("material", "two_rim.material"),
          ("source", "two_rim.source"))
_RANK = {"pass": 0, "not_run": 1, "unknown": 2, "fail": 3}

VERDICTS = {
    "pass": "every pair of D certified disjoint (Theorem S on the retained hinges, certified separating axes "
            "elsewhere), with complete current source, material, cut and ideal evidence from the expected checkers "
            "under the expected policy",
    "fail": "a certified interior witness: two faces of D overlap, with every non-pair obligation current and passing",
    "unknown": "valid current evidence that leaves at least one pair undecided; never a safety pass",
    "not_determined": "no source-linked geometric verdict: required evidence is missing, stale, failing, from an "
                      "unexpected checker or under another policy, or the input is unsupported; never an overlap "
                      "and never a pass",
}
AGGREGATE_DEFINITION = {
    "name": AGGREGATE,
    "scope": "source-linked: the Stage 2 source and material bundles, the cut claims and every ideal claim, each on "
             "its own subject hash; the float development and trimmed totals are separate and unchanged",
    "requirements": {role: list(claims) for role, claims in _ROLES},
    "checkers": {role: {"name": n, "version": v} for role, (n, v) in CHECKERS.items()},
    "methods": {"default": "exact_computation", _REMAINING: "rigorous_enclosure"},
    "coverage": dict(_COVERAGE, default="all"),
    "policy": "exact claims declare none; the claims in policy_claims must declare exactly the expected policy",
    "policy_claims": list(IDEAL_POLICY_OBLIGATIONS),
    "verdicts": VERDICTS,
}


def _subjects(get_state, ideal_hash):
    """ideal -> cut -> material -> source hashes along the actual parent links; None where the chain breaks."""
    out, h = {role: None for role, _ in _KINDS}, ideal_hash
    for role, kind in _KINDS:
        if h is None:
            break
        try:
            state = get_state(h)
        except (KeyError, TypeError, ValueError):
            break
        if state["kind"] != kind:
            break
        out[role], h = h, state["parent"]
    return out


def _requirements(subject, claims):
    return [Requirement(c, subject, methods=("rigorous_enclosure",) if c == _REMAINING else ("exact_computation",),
                        params={}, coverage=_COVERAGE.get(c, "all")) for c in claims]


def _evaluate(get_state, evidence, summarize_fn, ideal_hash, expected_policy):
    subjects = _subjects(get_state, ideal_hash)
    by_id = {evidence_id(e): e for e in evidence}
    rows = []
    for role, claims in _ROLES:
        reqs = _requirements(subjects[role], claims)
        found = {}
        for policy, subset in ((None, [r for r in reqs if r.claim not in IDEAL_POLICY_OBLIGATIONS]),
                               (expected_policy, [r for r in reqs if r.claim in IDEAL_POLICY_OBLIGATIONS])):
            if subset:
                found.update({row["claim"]: row for row in summarize_fn(subset, policy)["requirements"]})
        name, version = CHECKERS[role]
        for claim in claims:
            row = dict(found[claim], role=role, checker=name, checker_version=version, identity_problems=[])
            for eid in row["evidence"]:
                rec = by_id.get(eid)
                if rec is None:
                    row["identity_problems"].append(f"evidence {eid} is not a record of this run")
                elif (rec["checker"], rec["checker_version"]) != (name, version):
                    row["identity_problems"].append(f"evidence {eid} came from {rec['checker']} "
                                                    f"v{rec['checker_version']}, not {name} v{version}")
            rows.append(row)

    def effective(r):
        return "unknown" if r["identity_problems"] else r["outcome"]

    def usable(r):
        return bool(r["evidence"]) and r["reason"] == "" and not r["identity_problems"]
    reasons = [f"{r['role']}: {r['claim']}: " + (r["reason"] or "; ".join(r["identity_problems"]))
               for r in rows if not usable(r)]
    reasons += [f"{r['role']}: {r['claim']} is {r['outcome']}" for r in rows
                if usable(r) and r["claim"] not in IDEAL_POLICY_OBLIGATIONS and r["outcome"] != "pass"]
    pair = {r["claim"]: r for r in rows if r["claim"] in IDEAL_POLICY_OBLIGATIONS}
    if reasons:
        verdict = "not_determined"
    elif pair[_REMAINING]["outcome"] == "fail":
        verdict = "fail"
    elif pair[_THEOREM_S]["outcome"] == "pass" and pair[_REMAINING]["outcome"] == "pass":
        verdict = "pass"
    else:
        verdict = "unknown"
    return {"aggregate": AGGREGATE, "subjects": subjects,
            "outcome": max((effective(r) for r in rows), key=_RANK.__getitem__),
            "requirements": rows, "identity_problems": [p for r in rows for p in r["identity_problems"]],
            "ideal_geometric_verdict": {"verdict": verdict, "subject": ideal_hash, "reasons": reasons,
                                        "meaning": VERDICTS[verdict]}}


def ideal_obligations(run, ideal_hash, *, expected_policy) -> dict:
    """The aggregate and the geometric verdict for one ideal state of a Run, from its current evidence only."""
    return _evaluate(run.get, run.evidence, lambda reqs, policy: run.summarize(reqs, expected_tolerances=policy),
                     ideal_hash, expected_policy)


def loaded_ideal_obligations(loaded, registry, ideal_hash, *, expected_policy) -> dict:
    """The same evaluation for a loaded run file, validated against `registry` (stale revisions do not count)."""
    store, record = loaded.store, loaded.record
    return _evaluate(store.get, record["evidence"],
                     lambda reqs, policy: summarize(record["evidence"], reqs, store, registry,
                                                    expected_tolerances=policy), ideal_hash, expected_policy)


def _checked(run, role, subject):
    name, version = CHECKERS[role]
    try:
        return {"subject": subject, "status": "checked",
                "claims": {e["claim"]: e["outcome"] for e in run.check(name, version, subject, {})}}
    except RegistryError as exc:   # the rejected attempt stays in the run history
        return {"subject": subject, "status": "rejected", "reason": str(exc), "claims": {}}


def ideal_candidate_search(run, material_hash: str, delta, *, expected_policy, seams=None) -> dict:
    """Cut and define the ideal state at every original hinge (or `seams`), run every checker, report per seam."""
    state = run.get(material_hash)
    material = state["payload"]
    parent = run.get(state["parent"]) if state["parent"] is not None else None
    source_hash = state["parent"] if parent is not None and parent["kind"] == "two_rim.source" else None
    prerequisites = {"material": _checked(run, "material", material_hash)}
    prerequisites["source"] = _checked(run, "source", source_hash) if source_hash is not None else \
        {"subject": None, "status": "no_source_parent", "claims": {},
         "reason": "the material's parent is not a two_rim.source state"}
    rows = []
    for seam in seams or [e["id"] for e in material["hinges"]]:
        c = run.apply("two_rim.cut.open", 1, {"seam": seam}, material_hash)
        i = run.apply("two_rim.ideal.define", 1, {"delta": delta}, c["output"]) if c["status"] == "succeeded" else None
        row = {"seam": seam, "cut": c["output"], "ideal": None}
        if i is None or i["status"] != "succeeded":
            reason = "an action attempt did not succeed (for example an unsupported delta): no ideal state exists " \
                     "and nothing is decided; see the run history"
            row.update({"failure": reason, AGGREGATE: "not_run",
                        "ideal_geometric_verdict": {"verdict": "not_determined", "subject": None, "reasons": [reason],
                                                    "meaning": VERDICTS["not_determined"]}})
            rows.append(row)
            continue
        row["ideal"] = i["output"]
        row["cut_claims"] = _checked(run, "cut", c["output"])["claims"]
        row["ideal_claims"] = _checked(run, "ideal", i["output"])["claims"]
        ob = ideal_obligations(run, i["output"], expected_policy=expected_policy)
        row.update({AGGREGATE: ob["outcome"], "ideal_geometric_verdict": ob["ideal_geometric_verdict"],
                    "obligations": ob})
        rows.append(row)
    return {"label": "ideal_candidate_search",
            "disclaimer": "finite scan of the original hinges on the ideal trimmed development D (exact inputs, "
                          "Theorem S and rational-interval certificates); not the manuscript's extremal selector; a "
                          "verdict concerns D only, never a float state; unknown or not_determined is not a "
                          "refutation of any theorem",
            "material": material_hash, "source": source_hash, "delta": delta, "prerequisites": prerequisites,
            "aggregate_definition": AGGREGATE_DEFINITION, "expected_policy": expected_policy, "results": rows}
