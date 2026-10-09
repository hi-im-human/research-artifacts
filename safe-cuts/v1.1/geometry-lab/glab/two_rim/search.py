"""Enumerated original-seam search (generator-side orchestration through the Run API).

This is a SEARCH over every original lateral hinge with independent checks, not the manuscript's
extremal-seam selector. A failed or inconclusive scan is not a refutation of any theorem.

Two kinds of total per seam (Stage 3 repair S01):
- local totals (`full_obligations`, `trimmed_obligations`): the chain from the material down (cut,
  development, trim). They say nothing about whether the material matches its source.
- source-linked totals (`source_linked_full_obligations`, `source_linked_trimmed_obligations`): the local
  total plus the Stage 2 source and material bundles (including `matches_parent_source`), each evaluated
  by its registered checker on its own subject hash. Missing, unknown, stale or failed prerequisite
  evidence never yields a pass. Nothing is inferred from ancestry hashes or action success.
The trimmed totals inherit the development's exact record/copy contracts, never its full-domain
numerical verdicts: a trim is a smaller domain and may remove an overlap.
"""
from __future__ import annotations

from ..core.evidence import UNSET, Requirement
from ..core.registry import RegistryError

__all__ = ["enumerated_candidate_search", "CUT_OBLIGATIONS", "DEVELOPMENT_OBLIGATIONS", "TRIM_OBLIGATIONS",
           "SOURCE_OBLIGATIONS", "MATERIAL_OBLIGATIONS", "DEVELOPMENT_EXACT_OBLIGATIONS"]

# Claim names of the independent checkers (kept in step with glab.check by tests; never imported here).
SOURCE_OBLIGATIONS = ("two_rim.source.record_schema", "two_rim.source.height_positive",
                      "two_rim.source.rims_strictly_convex_clockwise", "two_rim.source.normalization_accounts_for_input")
MATERIAL_OBLIGATIONS = ("two_rim.material.record_schema", "two_rim.material.identity_hash",
                        "two_rim.material.facets_match_supporting_plane_oracle", "two_rim.material.incidence_and_rings",
                        "two_rim.material.matches_parent_source")
CUT_OBLIGATIONS = ("two_rim.cut.record_schema", "two_rim.cut.material_copy_matches_parent",
                   "two_rim.cut.exactly_one_original_seam_open", "two_rim.cut.face_coverage_complete_unique",
                   "two_rim.cut.glue_classes_match_cut_relation")
DEVELOPMENT_EXACT_OBLIGATIONS = ("two_rim.development.record_schema", "two_rim.development.cut_copy_matches_parent")
_NUMERICAL = ("two_rim.development.face_maps_rigid", "two_rim.development.no_reflected_face",
              "two_rim.development.nonempty_face_images", "two_rim.development.retained_hinges_and_glued_vertices_agree",
              "two_rim.development.face_interiors_disjoint_all_pairs")
DEVELOPMENT_OBLIGATIONS = DEVELOPMENT_EXACT_OBLIGATIONS + _NUMERICAL
TRIM_OBLIGATIONS = ("two_rim.trim.record_schema", "two_rim.trim.maps_identical_to_parent",
                    "two_rim.trim.domain_is_exact_band") + _NUMERICAL

# Registered checker versions this search runs (development/trim v2 since the S02-S04 repair).
CHECKERS = {"source": ("two_rim.check.source", 2), "material": ("two_rim.check.material", 2),
            "cut": ("two_rim.check.cut", 1), "development": ("two_rim.check.development", 2),
            "trimmed": ("two_rim.check.trimmed_development", 2)}
_RANK = {"pass": 0, "not_run": 1, "unknown": 2, "fail": 3}

AGGREGATES = {
    "full_obligations": {"scope": "local: cut and full development; no source correspondence",
                         "requirements": {"cut": list(CUT_OBLIGATIONS), "development": list(DEVELOPMENT_OBLIGATIONS)}},
    "trimmed_obligations": {"scope": "local: cut, the development's exact record/copy claims, and the trimmed "
                                     "domain; no source correspondence",
                            "requirements": {"cut": list(CUT_OBLIGATIONS),
                                             "development": list(DEVELOPMENT_EXACT_OBLIGATIONS),
                                             "trimmed": list(TRIM_OBLIGATIONS)}},
    "source_linked_full_obligations": {
        "scope": "source-linked: source and material bundles plus the local full total",
        "requirements": {"source": list(SOURCE_OBLIGATIONS), "material": list(MATERIAL_OBLIGATIONS),
                         "cut": list(CUT_OBLIGATIONS), "development": list(DEVELOPMENT_OBLIGATIONS)}},
    "source_linked_trimmed_obligations": {
        "scope": "source-linked: source and material bundles plus the local trimmed total (never the full-domain "
                 "numerical verdicts)",
        "requirements": {"source": list(SOURCE_OBLIGATIONS), "material": list(MATERIAL_OBLIGATIONS),
                         "cut": list(CUT_OBLIGATIONS), "development": list(DEVELOPMENT_EXACT_OBLIGATIONS),
                         "trimmed": list(TRIM_OBLIGATIONS)}},
}


def _claims(evs):
    return {e["claim"]: e["outcome"] for e in evs}


def _prerequisite(run, role, subject):
    name, version = CHECKERS[role]
    try:
        return {"subject": subject, "status": "checked", "claims": _claims(run.check(name, version, subject, {}))}
    except RegistryError as exc:  # the rejected attempt stays in the run history
        return {"subject": subject, "status": "rejected", "reason": str(exc), "claims": {}}


def _outcome(run, subjects, requirements, numerical_tolerances):
    """Conservative total. Numerical claims are held to the caller's expected policy when one is given."""
    if any(subjects.get(role) is None for role in requirements):
        return "not_run"
    exact, numerical = [], []
    for role, claims in requirements.items():
        for c in claims:
            (numerical if c in _NUMERICAL else exact).append(Requirement(c, subjects[role]))
    if numerical_tolerances is UNSET:
        return run.summarize(exact + numerical)["outcome"]
    parts = [run.summarize(exact, expected_tolerances=None)["outcome"],
             run.summarize(numerical, expected_tolerances=numerical_tolerances)["outcome"]]
    return max(parts, key=_RANK.__getitem__)


def enumerated_candidate_search(run, material_hash: str, delta, *, expected_numerical_tolerances=UNSET) -> dict:
    """Cut, develop and trim at every original hinge; run every checker; report local and source-linked totals.

    expected_numerical_tolerances: optional policy that numerical evidence must declare (Claim.tolerances);
    exact claims are then required to declare none.
    """
    state = run.get(material_hash)
    material = state["payload"]
    parent = run.get(state["parent"]) if state["parent"] is not None else None
    source_hash = state["parent"] if parent is not None and parent["kind"] == "two_rim.source" else None
    prerequisites = {"material": _prerequisite(run, "material", material_hash)}
    prerequisites["source"] = _prerequisite(run, "source", source_hash) if source_hash is not None else \
        {"subject": None, "status": "no_source_parent", "claims": {},
         "reason": "the material's parent is not a two_rim.source state"}
    rows = []
    for e in material["hinges"]:
        row = {"seam": e["id"]}
        c = run.apply("two_rim.cut.open", 1, {"seam": e["id"]}, material_hash)
        d = run.apply("two_rim.develop.static", 1, {}, c["output"]) if c["status"] == "succeeded" else None
        t = run.apply("two_rim.trim.apply", 1, {"delta": delta}, d["output"]) \
            if d is not None and d["status"] == "succeeded" else None
        if t is None or t["status"] != "succeeded":
            row["failure"] = "an action attempt did not succeed; see the run history"
            row.update({k: "not_run" for k in AGGREGATES})
            rows.append(row)
            continue
        row.update(cut=c["output"], development=d["output"], trimmed=t["output"])
        row["cut_claims"] = _claims(run.check(*CHECKERS["cut"], c["output"], {}))
        row["full_claims"] = _claims(run.check(*CHECKERS["development"], d["output"], {}))
        row["trimmed_claims"] = _claims(run.check(*CHECKERS["trimmed"], t["output"], {}))
        subjects = {"source": source_hash, "material": material_hash, "cut": c["output"],
                    "development": d["output"], "trimmed": t["output"]}
        for key, spec in AGGREGATES.items():
            row[key] = _outcome(run, subjects, spec["requirements"], expected_numerical_tolerances)
        rows.append(row)
    return {"label": "enumerated_candidate_search",
            "disclaimer": "finite scan of every original hinge with independent numerical checks; not the manuscript's "
                          "extremal selector; unknown or fail is not a refutation of any theorem",
            "material": material_hash, "source": source_hash, "delta": delta, "prerequisites": prerequisites,
            "aggregate_definitions": AGGREGATES, "results": rows}
