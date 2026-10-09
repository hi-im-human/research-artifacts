"""Test-side exporter: a maintained Run's ideal lane as a re-check bundle (schema two_rim.ideal.recheck_bundle/1).

For each seam the bundle carries the ideal state and its whole ancestor chain (cut, material, source) as stored
records keyed by their hashes, and the ideal checker's evidence records of the latest check attempt on that state.
Nothing is recomputed or summarized here; the re-checker binds to these records and re-derives everything else.
"""
from __future__ import annotations

__all__ = ["BUNDLE_SCHEMA", "IDEAL_CHECKER", "ideal_bundle"]

BUNDLE_SCHEMA = "two_rim.ideal.recheck_bundle/1"
IDEAL_CHECKER = "two_rim.check.ideal_trimmed_development"


def ideal_bundle(run, ideals: dict) -> dict:
    """ideals: {seam: ideal state hash}. Each ideal state must have been checked in `run`."""
    out = {"schema": BUNDLE_SCHEMA,
           "label": "maintained ideal lane: stored states and ideal-checker evidence, for an independent re-check",
           "states": {}, "seams": {}}
    evidence = run.evidence
    for seam, ideal in ideals.items():
        h = ideal
        while h is not None:
            record = run.get(h)
            out["states"][h] = record
            h = record["parent"]
        mine = [e for e in evidence if e["subject"] == ideal and e["checker"] == IDEAL_CHECKER]
        last = max(e["attempt"] for e in mine)
        out["seams"][seam] = {"ideal_state": ideal, "evidence": [e for e in mine if e["attempt"] == last]}
    return out
