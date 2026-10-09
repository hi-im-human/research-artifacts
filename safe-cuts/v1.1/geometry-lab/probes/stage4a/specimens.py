"""ISOLATED STAGE 4A PROTOTYPE: real Stage 2/3 states and prerequisite evidence, built in a maintained Run.

Read-only use of glab: a fresh Registry with the maintained actions and checkers (the probe registers
nothing of its own) and the normal Run API. Nothing is written under glab/.
"""
from __future__ import annotations

from dataclasses import dataclass

from glab.check.two_rim_development import register_development_checkers
from glab.check.two_rim_source import register_checkers
from glab.core.evidence import evidence_id
from glab.core.registry import Registry
from glab.core.runfile import Run
from glab.two_rim.actions import register_actions
from glab.two_rim.dev_actions import register_development_actions

__all__ = ["SQUARE", "E11", "E11_DELTA", "maintained_registry", "Prepared", "prepare", "prerequisites_complete",
           "float_states"]

SQUARE = {"top": [[0, 0], [0, 2], [2, 2], [2, 0]], "bottom": [[0, 0], [0, 2], [2, 2], [2, 0]], "height": "3",
          "input_kind": "cyclic_boundary"}
# Historical exact eleven-panel source (Codex Forge review at commit-11; SYSTEM-TO-CLAUDE-STAGE-3.md).
E11 = {"top": [[-40, -28], [31, -11], [16, 27], [-15, 50]],
       "bottom": [[-85, 60], [-26, -53], ["1693/100", "-2569/50"], ["564/25", "-4993/100"],
                  ["303/10", "-77/2"], [60, 74], [18, 91]],
       "height": "1/10000", "input_kind": "point_set_hull"}
E11_DELTA = "1/10000"


def maintained_registry() -> Registry:
    reg = Registry()
    register_actions(reg)
    register_checkers(reg)
    register_development_actions(reg)
    register_development_checkers(reg)
    return reg


@dataclass
class Prepared:
    """Run plus state hashes; `prerequisites` is an informational cache of summaries (never trusted)."""
    run: Run
    source: str
    material: str
    cuts: dict
    prerequisites: dict


def _summary(run, evs):
    return [{"id": evidence_id(e), "claim": e["claim"], "outcome": e["outcome"], "checker": e["checker"],
             "checker_version": e["checker_version"], "method": e["method"],
             "validation": run.validate(e)["status"]} for e in evs]


def _succeeded(result):
    if result["status"] != "succeeded":
        raise RuntimeError(f"action attempt did not succeed: {result}")
    return result["output"]


def prepare(params, seams=None, run: Run | None = None) -> Prepared:
    """Source, material and cut states with their registered prerequisite checks (source v2, material v2, cut v1)."""
    run = run or Run(maintained_registry())
    s = _succeeded(run.apply("two_rim.source.normalize", 1, dict(params)))
    m = _succeeded(run.apply("two_rim.material.build", 1, {}, s))
    prereq = {"source": _summary(run, run.check("two_rim.check.source", 2, s, {})),
              "material": _summary(run, run.check("two_rim.check.material", 2, m, {}))}
    cuts = {}
    for seam in seams or [e["id"] for e in run.get(m)["payload"]["hinges"]]:
        c = _succeeded(run.apply("two_rim.cut.open", 1, {"seam": seam}, m))
        cuts[seam] = c
        prereq[f"cut:{seam}"] = _summary(run, run.check("two_rim.check.cut", 1, c, {}))
    return Prepared(run, s, m, cuts, prereq)


def prerequisites_complete(prepared: Prepared, seam: str):
    """(complete, problems) from the Run's ACTUAL evidence (repair A02); the cached Prepared.prerequisites rows
    are informational only and never consulted here."""
    from .binding import prerequisite_status
    run = prepared.run
    cut = prepared.cuts[seam]
    material = run.get(cut)["parent"]
    source = run.get(material)["parent"] if material is not None else None
    status = prerequisite_status(run, {"source_state": source, "material_state": material, "cut_state": cut})
    return status["source_linked"], status["problems"]


def float_states(prepared: Prepared, seam: str, delta: str):
    """Stage 3 float development and trimmed states with their v2 checks (selection and firewall controls only)."""
    run = prepared.run
    d = _succeeded(run.apply("two_rim.develop.static", 1, {}, prepared.cuts[seam]))
    t = _succeeded(run.apply("two_rim.trim.apply", 1, {"delta": delta}, d))
    dev_ev = run.check("two_rim.check.development", 2, d, {})
    trim_ev = run.check("two_rim.check.trimmed_development", 2, t, {})
    return {"development": d, "trimmed": t, "development_evidence": dev_ev, "trimmed_evidence": trim_ev}
