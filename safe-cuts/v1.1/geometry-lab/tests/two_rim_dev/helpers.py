"""Shared Stage 3 test helpers: registries, fixtures and small run builders."""
from __future__ import annotations

import json
from pathlib import Path

from glab.check.two_rim_development import register_development_checkers
from glab.check.two_rim_source import register_checkers
from glab.core.registry import Registry
from glab.core.runfile import Run
from glab.two_rim.actions import register_actions
from glab.two_rim.dev_actions import register_development_actions

HERE = Path(__file__).resolve().parent
FIXTURE_DIR = HERE.parent / "two_rim" / "fixtures"
RENAME = {"cyclic_convex_polygon": "cyclic_boundary", "point_set_hull": "point_set_hull"}

# Historical exact eleven-panel source (Codex Forge review at commit-11; SYSTEM-TO-CLAUDE-STAGE-3.md).
E11 = {"top": [[-40, -28], [31, -11], [16, 27], [-15, 50]],
       "bottom": [[-85, 60], [-26, -53], ["1693/100", "-2569/50"], ["564/25", "-4993/100"],
                  ["303/10", "-77/2"], [60, 74], [18, 91]],
       "height": "1/10000", "input_kind": "point_set_hull"}
E11_DELTA = "1/10000"


def fixture(name):
    p = json.loads((FIXTURE_DIR / f"{name}.json").read_text(encoding="utf-8"))["params"]
    return dict(p, input_kind=RENAME[p["input_kind"]])


def registry():
    reg = Registry()
    register_actions(reg)
    register_checkers(reg)
    register_development_actions(reg)
    register_development_checkers(reg)
    return reg


def material(run, params):
    s = run.apply("two_rim.source.normalize", 1, params)
    assert s["status"] == "succeeded", s
    m = run.apply("two_rim.material.build", 1, {}, s["output"])
    assert m["status"] == "succeeded", m
    return s["output"], m["output"]


def developed(run, params, seam="E0", delta=None):
    s, m = material(run, params)
    c = run.apply("two_rim.cut.open", 1, {"seam": seam}, m)
    assert c["status"] == "succeeded", c
    d = run.apply("two_rim.develop.static", 1, {}, c["output"])
    assert d["status"] == "succeeded", d
    out = {"source": s, "material": m, "cut": c["output"], "development": d["output"]}
    if delta is not None:
        t = run.apply("two_rim.trim.apply", 1, {"delta": delta}, d["output"])
        assert t["status"] == "succeeded", t
        out["trimmed"] = t["output"]
    return out


def outcomes(evs):
    return {e["claim"]: e["outcome"] for e in evs}


def new_run():
    return Run(registry())
