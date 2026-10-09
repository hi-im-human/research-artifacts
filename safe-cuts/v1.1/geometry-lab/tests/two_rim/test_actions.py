"""Stage 2 task 4: registered source/material actions, recorded checks, save/load/replay."""
import copy

import pytest

from glab.check.two_rim_source import register_checkers
from glab.core.evidence import Requirement, summarize
from glab.core.registry import Registry
from glab.core.runfile import Run, load_run, replay
from glab.two_rim.actions import register_actions

MIXED = {"top": [[0, 0], [4, 0], [0, 4]], "bottom": [[2, -1], [5, -1], [5, 2], [2, 2]], "height": "2",
         "input_kind": "cyclic_boundary"}
from glab.check.two_rim_source import MATERIAL_CLAIMS, SOURCE_CLAIMS  # v2: incl. record_schema, correspondence


def registry():
    reg = Registry()
    register_actions(reg)
    register_checkers(reg)
    return reg


def build(run, params=MIXED):
    s = run.apply("two_rim.source.normalize", 1, params)
    assert s["status"] == "succeeded", s
    m = run.apply("two_rim.material.build", 1, {}, s["output"])
    assert m["status"] == "succeeded", m
    return s["output"], m["output"]


def requirements(s, m):
    return [Requirement(c, s) for c in SOURCE_CLAIMS] + [Requirement(c, m) for c in MATERIAL_CLAIMS]


def test_source_then_material_with_independent_checks():
    run = Run(registry())
    s, m = build(run)
    assert run.get(m)["parent"] == s and run.get(s)["kind"] == "two_rim.source"
    assert run.get(m)["kind"] == "two_rim.material" and run.get(m)["representation"] == "exact"
    run.check("two_rim.check.source", 2, s, {})
    ev = run.check("two_rim.check.material", 2, m, {})
    assert all(e["dependencies"] == [m, s] for e in ev)
    out = run.summarize(requirements(s, m))
    assert out["outcome"] == "pass" and out["verified"] is True


def test_save_load_replay_and_unchanged_parents(tmp_path):
    reg = registry()
    run = Run(reg)
    s, m = build(run)
    before = copy.deepcopy(run.get(s))
    run.check("two_rim.check.source", 2, s, {})
    run.check("two_rim.check.material", 2, m, {})
    assert run.get(s) == before
    p = tmp_path / "run.json"
    digest = run.save(p)
    loaded = load_run(p, expected_digest=digest)
    as_loaded = summarize(loaded.record["evidence"], requirements(s, m), loaded.store, reg)
    assert as_loaded["outcome"] == "pass" and as_loaded["verified"] is False
    report = replay(loaded, reg)
    assert report["outcome"] == "reproduced" and report["run_digest_reproduced"] is True
    assert report["run"].summarize(requirements(s, m))["verified"] is True


def test_reversed_presentation_same_identity_different_history():
    run = Run(registry())
    s1, m1 = build(run)
    rev = dict(MIXED, top=MIXED["top"][::-1], bottom=MIXED["bottom"][1:] + MIXED["bottom"][:1])
    s2, m2 = build(run, rev)
    assert s1 != s2 and m1 != m2
    assert run.get(m1)["payload"]["identity"] == run.get(m2)["payload"]["identity"]
    strip = lambda st: {k: v for k, v in st["payload"].items()}
    assert strip(run.get(m1)) == strip(run.get(m2))


def test_domain_violation_is_a_failed_attempt_and_type_violation_is_rejected(tmp_path):
    reg = registry()
    run = Run(reg)
    failed = run.apply("two_rim.source.normalize", 1, dict(MIXED, top=[[0, 0], [4, 0, 1], [0, 4]]))
    assert failed["status"] == "failed" and failed["failure"]["type"] == "SourceInputError"
    rejected = run.apply("two_rim.source.normalize", 1, dict(MIXED, top=[[0, 0], [4, 0.5], [0, 4]]))
    assert rejected["status"] == "rejected" and "top[1][1]" in rejected["failure"]["message"]
    reflex = run.apply("two_rim.source.normalize", 1, dict(MIXED, top=[[0, 0], [4, 0], [1, 1], [0, 4]]))
    assert reflex["status"] == "failed" and "not strictly convex" in reflex["failure"]["message"]
    p = tmp_path / "r.json"
    report = replay(load_run(p, expected_digest=run.save(p)), reg)
    assert report["outcome"] == "reproduced"


def test_material_build_requires_a_source_state():
    run = Run(registry())
    s, m = build(run)
    assert run.apply("two_rim.material.build", 1, {}, m)["status"] == "rejected"
    assert run.apply("two_rim.material.build", 1, {"x": 1}, s)["status"] == "rejected"


def test_checker_rejects_wrong_kind():
    from glab.core.registry import RegistryError
    run = Run(registry())
    s, m = build(run)
    with pytest.raises(RegistryError):
        run.check("two_rim.check.material", 2, s, {})
    assert run.checks[-1]["status"] == "rejected"
