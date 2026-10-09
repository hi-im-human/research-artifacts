"""System's bounded Stage 2 review cases for head commit-37.

Run with GLAB_ENGINE pointing at the engine checkout:
  python -m pytest -q /path/to/test_source_boundary.py

These are regression/acceptance requests, not edits to production code.
D01 requests a new source-correspondence predicate in the material checking
bundle; it does not assert that the old three narrower predicates are false.
D02 and D03 exercise declared record/incidence contracts without invalidating
content hashes. Deliberately faulty registered builders stand in for an
implementation defect; no unsafe external code or opaque tampering is used.
"""
from __future__ import annotations

import copy
import os
import sys
from pathlib import Path

import pytest

ENGINE = Path(os.environ.get("GLAB_ENGINE", str(Path.cwd()))).resolve()
sys.path.insert(0, str(ENGINE))

from glab.check.two_rim_source import register_checkers
from glab.core.registry import ActionSpec, Registry, StateDraft
from glab.core.runfile import Run, load_run, replay
from glab.two_rim.actions import register_actions
from glab.two_rim.material import build_material, material_identity
from glab.two_rim.source import normalize_source

SQUARE = [[0, 0], [0, 2], [2, 2], [2, 0]]
BASE = dict(top=SQUARE, bottom=SQUARE, height="3", input_kind="cyclic_boundary")


def new_registry():
    reg = Registry()
    register_actions(reg)
    register_checkers(reg)
    return reg


def material_run(mutator=None, alternate_source=None):
    reg = new_registry()

    def builder(subject, params, seed):
        # Fault injection only. The actual source ancestor is unchanged.
        source = copy.deepcopy(subject["payload"]) if alternate_source is None else alternate_source
        material = build_material(source)
        if mutator is not None:
            mutator(material)
        material["identity"] = material_identity(material)
        return StateDraft("two_rim.material", material, "exact")

    reg.register_action(ActionSpec("review.material.build", 1, "two_rim.source", {}, "review-commit-37", builder))
    run = Run(reg)
    source = run.apply("two_rim.source.normalize", 1, copy.deepcopy(BASE))["output"]
    result = run.apply("review.material.build", 1, {}, source)
    assert result["status"] == "succeeded", result
    material = result["output"]
    assert run.get(material)["parent"] == source
    assert run.get(material)["payload"]["identity"] == material_identity(run.get(material)["payload"])
    return run, reg, source, material


def checked_material(run, source, material):
    source_claims = run.check("two_rim.check.source", 1, source, {})
    assert source_claims and all(e["outcome"] == "pass" for e in source_claims)
    return run.check("two_rim.check.material", 1, material, {})


def assert_not_all_pass(claims):
    assert claims and any(e["outcome"] != "pass" for e in claims), [
        (e["claim"], e["outcome"]) for e in claims
    ]


def test_control_valid_material_remains_accepted(tmp_path):
    run, reg, source, material = material_run()
    claims = checked_material(run, source, material)
    assert claims and all(e["outcome"] == "pass" for e in claims)
    path = tmp_path / "valid.run.json"
    report = replay(load_run(path, expected_digest=run.save(path)), reg)
    assert report["outcome"] == "reproduced" and report["run_digest_reproduced"]


def test_control_changed_vertex_is_detected():
    def move(m):
        m["vertices"][0]["xyz"][0] = "1/3"
    run, _, source, material = material_run(move)
    assert_not_all_pass(checked_material(run, source, material))


@pytest.mark.parametrize("difference", ["height", "xy_coordinates"])
def test_D01_material_must_match_its_actual_source(difference):
    other = copy.deepcopy(BASE)
    if difference == "height":
        other["height"] = "4"
    else:
        other["top"] = [[x + 10, y] for x, y in other["top"]]
        other["bottom"] = [[x + 10, y] for x, y in other["bottom"]]
    alternate = normalize_source(**other)
    run, _, source, material = material_run(alternate_source=alternate)
    actual = run.get(source)["payload"]["normalized"]
    made = run.get(material)["payload"]
    assert (made["height"] != actual["height"] or
            [v["xyz"][:2] for v in made["vertices"] if v["rim"] == "top"] != actual["top"])
    assert_not_all_pass(checked_material(run, source, material))


def duplicate_face(m):
    m["faces"][1]["id"] = m["faces"][0]["id"]


def duplicate_hinge(m):
    m["hinges"].append(copy.deepcopy(m["hinges"][0]))


def duplicate_rim_edge(m):
    m["rim_edges"].append(copy.deepcopy(m["rim_edges"][0]))


def cross_cap(m):
    ring = m["caps"][0]["boundary"]
    ring[1], ring[2] = ring[2], ring[1]


def misalign_cap_edges(m):
    edges = m["caps"][0]["boundary_edges"]
    edges[0], edges[1] = edges[1], edges[0]


@pytest.mark.parametrize("mutation", [duplicate_face, duplicate_hinge, duplicate_rim_edge, cross_cap,
                                       misalign_cap_edges], ids=lambda f: f.__name__)
def test_D02_lossy_containers_must_not_hide_invalid_incidence(mutation):
    run, _, source, material = material_run(mutation)
    assert_not_all_pass(checked_material(run, source, material))


@pytest.mark.parametrize("mutation", ["extra_input_coordinate", "extra_normalized_coordinate", "unknown_schema"])
def test_D03_source_shape_and_version_are_checked(mutation):
    reg = new_registry()
    payload = normalize_source(**copy.deepcopy(BASE))
    if mutation == "extra_input_coordinate":
        payload["input"]["top"][0].append(99)
    elif mutation == "extra_normalized_coordinate":
        payload["normalized"]["top"][0].append("99")
    else:
        payload["schema"] = "two_rim.source/99"
    reg.register_action(ActionSpec("review.source.malformed", 1, None, {}, "review-commit-37",
                                   lambda s, p, seed: StateDraft("two_rim.source", payload, "exact")))
    run = Run(reg)
    made = run.apply("review.source.malformed", 1, {})
    assert made["status"] == "succeeded"
    assert_not_all_pass(run.check("two_rim.check.source", 1, made["output"], {}))


def test_D03_unknown_material_schema_cannot_pass():
    run, _, source, material = material_run(lambda m: m.update(schema="two_rim.material/99"))
    assert_not_all_pass(checked_material(run, source, material))
