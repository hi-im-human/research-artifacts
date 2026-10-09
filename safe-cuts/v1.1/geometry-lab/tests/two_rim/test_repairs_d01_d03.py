"""Stage 2 repairs: D01 source correspondence, D02 record/incidence validation, D03 shape/version."""
import copy

import pytest

from glab.check.two_rim_source import check_material, register_checkers
from glab.core.registry import ActionSpec, Registry, StateDraft
from glab.core.runfile import Run, load_run, replay
from glab.two_rim.actions import register_actions
from glab.two_rim.material import build_material, material_identity
from glab.two_rim.source import normalize_source

MIXED = dict(top=[[0, 0], [4, 0], [0, 4]], bottom=[[2, -1], [5, -1], [5, 2], [2, 2]], height="2",
             input_kind="cyclic_boundary")
PRISM = dict(top=[[2, 1], [4, 1], [4, 3], [2, 3]], bottom=[[0, 0], [2, 0], [2, 2], [0, 2]], height="3/2",
             input_kind="cyclic_boundary")
CORR = "two_rim.material.matches_parent_source"
SCHEMA_S, SCHEMA_M = "two_rim.source.record_schema", "two_rim.material.record_schema"
INC = "two_rim.material.incidence_and_rings"


def reg():
    r = Registry()
    register_actions(r)
    register_checkers(r)
    return r


def faulty(r, source_payload=None, mutate=None, accepts="two_rim.source", name="test.material.build"):
    def builder(subject, params, seed):
        src = copy.deepcopy(subject["payload"]) if source_payload is None else source_payload
        m = build_material(src)
        if mutate:
            mutate(m)
        m["identity"] = material_identity(m)
        return StateDraft("two_rim.material", m, "exact")
    r.register_action(ActionSpec(name, 1, accepts, {}, "test-faulty-1", builder))


def outcomes(evs):
    return {e["claim"]: e["outcome"] for e in evs}


def build_run(params=MIXED, builder="two_rim.material.build", r=None):
    r = r or reg()
    run = Run(r)
    s = run.apply("two_rim.source.normalize", 1, copy.deepcopy(params))["output"]
    m = run.apply(builder, 1, {}, s)
    assert m["status"] == "succeeded", m
    return r, run, s, m["output"]


# ---------------------------------------------------------------- D01

def test_correct_correspondence_passes_with_all_claims():
    _, run, s, m = build_run()
    src = outcomes(run.check("two_rim.check.source", 2, s, {}))
    mat = outcomes(run.check("two_rim.check.material", 2, m, {}))
    assert set(src.values()) == {"pass"} and set(mat.values()) == {"pass"}
    assert CORR in mat and SCHEMA_M in mat and SCHEMA_S in src


@pytest.mark.parametrize("change", ["height", "xy"])
def test_wrong_source_fails_only_the_correspondence_claim(change):
    other = copy.deepcopy(MIXED)
    if change == "height":
        other["height"] = "4"
    else:
        other["top"] = [[x + 10, y] for x, y in other["top"]]
        other["bottom"] = [[x + 10, y] for x, y in other["bottom"]]
    r = reg()
    faulty(r, source_payload=normalize_source(**other))
    _, run, s, m = build_run(builder="test.material.build", r=r)
    res = outcomes(run.check("two_rim.check.material", 2, m, {}))
    assert res[CORR] == "fail"
    assert all(v == "pass" for k, v in res.items() if k != CORR)  # the narrow intrinsic claims stay true


def test_reordered_presentation_with_equal_normalized_material_corresponds():
    rev = dict(MIXED, top=MIXED["top"][::-1], bottom=MIXED["bottom"][1:] + MIXED["bottom"][:1])
    r = reg()
    faulty(r, source_payload=normalize_source(**rev))
    _, run, s, m = build_run(builder="test.material.build", r=r)
    assert outcomes(run.check("two_rim.check.material", 2, m, {}))[CORR] == "pass"


def test_material_without_a_source_parent_fails_correspondence():
    r = reg()

    def orphan(subject, params, seed):
        return StateDraft("two_rim.material", build_material(normalize_source(**MIXED)), "exact")
    r.register_action(ActionSpec("test.material.orphan", 1, None, {}, "test-1", orphan))
    run = Run(r)
    m = run.apply("test.material.orphan", 1, {})["output"]
    res = run.check("two_rim.check.material", 2, m, {})
    e = next(e for e in res if e["claim"] == CORR)
    assert e["outcome"] == "fail" and "no parent" in e["receipt"]["problems"][0]


def test_material_whose_parent_is_the_wrong_kind_fails_correspondence():
    r = reg()
    faulty(r, source_payload=normalize_source(**MIXED), accepts="two_rim.material", name="test.material.copy")
    _, run, s, m = build_run(r=r)
    m2 = run.apply("test.material.copy", 1, {}, m)["output"]
    e = next(e for e in run.check("two_rim.check.material", 2, m2, {}) if e["claim"] == CORR)
    assert e["outcome"] == "fail" and "two_rim.source" in e["receipt"]["problems"][0]


def test_direct_call_without_context_is_unknown_not_pass():
    m = build_material(normalize_source(**MIXED))
    res = {c.predicate: c.outcome for c in check_material({"payload": m, "parent": None}, {})}
    assert res[CORR] == "unknown"


def test_correspondence_evidence_goes_stale_when_the_source_changes():
    _, run, s, m = build_run()
    ev = next(e for e in run.check("two_rim.check.material", 2, m, {}) if e["claim"] == CORR)
    assert ev["dependencies"] == [m, s]
    bad = run.get(s)
    bad["payload"]["normalized"]["height"] = "5"
    run._store._tamper_for_tests(s, bad)
    assert run.validate(ev)["status"] == "stale_subject"


def test_correspondence_checks_save_load_and_replay(tmp_path):
    r, run, s, m = build_run()
    run.check("two_rim.check.source", 2, s, {})
    run.check("two_rim.check.material", 2, m, {})
    p = tmp_path / "r.json"
    report = replay(load_run(p, expected_digest=run.save(p)), r)
    assert report["outcome"] == "reproduced" and report["run_digest_reproduced"] is True


def test_v1_checkers_are_no_longer_registered():
    from glab.core.registry import RegistryError
    r = reg()
    for name in ("two_rim.check.source", "two_rim.check.material"):
        with pytest.raises(RegistryError):
            r.checker(name, 1)


# ---------------------------------------------------------------- D02

def _mutated_material_claims(mutate, params=PRISM):
    r = reg()
    faulty(r, mutate=mutate)
    _, run, s, m = build_run(params, builder="test.material.build", r=r)
    return outcomes(run.check("two_rim.check.material", 2, m, {}))


@pytest.mark.parametrize("mutate,claim", [
    (lambda m: m["faces"][1].update(id=m["faces"][0]["id"]), SCHEMA_M),
    (lambda m: m["hinges"].append(copy.deepcopy(m["hinges"][0])), SCHEMA_M),
    (lambda m: m["rim_edges"].append(copy.deepcopy(m["rim_edges"][0])), SCHEMA_M),
    (lambda m: m["vertices"].append(copy.deepcopy(m["vertices"][0])), SCHEMA_M),
    (lambda m: m["caps"].append(copy.deepcopy(m["caps"][0])), SCHEMA_M),
    (lambda m: m["faces"][0].update(entry="E99"), SCHEMA_M),
    (lambda m: m["caps"][0]["boundary"].__setitem__(slice(1, 3), m["caps"][0]["boundary"][2:0:-1]), INC),
    (lambda m: m["caps"][0]["boundary_edges"].__setitem__(slice(0, 2), m["caps"][0]["boundary_edges"][1::-1]), INC),
    (lambda m: m["caps"][1]["boundary"].reverse(), INC),
])
def test_invalid_declarations_and_cap_paths_fail(mutate, claim):
    res = _mutated_material_claims(mutate)
    assert res[claim] == "fail", res


def test_schema_failure_makes_other_material_claims_unknown():
    res = _mutated_material_claims(lambda m: m["faces"][1].update(id=m["faces"][0]["id"]))
    assert res[SCHEMA_M] == "fail" and {v for k, v in res.items() if k != SCHEMA_M} == {"unknown"}


@pytest.mark.parametrize("params", [MIXED, PRISM])
def test_valid_triangles_trapezoids_caps_and_shared_vertices_pass(params):
    _, run, s, m = build_run(params)
    mat = run.get(m)["payload"]
    fan = max(sum(v["id"] in f["boundary"] for f in mat["faces"]) for v in mat["vertices"])
    assert fan >= 2  # repeated references to one vertex are not duplicate declarations
    assert set(outcomes(run.check("two_rim.check.material", 2, m, {})).values()) == {"pass"}


# ---------------------------------------------------------------- D03

def _source_claims(mutate=None, params=MIXED):
    payload = normalize_source(**copy.deepcopy(params))
    if mutate:
        mutate(payload)
    r = reg()
    r.register_action(ActionSpec("test.source.raw", 1, None, {}, "test-1",
                                 lambda s, p, seed: StateDraft("two_rim.source", payload, "exact")))
    run = Run(r)
    h = run.apply("test.source.raw", 1, {})["output"]
    return outcomes(run.check("two_rim.check.source", 2, h, {}))


@pytest.mark.parametrize("mutate", [
    lambda p: p["input"]["top"][0].append(99),
    lambda p: p["input"]["top"][0].pop(),
    lambda p: p["input"]["top"].__setitem__(0, [True, 0]),
    lambda p: p["normalized"]["top"][0].append("99"),
    lambda p: p["normalized"]["top"].__setitem__(0, ["0.0", "0"]),   # non-canonical normalized spelling
    lambda p: p.update(schema="two_rim.source/99"),
    lambda p: p.update(units="metres"),
    lambda p: p["normalization"]["top"].pop("reversed"),
])
def test_source_shape_and_version_violations_fail_and_block_interpretation(mutate):
    res = _source_claims(mutate)
    assert res[SCHEMA_S] == "fail"
    assert {v for k, v in res.items() if k != SCHEMA_S} == {"unknown"}


def test_valid_exact_input_spellings_are_accepted_as_given():
    params = dict(MIXED, top=[["0.0", 0], [" 4 ", "0/1"], ["0", "8/2"]], height="2.0")
    res = _source_claims(params=params)
    assert set(res.values()) == {"pass"}


def test_unknown_material_schema_cannot_pass():
    res = _mutated_material_claims(lambda m: m.update(schema="two_rim.material/99"))
    assert res[SCHEMA_M] == "fail" and "pass" not in {v for k, v in res.items() if k != SCHEMA_M}
