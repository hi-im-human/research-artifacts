"""Task 2: explicit versioned registry; every attempt recorded; parents never mutated."""
import pytest

from glab.core.records import content_hash
from glab.core.registry import ActionSpec, Param, Registry, RegistryError, StateDraft
from glab.core.runfile import Run
from tests.core.toy import REV, registry


@pytest.fixture
def run():
    return Run(registry())


def source(run, value="3"):
    rec = run.apply("toy.int.source", 1, {"value": value})
    assert rec["status"] == "succeeded", rec
    return rec["output"]


def test_two_actions_create_new_snapshots(run):
    a = source(run, "3")
    rec = run.apply("toy.int.add", 1, {"k": 4}, a)
    assert rec["status"] == "succeeded" and rec["input"] == a
    b = rec["output"]
    assert run.get(b) == {"schema": "glab.state/1", "kind": "toy.int", "parent": a,
                          "representation": "exact", "payload": {"value": "7"}}
    assert run.get(a)["payload"] == {"value": "3"}
    assert [r["seq"] for r in run.actions] == [0, 1]
    assert rec["implementation_revision"] == REV and rec["seed"] is None and rec["failure"] is None


@pytest.mark.parametrize("name,version,params,msg", [
    ("toy.int.rotate", 1, {}, "unknown action"),
    ("toy.int.add", 2, {"k": 1}, "unknown version"),
    ("toy.int.add", True, {"k": 1}, "version"),
    ("toy.int.add", "1", {"k": 1}, "version"),
    ("toy.int.add", 1, {"k": 1, "code": "__import__('os').system('x')"}, "unexpected parameter"),
    ("toy.int.add", 1, {}, "missing parameter"),
    ("toy.int.add", 1, {"k": "1"}, "parameter 'k'"),
    ("toy.int.add", 1, {"k": True}, "parameter 'k'"),
    ("toy.int.add", 1, {"k": 1.0}, "parameter 'k'"),
    ("toy.int.add", 1, ["k", 1], "parameters must be an object"),
])
def test_rejections_are_recorded_not_lost(run, name, version, params, msg):
    a = source(run)
    rec = run.apply(name, version, params, a)
    assert rec["status"] == "rejected" and rec["output"] is None
    assert msg in rec["failure"]["message"] and rec["failure"]["stage"] == "validation"
    assert run.actions[-1] == rec and len(run.actions) == 2


def test_incompatible_input_kind_and_bad_inputs_rejected(run):
    a = source(run, "4")
    f = run.apply("toy.int.halve_float", 1, {}, a)["output"]
    assert run.apply("toy.int.add", 1, {"k": 1}, f)["failure"]["message"].startswith("toy.int.add v1 accepts toy.int")
    assert run.apply("toy.int.source", 1, {"value": "1"}, a)["status"] == "rejected"  # source takes no input
    assert run.apply("toy.int.add", 1, {"k": 1}, None)["status"] == "rejected"
    assert run.apply("toy.int.add", 1, {"k": 1}, "sha256:" + "0" * 64)["status"] == "rejected"
    assert run.apply("toy.int.add", 1, {"k": 1}, a, seed=True)["status"] == "rejected"
    assert run.apply("toy.int.source", 1, {"value": 0.5})["status"] == "rejected"  # float literal


def test_failed_construction_is_retained_with_no_output(run):
    a = source(run)
    for name, kind in (("toy.int.explode", "RuntimeError"), ("toy.int.bad_draft", "RecordError")):
        rec = run.apply(name, 1, {}, a)
        assert rec["status"] == "failed" and rec["output"] is None
        assert rec["failure"]["stage"] == "execution" and rec["failure"]["type"] == kind
    rec = run.apply("toy.int.divide", 1, {"d": 0}, a)
    assert rec["status"] == "failed" and rec["failure"]["type"] == "ZeroDivisionError"
    assert [r["status"] for r in run.actions] == ["succeeded", "failed", "failed", "failed"]


def test_callback_cannot_mutate_retained_parent(run):
    a = source(run, "3")
    before = run.get(a)
    rec = run.apply("toy.int.mutate_input", 1, {}, a)
    assert rec["status"] == "succeeded"
    assert run.get(a) == before and content_hash(run.get(a)) == a


def test_returned_records_are_copies(run):
    a = source(run)
    run.actions[0]["status"] = "edited"
    run.get(a)["payload"]["value"] = "edited"
    assert run.actions[0]["status"] == "succeeded" and run.get(a)["payload"]["value"] == "3"


def test_seed_is_recorded(run):
    a = source(run)
    assert run.apply("toy.int.add", 1, {"k": 1}, a, seed=42)["seed"] == 42


def test_registry_rejects_duplicates_and_bad_specs():
    r = Registry()
    spec = ActionSpec("x.y", 1, None, {}, "rev", lambda s, p, seed: StateDraft("x", {}, "exact"))
    r.register_action(spec)
    with pytest.raises(RegistryError, match="already registered"):
        r.register_action(spec)
    for bad in (ActionSpec("x.z", True, None, {}, "rev", spec.fn), ActionSpec("x.z", 0, None, {}, "rev", spec.fn),
                ActionSpec("", 1, None, {}, "rev", spec.fn), ActionSpec("x.z", 1, None, {"p": int}, "rev", spec.fn),
                ActionSpec("x.z", 1, None, {}, "", spec.fn)):
        with pytest.raises(RegistryError):
            r.register_action(bad)
    assert r.identities() == {"actions": {"x.y@1": "rev"}, "checkers": {}}


def test_param_enum_and_exact():
    Param.enum(["a", "b"]).check("k", "a")
    with pytest.raises(RegistryError):
        Param.enum(["a", "b"]).check("k", "c")
    Param.exact().check("k", "1/3")
    with pytest.raises(RegistryError):
        Param.exact().check("k", 0.25)
