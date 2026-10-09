"""D01 core: opt-in, read-only dependency context for declared contextual checkers."""
import pytest

from glab.core.registry import CheckerSpec, Claim, Registry, RegistryError
from glab.core.runfile import ContextError, DependencyContext, Run, load_run, replay
from tests.core.toy import registry

SEEN = {}


def _parent_value(state, params, ctx):
    SEEN["ctx"] = ctx
    parent = ctx.parent()
    ok = parent is not None and parent["kind"] == "toy.int"
    return [Claim("toy.parent_known", "pass" if ok else "fail", "exact_computation", "exact_rational",
                  receipt={"parent_value": parent["payload"]["value"] if parent else None})]


def _mutating(state, params, ctx):
    p = ctx.parent()
    p["payload"]["value"] = "666"
    again = ctx.parent()
    return [Claim("toy.context_immutable", "pass" if again["payload"]["value"] != "666" else "fail",
                  "exact_computation", "exact_rational")]


def _unrelated(state, params, ctx):
    ctx.get(params["other"])
    return []


def reg_with_context():
    from glab.core.registry import Param
    reg = registry()
    reg.register_checker(CheckerSpec("toy.ctx.parent", 1, "toy.int", {}, "ctx-1", _parent_value, uses_context=True))
    reg.register_checker(CheckerSpec("toy.ctx.mutate", 1, "toy.int", {}, "ctx-1", _mutating, uses_context=True))
    reg.register_checker(CheckerSpec("toy.ctx.unrelated", 1, "toy.int", {"other": Param.str()}, "ctx-1",
                                     _unrelated, uses_context=True))
    return reg


def chain(run):
    a = run.apply("toy.int.source", 1, {"value": "3"})["output"]
    b = run.apply("toy.int.add", 1, {"k": 1}, a)["output"]
    return a, b


def test_uses_context_must_be_a_real_bool():
    reg = Registry()
    for bad in (1, "yes", None):
        with pytest.raises(RegistryError):
            reg.register_checker(CheckerSpec("x.y", 1, "k", {}, "r", lambda s, p, c: [], uses_context=bad))


def test_contextual_checker_reads_only_its_validated_closure():
    run = Run(reg_with_context())
    a, b = chain(run)
    (ev,) = run.check("toy.ctx.parent", 1, b, {})
    assert ev["outcome"] == "pass" and ev["receipt"] == {"parent_value": "3"}
    ctx = SEEN["ctx"]
    assert isinstance(ctx, DependencyContext)
    assert ctx.dependencies == (b, a) and list(ctx.dependencies) == ev["dependencies"]
    assert ctx.get(a)["payload"]["value"] == "3"
    for attr in vars(ctx).values():  # no store, registry or generator reachable from the context
        assert not hasattr(attr, "put") and not hasattr(attr, "register_action")


def test_root_subject_has_no_parent():
    run = Run(reg_with_context())
    a, _ = chain(run)
    (ev,) = run.check("toy.ctx.parent", 1, a, {})
    assert ev["outcome"] == "fail" and ev["receipt"] == {"parent_value": None}


def test_mutation_through_the_context_cannot_reach_the_store():
    run = Run(reg_with_context())
    a, b = chain(run)
    before = run.get(a)
    (ev,) = run.check("toy.ctx.mutate", 1, b, {})
    assert ev["outcome"] == "pass" and run.get(a) == before


def test_unrelated_state_read_is_an_attempt_failure_not_a_claim():
    run = Run(reg_with_context())
    a, b = chain(run)
    other = run.apply("toy.int.source", 1, {"value": "9"})["output"]
    with pytest.raises(ContextError):
        run.check("toy.ctx.unrelated", 1, b, {"other": other})
    attempt = run.checks[-1]
    assert attempt["status"] == "failed" and attempt["failure"]["type"] == "ContextError"
    assert attempt["evidence"] == [] and run.evidence == []


def test_ordinary_checkers_still_take_two_arguments():
    run = Run(reg_with_context())
    a, b = chain(run)
    assert run.check("toy.check.even", 1, b, {})[0]["outcome"] == "pass"


def test_context_evidence_is_invalidated_by_ancestor_change():
    run = Run(reg_with_context())
    a, b = chain(run)
    (ev,) = run.check("toy.ctx.parent", 1, b, {})
    run._store._tamper_for_tests(a, dict(run.get(a), payload={"value": "5"}))
    assert run.validate(ev)["status"] == "stale_subject"


def test_context_checks_save_load_and_replay(tmp_path):
    reg = reg_with_context()
    run = Run(reg)
    a, b = chain(run)
    run.check("toy.ctx.parent", 1, b, {})
    run.check("toy.ctx.mutate", 1, b, {})
    p = tmp_path / "r.json"
    report = replay(load_run(p, expected_digest=run.save(p)), reg)
    assert report["outcome"] == "reproduced" and report["run_digest_reproduced"] is True


def test_context_constructor_validates_the_chain():
    run = Run(registry())
    a, b = chain(run)
    run._store._tamper_for_tests(a, dict(run.get(a), payload={"value": "5"}))
    from glab.core.records import RecordError
    with pytest.raises(RecordError):
        DependencyContext(run._store, b)
