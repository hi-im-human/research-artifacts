"""Task 3: per-claim evidence, reuse validation, and conservative summaries."""
import copy

import pytest

from glab.core.evidence import (EvidenceError, OUTCOMES, Requirement, evidence_id, make_evidence,
                                summarize, validate_evidence)
from glab.core.registry import CheckerSpec, Claim, Param, Registry
from glab.core.runfile import Run
from tests.core.toy import REV, registry


def new_run(reg=None):
    return Run(reg or registry())


def src(run, value):
    return run.apply("toy.int.source", 1, {"value": value})["output"]


def test_outcome_method_representation_and_validation_are_distinct():
    run = new_run()
    s = src(run, "4")
    (ev,) = run.check("toy.check.even", 1, s, {})
    assert ev["outcome"] == "pass" and ev["method"] == "exact_computation"
    assert ev["representation"] == "exact" and ev["numeric_domain"] == "exact_rational"
    assert ev["subject"] == s and ev["dependencies"] == [s]
    assert ev["checker"] == "toy.check.even" and ev["checker_revision"] == REV
    v = run.validate(ev)
    assert v["status"] == "current" and v["reproduced"] is True


def test_missing_required_evidence_cannot_pass():
    run = new_run()
    s = src(run, "4")
    run.check("toy.check.even", 1, s, {})
    out = run.summarize([Requirement("toy.even", s), Requirement("toy.nonnegative", s)])
    assert out["outcome"] == "not_run" and out["verified"] is False
    assert [r["outcome"] for r in out["requirements"]] == ["pass", "not_run"]


def test_required_unknown_propagates_and_fail_dominates():
    run = new_run()
    s = src(run, "1001")
    run.check("toy.check.prime", 1, s, {})
    run.check("toy.check.nonnegative", 1, s, {})
    out = run.summarize([Requirement("toy.prime", s), Requirement("toy.nonnegative", s)])
    assert out["outcome"] == "unknown" and not out["verified"]
    run.check("toy.check.even", 1, s, {})
    out = run.summarize([Requirement("toy.prime", s), Requirement("toy.even", s)])
    assert out["outcome"] == "fail"


def test_repeated_checks_are_retained_and_conflicts_never_overwrite():
    run = new_run()
    s = src(run, "4")
    a = run.check("toy.check.even", 1, s, {})[0]
    b = run.check("toy.check.even", 1, s, {})[0]
    assert len(run.evidence) == 2 and evidence_id(a) != evidence_id(b)
    assert run.summarize([Requirement("toy.even", s)])["outcome"] == "pass"
    forged = dict(copy.deepcopy(b), seq=2, outcome="fail")
    evs = run.evidence + [forged]
    out = summarize(evs, [Requirement("toy.even", s)], run._store, run._registry, reproduced=run.reproduced)
    assert out["outcome"] == "unknown" and "conflict" in out["requirements"][0]["reason"]
    assert [e["outcome"] for e in evs] == ["pass", "pass", "fail"]


def test_changed_ancestor_invalidates_reuse():
    run = new_run()
    a = src(run, "3")
    b = run.apply("toy.int.add", 1, {"k": 1}, a)["output"]
    (ev,) = run.check("toy.check.even", 1, b, {})
    assert ev["dependencies"] == [b, a]
    run._store._tamper_for_tests(a, dict(run.get(a), payload={"value": "5"}))
    assert run.validate(ev)["status"] == "stale_subject"
    assert run.summarize([Requirement("toy.even", b)])["outcome"] != "pass"


def test_checker_revision_change_invalidates_reuse():
    run = new_run()
    s = src(run, "4")
    (ev,) = run.check("toy.check.even", 1, s, {})
    other = Registry()
    other.register_checker(CheckerSpec("toy.check.even", 1, "toy.int", {}, "changed-revision", lambda st, p: []))
    assert validate_evidence(ev, run._store, other)["status"] == "checker_mismatch"
    assert validate_evidence(ev, run._store, Registry())["status"] == "checker_mismatch"


def test_tolerance_policy_change_invalidates_reuse():
    run = new_run()
    f = run.apply("toy.int.halve_float", 1, {}, src(run, "3"))["output"]
    (ev,) = run.check("toy.check.not_integer", 1, f, {"tol": "1/1000"})
    assert run.validate(ev, expected_tolerances={"abs": "1/1000"})["status"] == "current"
    assert run.validate(ev, expected_tolerances={"abs": "1/100"})["status"] == "policy_mismatch"
    out = run.summarize([Requirement("toy.not_integer", f)], expected_tolerances={"abs": "1/100"})
    assert out["outcome"] == "unknown"


def test_rounded_representation_is_not_evidence_about_its_exact_source():
    run = new_run()
    exact = src(run, "3")
    rounded = run.apply("toy.int.halve_float", 1, {}, exact)["output"]
    (ev,) = run.check("toy.check.not_integer", 1, rounded, {"tol": "1/1000"})
    assert ev["outcome"] == "pass" and ev["representation"] == "approximate"
    assert run.summarize([Requirement("toy.not_integer", exact)])["outcome"] == "not_run"
    strict = Requirement("toy.not_integer", rounded, representations=("exact",))
    out = run.summarize([strict])
    assert out["outcome"] == "unknown" and "representation" in out["requirements"][0]["reason"]


def test_numerical_pass_does_not_satisfy_an_exact_requirement():
    run = new_run()
    rounded = run.apply("toy.int.halve_float", 1, {}, src(run, "3"))["output"]
    run.check("toy.check.not_integer", 1, rounded, {"tol": "1/1000"})
    req = Requirement("toy.not_integer", rounded, methods=("exact_computation", "rigorous_enclosure"))
    out = run.summarize([req])
    assert out["outcome"] == "unknown" and "method" in out["requirements"][0]["reason"]


def test_ambiguous_contact_at_hypothetical_glued_hinge_stays_unknown():
    """Amendment A as metadata: nearness to intended gluing never decides an unresolved contact."""
    def contact(state, params):
        return [Claim("synthetic.interiors_disjoint", "unknown", "numerical_diagnostic", "float64",
                      coverage="pair F0/F1", tolerances={"abs": params["tol"]},
                      receipt={"contact": "within tolerance", "location": "adjacent to glued hinge H1",
                               "decided": False})]
    reg = registry()
    reg.register_checker(CheckerSpec("synthetic.contact", 1, "toy.float", {"tol": Param.exact()}, "syn-1", contact))
    run = new_run(reg)
    f = run.apply("toy.int.halve_float", 1, {}, src(run, "3"))["output"]
    run.check("synthetic.contact", 1, f, {"tol": "1e-9"})
    out = run.summarize([Requirement("synthetic.interiors_disjoint", f)])
    assert out["outcome"] == "unknown" and out["verified"] is False
    assert "pass_near_glued" not in OUTCOMES
    with pytest.raises(EvidenceError):
        make_evidence(seq=0, attempt=0, claim=Claim("x", "pass_near_glued", "numerical_diagnostic", "float64"),
                      subject=f, dependencies=[f], representation="approximate", checker="c",
                      checker_version=1, checker_revision="r", params={})


def test_near_integer_float_is_unknown_not_pass():
    run = new_run()
    f = run.apply("toy.int.halve_float", 1, {}, src(run, "2000001/1000000"))["output"]
    (ev,) = run.check("toy.check.not_integer", 1, f, {"tol": "1/1000"})
    assert ev["outcome"] == "unknown"


def test_imported_results_are_not_verified_by_label():
    run = new_run()
    s = src(run, "4")
    run.check("toy.check.even", 1, s, {})
    reqs = [Requirement("toy.even", s)]
    here = summarize(run.evidence, reqs, run._store, run._registry, reproduced=run.reproduced)
    imported = summarize(run.evidence, reqs, run._store, run._registry, reproduced=frozenset())
    assert here["outcome"] == imported["outcome"] == "pass"
    assert here["verified"] is True and imported["verified"] is False


def test_formal_proof_has_no_route_to_pass():
    run = new_run()
    s = src(run, "4")
    with pytest.raises(EvidenceError, match="formal"):
        make_evidence(seq=0, attempt=0, claim=Claim("toy.even", "pass", "formal_proof", "lean"), subject=s,
                      dependencies=[s], representation="exact", checker="c", checker_version=1,
                      checker_revision="r", params={"theorem_url": "https://example.org/proof"})
    (ev,) = run.check("toy.check.even", 1, s, {})
    claimed = dict(ev, method="formal_proof", receipt={"theorem_url": "https://example.org/proof"})
    assert run.validate(claimed)["status"] == "unsupported_method"
    out = summarize([claimed], [Requirement("toy.even", s)], run._store, run._registry,
                    reproduced=frozenset({evidence_id(claimed)}))
    assert out["outcome"] != "pass" and not out["verified"]

    def liar(state, params):
        return [Claim("toy.even", "pass", "formal_proof", "lean")]
    reg = registry()
    reg.register_checker(CheckerSpec("toy.check.liar", 1, "toy.int", {}, "liar", liar))
    run2 = new_run(reg)
    with pytest.raises(EvidenceError):
        run2.check("toy.check.liar", 1, src(run2, "4"), {})
    assert run2.evidence == []


def test_requirement_parameters_bind_evidence():
    run = new_run()
    f = run.apply("toy.int.halve_float", 1, {}, src(run, "3"))["output"]
    run.check("toy.check.not_integer", 1, f, {"tol": "1/1000"})
    assert run.summarize([Requirement("toy.not_integer", f, params={"tol": "1/10"})])["outcome"] == "not_run"


def test_speculative_state_is_preserved_with_failing_evidence():
    run = new_run()
    neg = run.apply("toy.int.add", 1, {"k": -10}, src(run, "3"))
    assert neg["status"] == "succeeded"
    (ev,) = run.check("toy.check.nonnegative", 1, neg["output"], {})
    assert ev["outcome"] == "fail" and run.get(neg["output"])["payload"] == {"value": "-7"}


def test_check_input_validation():
    run = new_run()
    s = src(run, "4")
    f = run.apply("toy.int.halve_float", 1, {}, s)["output"]
    from glab.core.registry import RegistryError
    for args in (("toy.check.even", 1, f, {}), ("toy.check.even", 2, s, {}), ("toy.check.even", 1, s, {"x": 1}),
                 ("toy.check.even", 1, "sha256:" + "0" * 64, {})):
        with pytest.raises(RegistryError):
            run.check(*args)
