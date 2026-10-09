"""Stage 4A repair A02 (isolated prototype): calculation and prerequisites bound to the subject at use time."""
import dataclasses

import pytest

from glab.check.two_rim_source import MATERIAL_CLAIMS
from glab.core.registry import ActionSpec, CheckerSpec, Claim, StateDraft
from glab.core.runfile import Run
from glab.two_rim.material import build_material
from glab.two_rim.source import normalize_source
from probes.stage4a.firewall import ideal_certificate
from probes.stage4a.ideal import FrozenDict, load_subject
from probes.stage4a.specimens import E11, E11_DELTA, SQUARE, Prepared, _summary, maintained_registry, prepare


@pytest.fixture(scope="module")
def e11():
    return prepare(E11, seams=["E9", "E4"])


def test_valid_controls(e11):
    assert ideal_certificate(load_subject(e11, "E9", E11_DELTA))["seam_verdict"] == "fail"
    assert ideal_certificate(load_subject(e11, "E4", E11_DELTA))["seam_verdict"] == "pass"


def test_subject_fields_are_frozen(e11):
    s9, s4 = load_subject(e11, "E9", E11_DELTA), load_subject(e11, "E4", E11_DELTA)
    for field, value in (("model", s4.model), ("spec", s4.spec), ("id", s4.id), ("source_linked", False)):
        with pytest.raises(dataclasses.FrozenInstanceError):
            setattr(s9, field, value)


def test_nested_model_and_spec_mutation_is_refused(e11):
    s = load_subject(e11, "E9", E11_DELTA)
    with pytest.raises(TypeError):
        s.model.faces["F3"]["normal"] = (1, 2, 3)
    with pytest.raises(TypeError):
        s.model.vertices["A0"] = (0, 0, 0)
    with pytest.raises(TypeError):
        s.model.rings["F3"][0] = "E0@lo"
    with pytest.raises(TypeError):
        s.spec["seam"] = "E4"
    with pytest.raises(AttributeError):
        s.model.chain.append("F0")


def test_bypassed_model_swap_is_refused_at_issuance(e11):
    s9, s4 = load_subject(e11, "E9", E11_DELTA), load_subject(e11, "E4", E11_DELTA)
    object.__setattr__(s9, "model", s4.model)
    c = ideal_certificate(s9)
    assert c["status"] == "refused" and c["refusal"]["kind"] == "subject_model_mismatch"
    assert c["seam_verdict"] == "refused"


def test_bypassed_nested_mutation_is_refused_at_issuance(e11):
    s = load_subject(e11, "E9", E11_DELTA)
    face = dict(s.model.faces["F3"])
    face["normal"] = tuple(-x for x in face["normal"])
    dict.__setitem__(s.model.faces, "F3", FrozenDict(face))      # deliberate bypass of FrozenDict
    c = ideal_certificate(s)
    assert c["status"] == "refused" and c["refusal"]["kind"] == "subject_model_mismatch"


def test_spec_and_id_disagreement_is_refused(e11):
    s9, s4 = load_subject(e11, "E9", E11_DELTA), load_subject(e11, "E4", E11_DELTA)
    object.__setattr__(s9, "spec", s4.spec)                      # ID left as E9's
    c = ideal_certificate(s9)
    assert c["status"] == "refused" and c["refusal"]["kind"] == "subject_binding"


def test_consistent_swap_certifies_what_it_names_never_the_old_id(e11):
    s9, s4 = load_subject(e11, "E9", E11_DELTA), load_subject(e11, "E4", E11_DELTA)
    old_id = s9.id
    for field in ("spec", "id", "model"):
        object.__setattr__(s9, field, getattr(s4, field))
    c = ideal_certificate(s9)
    assert c["subject"]["id"] == s4.id != old_id and c["subject"]["spec"]["seam"] == "E4"


def _wrong_source(material_checker=True, extra_checker=None):
    reg = maintained_registry()
    reg.register_action(ActionSpec(
        "probe.control.wrong_material", 1, "two_rim.source", {}, "stage4a-control",
        lambda st, p, se: StateDraft("two_rim.material", build_material(normalize_source(**dict(SQUARE, height="4"))),
                                     "exact")))
    if extra_checker:
        reg.register_checker(extra_checker)
    run = Run(reg)
    s = run.apply("two_rim.source.normalize", 1, SQUARE)["output"]
    m = run.apply("probe.control.wrong_material", 1, {}, s)["output"]
    c = run.apply("two_rim.cut.open", 1, {"seam": "E0"}, m)["output"]
    pre = {"source": _summary(run, run.check("two_rim.check.source", 2, s, {})),
           "material": _summary(run, run.check("two_rim.check.material", 2, m, {})) if material_checker else [],
           "cut:E0": _summary(run, run.check("two_rim.check.cut", 1, c, {}))}
    if extra_checker:
        pre["material"] += _summary(run, run.check(extra_checker.name, extra_checker.version, m, {}))
    return Prepared(run, s, m, {"E0": c}, pre)


def test_carried_source_linked_flag_is_ignored():
    s = load_subject(_wrong_source(), "E0", "1/4")
    object.__setattr__(s, "source_linked", True)
    c = ideal_certificate(s)
    assert c["source_linked"] is False and c["seam_verdict"] == "not_source_linked"


def test_cached_prerequisite_rows_are_ignored():
    p = _wrong_source()
    p.prerequisites["material"] = [r for r in p.prerequisites["material"]
                                   if r["claim"] != "two_rim.material.matches_parent_source"]
    for rows in p.prerequisites.values():
        for r in rows:
            r["outcome"], r["validation"] = "pass", "current"      # forged cache strings
    c = ideal_certificate(load_subject(p, "E0", "1/4"))
    assert c["source_linked"] is False and c["seam_verdict"] == "not_source_linked"
    failing = [r for r in c["prerequisites"]["rows"] if r["outcome"] != "pass"]
    assert any(r["claim"] == "two_rim.material.matches_parent_source" for r in failing)


def test_stale_prerequisite_evidence_is_not_accepted():
    p = prepare(SQUARE, seams=["E0"])
    source = p.run.get(p.source)
    source["payload"]["normalized"]["height"] = "5"          # the stored source no longer matches its hash
    p.run._store._tamper_for_tests(p.source, source)
    c = ideal_certificate(load_subject(p, "E0", "1/4"))
    assert c["source_linked"] is False
    assert c["seam_verdict"] in ("not_source_linked", "refused")


def test_unrelated_prerequisite_evidence_is_not_accepted():
    run = Run(maintained_registry())
    s = run.apply("two_rim.source.normalize", 1, SQUARE)["output"]
    m = run.apply("two_rim.material.build", 1, {}, s)["output"]
    c0 = run.apply("two_rim.cut.open", 1, {"seam": "E0"}, m)["output"]
    c1 = run.apply("two_rim.cut.open", 1, {"seam": "E1"}, m)["output"]
    pre = {"source": _summary(run, run.check("two_rim.check.source", 2, s, {})),
           "material": _summary(run, run.check("two_rim.check.material", 2, m, {})),
           "cut:E0": _summary(run, run.check("two_rim.check.cut", 1, c1, {}))}   # E1's evidence under E0's name
    c = ideal_certificate(load_subject(Prepared(run, s, m, {"E0": c0, "E1": c1}, pre), "E0", "1/4"))
    assert c["source_linked"] is False
    assert any(r["subject"] == c0 and r["outcome"] == "not_run" for r in c["prerequisites"]["rows"])


def test_rogue_checker_with_matching_claim_names_is_not_accepted():
    def fake(state, params):
        return [Claim(name, "pass", "exact_computation", "exact_rational") for name in MATERIAL_CLAIMS]
    rogue = CheckerSpec("probe.control.fake_material", 1, "two_rim.material", {}, "stage4a-control", fake)
    c = ideal_certificate(load_subject(_wrong_source(material_checker=False, extra_checker=rogue), "E0", "1/4"))
    assert c["source_linked"] is False
    assert any("probe.control.fake_material" in str(r.get("problems")) for r in c["prerequisites"]["rows"])
