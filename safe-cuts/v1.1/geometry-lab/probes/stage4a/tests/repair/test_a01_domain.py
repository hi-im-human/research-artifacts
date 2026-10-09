"""Stage 4A repair A01 (isolated prototype): domain and face preconditions enforced at certificate issuance."""
import copy
from fractions import Fraction as F

import pytest

from glab.core.records import content_hash
from glab.core.registry import ActionSpec, StateDraft
from glab.core.runfile import Run
from glab.two_rim.cut import open_cut
from glab.two_rim.material import build_material, material_identity
from glab.two_rim.source import normalize_source
from probes.stage4a.classify import classify_seam
from probes.stage4a.firewall import ideal_certificate
from probes.stage4a.ideal import FrozenDict, UnsupportedSubject, load_subject, model_from_payloads
from probes.stage4a.specimens import E11, E11_DELTA, SQUARE, Prepared, _summary, maintained_registry, prepare

NEAR_ZERO = str(F(1, 10**30))
NEAR_HALF = str(F(1, 2) - F(1, 10**30))


@pytest.fixture(scope="module")
def square():
    return prepare(SQUARE, seams=["E0"])


@pytest.fixture(scope="module")
def e11():
    return prepare(E11, seams=["E9"])


@pytest.mark.parametrize("delta", ["-1", "0", "1/2", "1", "2", "3/4", "-1/10"])
def test_out_of_domain_delta_is_refused_before_D_exists(square, delta):
    with pytest.raises(UnsupportedSubject):
        load_subject(square, "E0", delta)


@pytest.mark.parametrize("delta", ["0.25", "2/8", " 1/4", 0.25, True, None])
def test_non_canonical_or_non_exact_delta_is_refused(square, delta):
    with pytest.raises(UnsupportedSubject):
        load_subject(square, "E0", delta)


def test_delta_altered_after_construction_is_refused_at_issuance(square):
    s = load_subject(square, "E0", "1/4")
    spec = dict(s.spec, delta="1/2")
    object.__setattr__(s, "spec", FrozenDict(spec))      # bypass the frozen object deliberately
    object.__setattr__(s, "id", content_hash(spec))       # and keep the ID consistent with the altered spec
    c = ideal_certificate(s, schedule=(64,))
    assert c["status"] == "refused" and c["seam_verdict"] == "refused"
    assert c["refusal"]["kind"] == "unsupported_subject"
    assert any("delta" in p for p in c["refusal"]["problems"])
    assert "classification" not in c or c["classification"] is None


@pytest.mark.parametrize("delta", [NEAR_ZERO, NEAR_HALF, "1/4", "1/10000"])
def test_valid_near_boundary_square_is_issued_and_passes(square, delta):
    c = ideal_certificate(load_subject(square, "E0", delta))
    assert c["status"] == "issued" and c["source_linked"] is True and c["seam_verdict"] == "pass"
    assert all(v for v in c["preconditions"]["checks"].values())


def test_valid_near_half_eleven_panel_is_issued_honestly(e11):
    c = ideal_certificate(load_subject(e11, "E9", NEAR_HALF))
    assert c["status"] == "issued" and c["source_linked"] is True
    assert c["seam_verdict"] in ("pass", "fail", "unknown")


def _faulty_run(material_mutation=None, cut_mutation=None):
    """A Run whose material or cut comes from a deliberately faulty registered builder."""
    reg = maintained_registry()

    def material(st, params, seed):
        payload = build_material(st["payload"])
        if material_mutation:
            material_mutation(payload)
        return StateDraft("two_rim.material", payload, "exact")

    def cut(st, params, seed):
        payload = open_cut(st["payload"], "E0")
        if cut_mutation:
            cut_mutation(payload)
        return StateDraft("two_rim.cut", payload, "exact")
    reg.register_action(ActionSpec("probe.control.material", 1, "two_rim.source", {}, "stage4a-control", material))
    reg.register_action(ActionSpec("probe.control.cut", 1, "two_rim.material", {}, "stage4a-control", cut))
    run = Run(reg)
    s = run.apply("two_rim.source.normalize", 1, SQUARE)["output"]
    m = run.apply("probe.control.material", 1, {}, s)["output"]
    c = run.apply("probe.control.cut", 1, {}, m)["output"]
    pre = {"source": _summary(run, run.check("two_rim.check.source", 2, s, {})),
           "material": _summary(run, run.check("two_rim.check.material", 2, m, {})),
           "cut:E0": _summary(run, run.check("two_rim.check.cut", 1, c, {}))}
    return Prepared(run, s, m, {"E0": c}, pre)


def test_inward_face_plane_is_a_refusal_not_an_overlap_failure():
    def inward(payload):
        payload["faces"][1]["plane"] = [-x for x in payload["faces"][1]["plane"]]
        payload["identity"] = material_identity(payload)    # self-consistent record: isolates the face precondition
    c = ideal_certificate(load_subject(_faulty_run(material_mutation=inward), "E0", "1/4"))
    assert c["status"] == "refused" and c["seam_verdict"] == "refused"
    assert c["refusal"]["kind"] == "unsupported_subject"
    assert any("outward" in p or "orientation" in p or "convex" in p for p in c["refusal"]["problems"])


def test_material_whose_identity_does_not_recompute_is_a_binding_refusal():
    def inconsistent(payload):
        payload["faces"][1]["plane"] = [-x for x in payload["faces"][1]["plane"]]   # identity left stale
    c = ideal_certificate(load_subject(_faulty_run(material_mutation=inconsistent), "E0", "1/4"))
    assert c["status"] == "refused" and c["refusal"]["kind"] == "subject_binding"
    assert any("identity" in p for p in c["refusal"]["problems"])


def test_scrambled_chain_is_a_refusal():
    def scramble(payload):
        order = payload["face_order"]
        order[1], order[2] = order[2], order[1]
    c = ideal_certificate(load_subject(_faulty_run(cut_mutation=scramble), "E0", "1/4"))
    assert c["status"] == "refused" and c["refusal"]["kind"] == "unsupported_subject"
    assert any("chain" in p for p in c["refusal"]["problems"])


def test_valid_faulty_run_control_is_issued():
    c = ideal_certificate(load_subject(_faulty_run(), "E0", "1/4"))   # no mutation: genuine material and cut
    assert c["status"] == "issued" and c["source_linked"] is True and c["seam_verdict"] == "pass"


def test_synthetic_low_level_classification_stays_possible_but_is_not_a_certificate(square):
    run = square.run
    cut = run.get(square.cuts["E0"])["payload"]
    material = copy.deepcopy(run.get(square.material)["payload"])
    model = model_from_payloads(material, dict(cut, material=material), "1/2")   # outside the supported domain
    res = classify_seam(model, schedule=(64,))
    assert len(res["rows"]) == 6 and "status" not in res and "seam_verdict" not in res
