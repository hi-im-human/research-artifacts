"""Stage 4A controls C2 (classification level), C4, C6, C7 on real specimens (isolated prototype)."""
import copy
from dataclasses import replace
from fractions import Fraction as F

import pytest

from glab.core.registry import ActionSpec, StateDraft
from glab.core.runfile import Run
from glab.two_rim.trim import apply_trim
from probes.stage4a.classify import applies_to, classify_pair, classify_seam
from probes.stage4a.firewall import aligned_distance_to_enclosure, ideal_certificate
from probes.stage4a.ideal import enclose, load_subject, model_from_payloads, shared_hinge_decision
from probes.stage4a.specimens import E11, E11_DELTA, float_states, maintained_registry, prepare


@pytest.fixture(scope="module")
def e11():
    return prepare(E11)


@pytest.fixture(scope="module")
def e9(e11):
    return load_subject(e11, "E9", E11_DELTA)


def test_prerequisites_are_present_current_and_passing(e11, e9):
    assert e9.source_linked and not e9.problems
    assert {r["checker"] for rows in e9.prerequisites.values() for r in rows} == \
        {"two_rim.check.source", "two_rim.check.material", "two_rim.check.cut"}
    assert any(r["claim"] == "two_rim.material.matches_parent_source" and r["outcome"] == "pass"
               for r in e9.prerequisites["material"])


# ---------------------------------------------------------------- C4 low-precision ambiguity

def test_low_precision_never_gives_a_false_verdict(e9):
    """At every lower precision a pair is either unknown or agrees with its 128-bit decision.

    The sweep includes precisions where only some pairs decide (40-56 bits on E9), so the agreement check is
    exercised on real decisions, not only on all-unknown rows.
    """
    model = e9.model
    high = classify_seam(model, schedule=(128,))
    decided = {tuple(r["pair"]): r["outcome"] for r in high["rows"] if r.get("method") != "shared_hinge_exact"}
    assert set(decided.values()) == {"pass", "fail"}
    partial = False
    for bits in (0, 2, 4, 8, 16, 32, 40, 48, 56):
        low = classify_seam(model, schedule=(bits,))
        outs = []
        for r in low["rows"]:
            if r.get("method") == "shared_hinge_exact":
                continue
            outs.append(r["outcome"])
            assert r["outcome"] in ("unknown", decided[tuple(r["pair"])]), (bits, r["pair"], r["outcome"])
        partial = partial or ("unknown" in outs and any(o != "unknown" for o in outs))
    assert partial, "the sweep must include a precision with both decided and undecided pairs"


def test_known_overlap_is_unknown_at_very_low_precision_and_fail_at_high(e9):
    model = e9.model
    assert classify_pair(model, "F10", "F7", schedule=(0,))["outcome"] == "unknown"
    row = classify_pair(model, "F10", "F7", schedule=(64,))
    assert row["outcome"] == "fail" and row["method"] == "interior_witness"


def test_zero_denominator_in_classification_is_unknown(e11):
    """C2 at pair level: a degenerate hinge makes the enclosure refuse; rows become unknown, never pass/fail."""
    run = e11.run
    cut = run.get(e11.cuts["E9"])["payload"]
    material = copy.deepcopy(run.get(e11.material)["payload"])
    h = next(e for e in material["hinges"] if e["id"] == "E5")
    upper = next(v for v in material["vertices"] if v["id"] == h["upper"])
    lower = next(v for v in material["vertices"] if v["id"] == h["lower"])
    upper["xyz"] = list(lower["xyz"])   # L = U: |e| = 0
    model = model_from_payloads(material, dict(cut, material=material), E11_DELTA)
    with pytest.raises(Exception):
        enclose(model, 64)
    res = classify_seam(model, schedule=(64,))
    assert all(r["outcome"] == "unknown" for r in res["rows"] if r.get("method") != "shared_hinge_exact")
    assert any("zero_denominator" in r.get("reason", "") for r in res["rows"])


# ---------------------------------------------------------------- C6 incorrect shared-hinge mapping

def test_valid_retained_neighbours_pass_by_exact_sides(e9):
    m = e9.model
    a, b = m.chain[3], m.chain[4]
    row = shared_hinge_decision(m, a, b, m.faces[a]["exit"])
    assert row["outcome"] == "pass" and set(row["sides"].values()) == {-1, 1}


def test_wrong_hinge_is_refused(e9):
    m = e9.model
    a, b = m.chain[3], m.chain[4]
    row = shared_hinge_decision(m, a, b, m.faces[a]["entry"])
    assert row["outcome"] == "unknown" and row["problems"]


def test_nonconsecutive_faces_are_refused(e9):
    m = e9.model
    a, b = m.chain[2], m.chain[4]
    assert shared_hinge_decision(m, a, b, m.faces[a]["exit"])["outcome"] == "unknown"


def test_the_seam_pair_is_not_shared_in_D(e9):
    m = e9.model
    first, last = m.chain[0], m.chain[-1]
    row = shared_hinge_decision(m, last, first, m.seam)
    assert row["outcome"] == "unknown"
    assert any("seam" in p for p in row["problems"])
    pair = classify_pair(m, first, last, schedule=(128,))
    assert pair.get("method") != "shared_hinge_exact"


def _tampered_model(e11, seam, mutate):
    run = e11.run
    material = copy.deepcopy(run.get(e11.material)["payload"])
    cut = run.get(e11.cuts[seam])["payload"]
    mutate(material, cut["face_order"])
    return model_from_payloads(material, dict(cut, material=material), E11_DELTA)


def test_matching_hinge_ids_with_a_different_endpoint_are_refused(e11):
    def mutate(material, order):
        b = next(f for f in material["faces"] if f["id"] == order[4])
        h = next(e for e in material["hinges"] if e["id"] == b["entry"])
        old = next(v for v in material["vertices"] if v["id"] == h["lower"])
        material["vertices"].append({"id": "Bcopy", "rim": old["rim"], "xyz": list(old["xyz"])})
        b["boundary"] = ["Bcopy" if v == h["lower"] else v for v in b["boundary"]]   # same coordinates, new ID
    m = _tampered_model(e11, "E9", mutate)
    a, b = m.chain[3], m.chain[4]
    row = shared_hinge_decision(m, a, b, m.faces[a]["exit"])
    assert row["outcome"] == "unknown" and any("lacks the hinge endpoint" in p for p in row["problems"])


def test_inward_normal_is_refused(e11):
    def mutate(material, order):
        b = next(f for f in material["faces"] if f["id"] == order[4])
        b["plane"] = [-c for c in b["plane"]]
    m = _tampered_model(e11, "E9", mutate)
    a, b = m.chain[3], m.chain[4]
    row = shared_hinge_decision(m, a, b, m.faces[a]["exit"])
    assert row["outcome"] == "unknown" and any("opposite" in p for p in row["problems"])


# ---------------------------------------------------------------- C7 altered approximate placement

def test_float_states_in_the_same_run_change_nothing_in_the_certificate(e11, e9):
    before = ideal_certificate(e9, schedule=(128,))
    float_states(e11, "E9", E11_DELTA)            # float development and trim now exist in this Run
    after = ideal_certificate(load_subject(e11, "E9", E11_DELTA), schedule=(128,))
    assert after["digest"] == before["digest"]


def test_altered_float_placement_never_inherits_the_ideal_certificate(e11, e9):
    before = ideal_certificate(e9, schedule=(128,))

    def bad(st, params, seed):
        payload = apply_trim(st["payload"], E11_DELTA)
        payload["maps"][3]["offset"] = [payload["maps"][3]["offset"][0] + 0.5, payload["maps"][3]["offset"][1]]
        return StateDraft("two_rim.trimmed_development", payload, "mixed")
    # A separate Run with its own registry carries the control-only faulty action (the probe's Run is untouched).
    reg = maintained_registry()
    reg.register_action(ActionSpec("probe.control.altered_trim", 1, "two_rim.development", {}, "stage4a-control", bad))
    other = prepare(E11, seams=["E9"], run=Run(reg))
    run = other.run
    floats = float_states(other, "E9", E11_DELTA)
    original = run.get(floats["trimmed"])["payload"]
    altered = run.apply("probe.control.altered_trim", 1, {}, floats["development"])["output"]
    ev = {e["claim"]: e["outcome"] for e in run.check("two_rim.check.trimmed_development", 2, altered, {})}
    assert ev["two_rim.development.retained_hinges_and_glued_vertices_agree"] == "fail"  # old control unchanged
    # Same content-addressed source/material/cut states: the ideal certificate is identical across Runs,
    # and nothing about the float states (original or altered) enters it.
    after = ideal_certificate(load_subject(other, "E9", E11_DELTA), schedule=(128,))
    assert after["subject"] == before["subject"]
    assert after["classification_digest"] == before["classification_digest"]
    # The full digests differ only through the Run-specific prerequisite evidence records.
    strip = ("prerequisites", "digest")
    assert {k: v for k, v in after.items() if k not in strip} == {k: v for k, v in before.items() if k not in strip}
    for h in (floats["development"], floats["trimmed"], altered):
        assert not applies_to(before, run.get(h))
    assert applies_to(before, before["subject"]["spec"])
    assert not applies_to(before, dict(before["subject"]["spec"], delta="1/4"))
    enc = enclose(e9.model, 128)
    good = aligned_distance_to_enclosure(e9.model, enc, original)
    worse = aligned_distance_to_enclosure(e9.model, enc, run.get(altered)["payload"])
    assert good["max_distance"] < 1e-9 and worse["max_distance"] > 0.1
    assert good["label"].startswith("diagnostic") and worse["label"].startswith("diagnostic")
