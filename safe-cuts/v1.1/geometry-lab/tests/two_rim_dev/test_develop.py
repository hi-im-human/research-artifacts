"""Stage 3: static full-affine development, golden comparison, and the required mutations."""
import copy
from fractions import Fraction

import numpy as np
import pytest

from glab.core.registry import ActionSpec, StateDraft
from glab.core.runfile import Run
from glab.two_rim.develop import chart_data, develop_static
from tests.two_rim_dev.bridge_support import load_bridge
from tests.two_rim_dev.helpers import E11, developed, fixture, material, new_run, outcomes, registry

BRIDGE = load_bridge()
MIXED = fixture("F2_nonnested_mixed")
FIXTURES = {n: fixture(n) for n in ("F1_translated_square_prism", "F2_nonnested_mixed",
                                     "F3_near_degenerate_prism", "X_pinned_hard_flat")}
FIXTURES["E11"] = E11
DEV = "two_rim.development."
RIGID, REFLECT, NONEMPTY, AGREE, PAIRS = (DEV + x for x in (
    "face_maps_rigid", "no_reflected_face", "nonempty_face_images",
    "retained_hinges_and_glued_vertices_agree", "face_interiors_disjoint_all_pairs"))


def dev_claims(run, h):
    return run.check("two_rim.check.development", 2, h, {})


def test_development_payload_structure():
    run = new_run()
    d = developed(run, MIXED, seam="E1")
    st = run.get(d["development"])
    p = st["payload"]
    assert st["representation"] == "mixed" and p["schema"] == "two_rim.development/1"
    assert p["numeric_domain"] == "float64" and p["cut"] == run.get(d["cut"])["payload"]
    assert [m["face"] for m in p["maps"]] == p["cut"]["face_order"]
    for m in p["maps"]:
        assert np.array(m["linear"]).shape == (2, 3) and len(m["offset"]) == 2
    assert len({tuple(m["offset"]) for m in p["maps"]}) == len(p["maps"])  # translations retained


@pytest.mark.parametrize("name", sorted(FIXTURES))
def test_golden_against_pinned_bridge_for_every_seam(name):
    run = new_run()
    s, m = material(run, FIXTURES[name])
    mat = run.get(m)["payload"]
    top = [(Fraction(v["xyz"][0]), Fraction(v["xyz"][1])) for v in mat["vertices"] if v["rim"] == "top"]
    bottom = [(Fraction(v["xyz"][0]), Fraction(v["xyz"][1])) for v in mat["vertices"] if v["rim"] == "bottom"]
    bridge = BRIDGE.PhysicalBridge(top, bottom, Fraction(mat["height"]))
    xyz = {v["id"]: np.array([float(Fraction(c)) for c in v["xyz"]]) for v in mat["vertices"]}
    for e in mat["hinges"]:
        k = next(i for i in range(bridge.n) if np.array_equal(bridge.low[i], xyz[e["lower"]])
                 and np.array_equal(bridge.high[i], xyz[e["upper"]]))
        c = run.apply("two_rim.cut.open", 1, {"seam": e["id"]}, m)["output"]
        ours = develop_static(run.get(c)["payload"])["maps"]
        theirs = bridge.maps(k)
        assert len(ours) == len(theirs)
        for mine, ref in zip(ours, theirs):
            np.testing.assert_allclose(np.array(mine["linear"]), ref.linear, rtol=1e-12, atol=1e-12)
            np.testing.assert_allclose(np.array(mine["offset"]), ref.offset, rtol=1e-12, atol=1e-9)


@pytest.mark.parametrize("seam", ["E0", "E1", "E2", "E3", "E4"])
def test_valid_development_claims(seam):
    run = new_run()
    d = developed(run, MIXED, seam=seam)
    res = outcomes(dev_claims(run, d["development"]))
    for claim in (DEV + "record_schema", DEV + "cut_copy_matches_parent", RIGID, REFLECT, NONEMPTY, AGREE):
        assert res[claim] == "pass", (claim, res)
    assert res[PAIRS] in ("pass", "unknown")  # retained-adjacent slivers may stay unknown; never a pass by proximity


def test_every_pair_is_checked_including_retained_adjacent_contacts():
    run = new_run()
    d = developed(run, MIXED, seam="E0")
    ev = next(e for e in dev_claims(run, d["development"]) if e["claim"] == PAIRS)
    rows = ev["receipt"]["rows"]
    n = len(run.get(d["cut"])["payload"]["face_order"])
    assert len(rows) == n * (n - 1) // 2 and ev["receipt"]["adjacent_pairs_skipped"] == 0
    adjacent = [r for r in rows if r["shared"] == "retained_hinge"]
    assert len(adjacent) == n - 1
    assert all(r["reason"] != "separated" and r["outcome"] in ("pass", "unknown") for r in adjacent)
    assert all("opposite_sides_margin" in r for r in adjacent)  # informational only
    assert ev["coverage"] == "all" and ev["method"] == "numerical_diagnostic"


def _faulty(mutate, params=MIXED, seam="E0"):
    reg = registry()

    def builder(subject, params_, seed):
        p = develop_static(subject["payload"])
        mutate(p)
        return StateDraft("two_rim.development", p, "mixed")
    reg.register_action(ActionSpec("test.develop.faulty", 1, "two_rim.cut", {}, "test-faulty-1", builder))
    run = Run(reg)
    s, m = material(run, params)
    c = run.apply("two_rim.cut.open", 1, {"seam": seam}, m)["output"]
    d = run.apply("test.develop.faulty", 1, {}, c)["output"]
    return run, d


def test_omitted_translation_keeps_faces_rigid_but_breaks_hinge_agreement():
    def drop_translation(p):
        charts = chart_data(p["cut"]["material"])
        rot = np.eye(2)
        n = len(charts["faces"])
        order = p["cut"]["face_order"]
        k = charts["faces"].index(order[0])
        for j in range(n):
            i = (k + j) % n
            lin = rot @ np.array(charts["chart"][i])
            p["maps"][j]["linear"] = lin.tolist()
            p["maps"][j]["offset"] = (-(lin @ np.array(charts["mid"][i]))).tolist()
            c, s = np.cos(charts["q"][(i + 1) % n]), np.sin(charts["q"][(i + 1) % n])
            rot = rot @ np.array([[c, -s], [s, c]])
    run, d = _faulty(drop_translation)
    res = outcomes(dev_claims(run, d))
    assert res[RIGID] == "pass" and res[AGREE] == "fail"


def test_damaged_transform_is_detected():
    run, d = _faulty(lambda p: p["maps"][2]["linear"][0].__setitem__(0, p["maps"][2]["linear"][0][0] * 1.001))
    assert outcomes(dev_claims(run, d))[RIGID] == "fail"


def test_reflected_face_is_detected():
    def reflect(p):
        m = p["maps"][3]
        m["linear"][1] = [-x for x in m["linear"][1]]
        m["offset"][1] = -m["offset"][1]
    run, d = _faulty(reflect)
    res = outcomes(dev_claims(run, d))
    assert res[RIGID] == "pass" and res[REFLECT] == "fail"


def test_omitted_face_breaks_the_record():
    run, d = _faulty(lambda p: p["maps"].pop())
    res = outcomes(dev_claims(run, d))
    assert res[DEV + "record_schema"] == "fail" and res[PAIRS] == "unknown"


def test_nonadjacent_stacking_is_an_interior_overlap():
    def stack(p):
        a, b = p["maps"][0], p["maps"][2]
        b["linear"], b["offset"] = copy.deepcopy(a["linear"]), copy.deepcopy(a["offset"])
    run, d = _faulty(stack, params=fixture("F1_translated_square_prism"))
    ev = next(e for e in dev_claims(run, d) if e["claim"] == PAIRS)
    assert ev["outcome"] == "fail"
    assert any(r["reason"] == "interior_overlap" for r in ev["receipt"]["rows"])


def test_cut_copy_must_match_the_parent_cut():
    run, d = _faulty(lambda p: p["cut"].update(seam="E3"))
    assert outcomes(dev_claims(run, d))[DEV + "cut_copy_matches_parent"] == "fail"


def test_changed_ancestor_invalidates_development_evidence():
    run = new_run()
    d = developed(run, MIXED, seam="E0")
    ev = dev_claims(run, d["development"])[0]
    cut = run.get(d["cut"])
    cut["payload"]["retained_hinges"].pop()
    run._store._tamper_for_tests(d["cut"], cut)
    assert run.validate(ev)["status"] == "stale_subject"


def test_holonomy_diagnostic_sign_policy():
    run = new_run()
    prism = developed(run, fixture("F1_translated_square_prism"), seam="E0")
    mixed = developed(run, MIXED, seam="E0")
    hol = DEV + "diagnostic.circuit_holonomy"
    p_ev = next(e for e in dev_claims(run, prism["development"]) if e["claim"] == hol)
    m_ev = next(e for e in dev_claims(run, mixed["development"]) if e["claim"] == hol)
    # v2 (repair S03): the checker reconstructs the lifted total turn; near identity its sign is unknown
    assert p_ev["outcome"] == "pass" and p_ev["receipt"]["lifted_total_turn_sign"] == "unknown"
    assert m_ev["outcome"] == "pass" and m_ev["receipt"]["lifted_total_turn_sign"] in ("negative", "positive")


def test_no_claim_uses_rigorous_enclosure():
    run = new_run()
    d = developed(run, MIXED, seam="E0", delta="1/4")
    evs = dev_claims(run, d["development"]) + run.check("two_rim.check.trimmed_development", 2, d["trimmed"], {})
    assert all(e["method"] in ("numerical_diagnostic", "exact_computation") for e in evs)
