"""Stage 3: exact cut topology and its independent checker."""
import copy

import pytest

from glab.core.registry import ActionSpec, StateDraft
from tests.two_rim_dev.helpers import E11, fixture, material, new_run, outcomes, registry
from glab.core.runfile import Run

MIXED = fixture("F2_nonnested_mixed")


def cut_claims(run, h):
    return outcomes(run.check("two_rim.check.cut", 1, h, {}))


def test_cut_payload_structure():
    run = new_run()
    s, m = material(run, MIXED)
    c = run.apply("two_rim.cut.open", 1, {"seam": "E2"}, m)["output"]
    p = run.get(c)["payload"]
    mat = run.get(m)["payload"]
    n = len(mat["faces"])
    assert p["schema"] == "two_rim.cut/1" and p["seam"] == "E2"
    assert p["face_order"] == [f"F{(2 + j) % n}" for j in range(n)]
    assert p["retained_hinges"] == [f"E{t}" for t in range(n) if t != 2]
    assert p["seam_copies"] == {"entry": {"face": "F2", "hinge": "E2"}, "exit": {"face": "F1", "hinge": "E2"}}
    assert p["material"] == mat
    assert run.get(c)["representation"] == "exact"


@pytest.mark.parametrize("params", [MIXED, fixture("F1_translated_square_prism"), E11])
def test_every_seam_opens_exactly_that_seam(params):
    run = new_run()
    s, m = material(run, params)
    mat = run.get(m)["payload"]
    for e in mat["hinges"]:
        c = run.apply("two_rim.cut.open", 1, {"seam": e["id"]}, m)["output"]
        assert set(cut_claims(run, c).values()) == {"pass"}, (e["id"], cut_claims(run, c))
        classes = run.get(c)["payload"]["glue_classes"]
        for v in mat["vertices"]:
            copies = sum(1 for cl in classes if cl[0].endswith(f"@{v['id']}"))
            assert copies == (2 if v["id"] in (e["lower"], e["upper"]) else 1), (e["id"], v["id"])


def test_seam_endpoint_in_a_multi_face_fan_splits_into_two_copies():
    run = new_run()
    s, m = material(run, MIXED)
    mat = run.get(m)["payload"]
    fan = {v["id"]: [f["id"] for f in mat["faces"] if v["id"] in f["boundary"]] for v in mat["vertices"]}
    seam = next(e for e in mat["hinges"] if len(fan[e["lower"]]) >= 3 or len(fan[e["upper"]]) >= 3)
    c = run.apply("two_rim.cut.open", 1, {"seam": seam["id"]}, m)["output"]
    big = seam["lower"] if len(fan[seam["lower"]]) >= 3 else seam["upper"]
    classes = [cl for cl in run.get(c)["payload"]["glue_classes"] if cl[0].endswith(f"@{big}")]
    assert len(classes) == 2 and sum(len(cl) for cl in classes) == len(fan[big])


@pytest.mark.parametrize("seam", ["E99", "F0", "", "RA0"])
def test_non_hinge_seams_fail(seam):
    run = new_run()
    s, m = material(run, MIXED)
    rec = run.apply("two_rim.cut.open", 1, {"seam": seam}, m)
    assert rec["status"] == "failed" and rec["failure"]["type"] == "DevelopmentInputError"


def _faulty_cut(mutate):
    reg = registry()
    from glab.two_rim.cut import open_cut

    def builder(subject, params, seed):
        p = open_cut(subject["payload"], "E1")
        mutate(p)
        return StateDraft("two_rim.cut", p, "exact")
    reg.register_action(ActionSpec("test.cut.faulty", 1, "two_rim.material", {}, "test-1", builder))
    run = Run(reg)
    s, m = material(run, MIXED)
    return run, run.apply("test.cut.faulty", 1, {}, m)["output"]


def test_extra_cut_is_detected():
    run, c = _faulty_cut(lambda p: p["retained_hinges"].remove("E3"))
    res = cut_claims(run, c)
    assert res["two_rim.cut.exactly_one_original_seam_open"] == "fail"


def test_welded_seam_copies_are_detected():
    def weld(p):
        mat = p["material"]
        e = next(h for h in mat["hinges"] if h["id"] == p["seam"])
        for v in (e["lower"], e["upper"]):
            parts = [cl for cl in p["glue_classes"] if cl[0].endswith(f"@{v}")]
            for cl in parts:
                p["glue_classes"].remove(cl)
            p["glue_classes"].append(sorted(o for cl in parts for o in cl))
    run, c = _faulty_cut(weld)
    assert cut_claims(run, c)["two_rim.cut.glue_classes_match_cut_relation"] == "fail"


def test_material_copy_must_match_the_parent():
    run, c = _faulty_cut(lambda p: p["material"].update(height="7"))
    assert cut_claims(run, c)["two_rim.cut.material_copy_matches_parent"] == "fail"


def test_face_order_must_cover_every_face_once():
    run, c = _faulty_cut(lambda p: p["face_order"].pop())
    assert cut_claims(run, c)["two_rim.cut.face_coverage_complete_unique"] == "fail"
