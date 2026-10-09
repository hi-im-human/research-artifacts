"""Stage 3: positive trim reusing the identical stored maps; exact trim domain."""
from fractions import Fraction

import pytest

from glab.core.registry import ActionSpec, StateDraft
from glab.core.runfile import Run, load_run, replay
from glab.two_rim.trim import apply_trim
from tests.two_rim_dev.helpers import developed, fixture, material, new_run, outcomes, registry

MIXED = fixture("F2_nonnested_mixed")
TRIM = "two_rim.trim."


def trim_claims(run, h):
    return outcomes(run.check("two_rim.check.trimmed_development", 2, h, {}))


def test_trim_reuses_identical_maps_and_exact_points():
    run = new_run()
    d = developed(run, MIXED, seam="E2", delta="1/4")
    t = run.get(d["trimmed"])
    p = t["payload"]
    assert t["parent"] == d["development"] and t["representation"] == "mixed"
    assert p["maps"] == run.get(d["development"])["payload"]["maps"]
    mat = run.get(d["material"])["payload"]
    xyz = {v["id"]: [Fraction(c) for c in v["xyz"]] for v in mat["vertices"]}
    for e in mat["hinges"]:
        lo, hi = xyz[e["lower"]], xyz[e["upper"]]
        for tag, s in (("lo", Fraction(1, 4)), ("hi", Fraction(3, 4))):
            pt = p["trim_points"][f"{e['id']}@{tag}"]
            assert pt["hinge"] == e["id"] and Fraction(pt["t"]) == s
            assert [Fraction(c) for c in pt["xyz"]] == [a + s * (b - a) for a, b in zip(lo, hi)]
    assert all(len(f["boundary"]) == 4 for f in p["faces"])  # (3.5): both runs positive after trimming


@pytest.mark.parametrize("delta", ["1/4", "1/100", "1/3"])
def test_trimmed_claims_pass_for_valid_trims(delta):
    run = new_run()
    d = developed(run, MIXED, seam="E0", delta=delta)
    res = trim_claims(run, d["trimmed"])
    for claim in (TRIM + "record_schema", TRIM + "maps_identical_to_parent", TRIM + "domain_is_exact_band",
                  "two_rim.development.face_maps_rigid", "two_rim.development.no_reflected_face",
                  "two_rim.development.nonempty_face_images",
                  "two_rim.development.retained_hinges_and_glued_vertices_agree"):
        assert res[claim] == "pass", (claim, res)
    assert res["two_rim.development.face_interiors_disjoint_all_pairs"] in ("pass", "unknown")


@pytest.mark.parametrize("delta", ["0", "1/2", "-1/10", "3/5"])
def test_invalid_delta_fails(delta):
    run = new_run()
    d = developed(run, MIXED)
    rec = run.apply("two_rim.trim.apply", 1, {"delta": delta}, d["development"])
    assert rec["status"] == "failed" and rec["failure"]["type"] == "DevelopmentInputError"


def test_float_delta_rejected_and_trim_of_trim_refused():
    run = new_run()
    d = developed(run, MIXED, delta="1/4")
    assert run.apply("two_rim.trim.apply", 1, {"delta": 0.25}, d["development"])["status"] == "rejected"
    assert run.apply("two_rim.trim.apply", 1, {"delta": "1/8"}, d["trimmed"])["status"] == "rejected"


def _faulty_trim(mutate):
    reg = registry()

    def builder(subject, params, seed):
        p = apply_trim(subject["payload"], "1/4")
        mutate(p)
        return StateDraft("two_rim.trimmed_development", p, "mixed")
    reg.register_action(ActionSpec("test.trim.faulty", 1, "two_rim.development", {}, "test-1", builder))
    run = Run(reg)
    d = developed(run, MIXED)
    return run, run.apply("test.trim.faulty", 1, {}, d["development"])["output"]


def test_rescaled_maps_are_not_the_same_maps():
    def rescale(p):
        p["maps"][0]["linear"] = [[x * 0.5 for x in row] for row in p["maps"][0]["linear"]]
    run, t = _faulty_trim(rescale)
    res = trim_claims(run, t)
    assert res[TRIM + "maps_identical_to_parent"] == "fail"
    assert res["two_rim.development.face_maps_rigid"] == "fail"


def test_wrong_trim_point_is_not_the_exact_band():
    run, t = _faulty_trim(lambda p: p["trim_points"]["E0@lo"].update(xyz=["0", "0", "0"]))
    assert trim_claims(run, t)[TRIM + "domain_is_exact_band"] == "fail"


def test_full_chain_saves_loads_and_replays(tmp_path):
    reg = registry()
    run = Run(reg)
    d = developed(run, MIXED, seam="E3", delta="1/5")
    run.check("two_rim.check.cut", 1, d["cut"], {})
    run.check("two_rim.check.development", 2, d["development"], {})
    run.check("two_rim.check.trimmed_development", 2, d["trimmed"], {})
    p = tmp_path / "r.json"
    report = replay(load_run(p, expected_digest=run.save(p)), reg)
    assert report["outcome"] == "reproduced" and report["run_digest_reproduced"] is True
