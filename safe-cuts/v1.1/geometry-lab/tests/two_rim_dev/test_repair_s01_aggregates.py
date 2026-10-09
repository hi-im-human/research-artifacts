"""Stage 3 repair S01: local totals versus source-linked aggregates in the enumerated search."""
from dataclasses import replace

from glab.check.two_rim_development import register_development_checkers
from glab.core.registry import ActionSpec, Registry, StateDraft
from glab.core.runfile import Run
from glab.two_rim.actions import register_actions
from glab.two_rim.dev_actions import register_development_actions
from glab.two_rim.develop import develop_static
from glab.two_rim.material import build_material
from glab.two_rim.search import (DEVELOPMENT_OBLIGATIONS, MATERIAL_OBLIGATIONS, SOURCE_OBLIGATIONS,
                                 TRIM_OBLIGATIONS, enumerated_candidate_search)
from glab.two_rim.source import normalize_source
from tests.two_rim_dev.helpers import E11, material, new_run, registry

SQ = [[0, 0], [0, 2], [2, 2], [2, 0]]
SQUARE = {"top": SQ, "bottom": SQ, "height": "3", "input_kind": "cyclic_boundary"}
PAIRS = "two_rim.development.face_interiors_disjoint_all_pairs"
CUT_COPY = "two_rim.development.cut_copy_matches_parent"


def search(run, params, delta):
    _, m = material(run, params)
    return enumerated_candidate_search(run, m, delta)


def test_complete_aggregate_passes_with_the_real_stage2_bundle():
    rep = search(new_run(), SQUARE, "1/4")
    assert rep["prerequisites"]["source"]["claims"] == {c: "pass" for c in SOURCE_OBLIGATIONS}
    assert rep["prerequisites"]["material"]["claims"] == {c: "pass" for c in MATERIAL_OBLIGATIONS}
    assert len(rep["results"]) == 4
    for row in rep["results"]:
        assert row["full_obligations"] == row["trimmed_obligations"] == "pass"
        assert row["source_linked_full_obligations"] == row["source_linked_trimmed_obligations"] == "pass"


def test_report_labels_local_and_source_linked_aggregates():
    rep = search(new_run(), SQUARE, "1/4")
    defs = rep["aggregate_definitions"]
    assert defs["full_obligations"]["scope"].startswith("local")
    assert defs["trimmed_obligations"]["scope"].startswith("local")
    assert defs["source_linked_trimmed_obligations"]["scope"].startswith("source-linked")
    linked = defs["source_linked_trimmed_obligations"]["requirements"]
    assert linked["source"] == list(SOURCE_OBLIGATIONS) and linked["material"] == list(MATERIAL_OBLIGATIONS)
    assert "two_rim.material.matches_parent_source" in linked["material"]
    # the trimmed total inherits the development's exact contracts, not its full-domain numerical verdicts
    assert linked["development"] == ["two_rim.development.record_schema", CUT_COPY]
    assert linked["trimmed"] == list(TRIM_OBLIGATIONS)


def _registry_without_stage2():
    r = Registry()
    register_actions(r)
    register_development_actions(r)
    register_development_checkers(r)
    return r


def test_missing_prerequisite_checker_is_never_a_complete_pass():
    run = Run(_registry_without_stage2())
    rep = search(run, SQUARE, "1/4")
    assert rep["prerequisites"]["source"]["status"] == "rejected"
    assert rep["prerequisites"]["material"]["status"] == "rejected"
    for row in rep["results"]:
        assert row["trimmed_obligations"] == "pass"  # local geometry is unaffected
        assert row["source_linked_full_obligations"] == row["source_linked_trimmed_obligations"] == "not_run"
    rejected = [h for h in run.checks if h["status"] == "rejected"]
    assert {h["checker"] for h in rejected} == {"two_rim.check.source", "two_rim.check.material"}


def test_changed_source_fails_only_the_source_linked_aggregates():
    reg = registry()
    reg.register_action(ActionSpec(
        "test.wrong.material", 1, "two_rim.source", {}, "test-1",
        lambda st, p, seed: StateDraft("two_rim.material",
                                       build_material(normalize_source(SQ, SQ, "4", "cyclic_boundary")), "exact")))
    run = Run(reg)
    s = run.apply("two_rim.source.normalize", 1, SQUARE)["output"]
    m = run.apply("test.wrong.material", 1, {}, s)["output"]
    rep = enumerated_candidate_search(run, m, "1/4")
    mat = rep["prerequisites"]["material"]["claims"]
    assert mat["two_rim.material.matches_parent_source"] == "fail"
    # intrinsic material geometry of the height-4 body is not relabeled as false
    assert all(v == "pass" for k, v in mat.items() if k != "two_rim.material.matches_parent_source")
    for row in rep["results"]:
        assert row["full_obligations"] == row["trimmed_obligations"] == "pass"
        assert row["source_linked_full_obligations"] == row["source_linked_trimmed_obligations"] == "fail"


def test_failed_development_cut_copy_blocks_the_trimmed_aggregates():
    reg = registry()
    spec = reg.action("two_rim.develop.static", 1)

    def bad(st, params, seed):
        payload = develop_static(st["payload"])
        payload["cut"]["schema"] = "two_rim.cut/99"
        return StateDraft("two_rim.development", payload, "mixed")
    faulty = Registry()
    register_actions(faulty)
    from glab.check.two_rim_source import register_checkers
    register_checkers(faulty)
    for name in ("two_rim.cut.open", "two_rim.trim.apply"):
        faulty.register_action(reg.action(name, 1))
    faulty.register_action(replace(spec, fn=bad, revision="test-fault-injected-development"))
    register_development_checkers(faulty)
    run = Run(faulty)
    rep = search(run, SQUARE, "1/4")
    for row in rep["results"]:
        assert row["full_claims"][CUT_COPY] == "fail"
        assert row["trimmed_claims"]["two_rim.trim.maps_identical_to_parent"] == "pass"
        assert row["trimmed_obligations"] == "fail"
        assert row["source_linked_trimmed_obligations"] == "fail"


def test_full_domain_failure_is_not_inherited_by_the_trimmed_domain():
    # E11 at delta 49/100: current E9's full development overlaps, but the thick trim removes the
    # interior overlaps; its trimmed status is decided by its own domain only.
    rep = search(new_run(), E11, "49/100")
    row = next(r for r in rep["results"] if r["seam"] == "E9")
    assert row["full_claims"][PAIRS] == "fail"
    assert row["source_linked_full_obligations"] == "fail"
    assert row["trimmed_claims"][PAIRS] == "unknown"
    assert row["trimmed_claims"]["two_rim.development.diagnostic.unglued_pairs_disjoint"] == "pass"
    assert row["source_linked_trimmed_obligations"] == "unknown"


def test_material_without_a_source_parent_is_not_source_linked():
    reg = registry()
    reg.register_action(ActionSpec(
        "test.root.material", 1, None, {}, "test-1",
        lambda st, p, seed: StateDraft("two_rim.material",
                                       build_material(normalize_source(SQ, SQ, "3", "cyclic_boundary")), "exact")))
    run = Run(reg)
    m = run.apply("test.root.material", 1, {})["output"]
    rep = enumerated_candidate_search(run, m, "1/4")
    assert rep["prerequisites"]["source"]["status"] == "no_source_parent"
    assert all(r["source_linked_trimmed_obligations"] == "not_run" for r in rep["results"])


def test_search_duplicated_stage2_claim_names_match_the_checker():
    from glab.check import two_rim_source as s2
    assert SOURCE_OBLIGATIONS == s2.SOURCE_CLAIMS
    assert MATERIAL_OBLIGATIONS == s2.MATERIAL_CLAIMS
    assert DEVELOPMENT_OBLIGATIONS[:2] == ("two_rim.development.record_schema", CUT_COPY)
    from glab.check.two_rim_development import DEV_EXACT
    from glab.two_rim.search import CHECKERS, DEVELOPMENT_EXACT_OBLIGATIONS
    assert DEVELOPMENT_EXACT_OBLIGATIONS == DEV_EXACT
    reg = registry()
    for name, version in CHECKERS.values():
        reg.checker(name, version)  # raises if the search names an unregistered checker version
