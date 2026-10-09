"""Stage 4B: save, load and replay of the ideal lane, with policy and revision checks (mismatches are rejected)."""
import json

import pytest

from glab.core.evidence import validate_evidence
from glab.core.runfile import RunIntegrityError, load_run, replay
from glab.ideal_check.checker import IDEAL_CHECKER_REVISION, IDEAL_POLICY, enclosure_policy
from glab.two_rim.ideal_search import ideal_candidate_search, loaded_ideal_obligations

from .helpers import E11, E11_DELTA, IDEAL_CHECKER, SQUARE, ideal_lane, material, new_run, registry


@pytest.fixture(scope="module")
def saved(tmp_path_factory):
    run = new_run()
    _, m = material(run, SQUARE)
    ideal_candidate_search(run, m, "1/4", expected_policy=IDEAL_POLICY)
    lane = ideal_lane(run, E11, "E9", E11_DELTA)
    for name, version, subject in (("two_rim.check.source", 2, lane["source"]),
                                   ("two_rim.check.material", 2, lane["material"]),
                                   ("two_rim.check.cut", 1, lane["cut"]), (*IDEAL_CHECKER, lane["ideal"])):
        run.check(name, version, subject, {})
    path = tmp_path_factory.mktemp("ideal-run") / "run.json"
    digest = run.save(path)
    return run, path, digest, lane


def test_saved_run_loads_against_its_digest_and_replays_exactly(saved):
    run, path, digest, _ = saved
    loaded = load_run(path, expected_digest=digest)
    assert loaded.anchor == "matched" and loaded.integrity == "internally_consistent"
    result = replay(loaded, registry())
    assert result["outcome"] == "reproduced" and result["run_digest_reproduced"] is True
    assert result["run"].evidence == run.evidence


def test_loaded_evidence_is_current_under_the_published_policy_and_verdicts_survive(saved):
    _, path, digest, lane = saved
    loaded = load_run(path, expected_digest=digest)
    ideal_ev = [e for e in loaded.record["evidence"] if e["checker"] == IDEAL_CHECKER[0]]
    policy_claims = [e for e in ideal_ev if e["tolerances"] is not None]
    assert policy_claims and all(e["checker_revision"] == IDEAL_CHECKER_REVISION for e in ideal_ev)
    for e in policy_claims:
        assert validate_evidence(e, loaded.store, registry(), expected_tolerances=IDEAL_POLICY)["status"] == "current"
    ob = loaded_ideal_obligations(loaded, registry(), lane["ideal"], expected_policy=IDEAL_POLICY)
    assert ob["outcome"] == "fail" and ob["ideal_geometric_verdict"]["verdict"] == "fail"


def test_a_policy_mismatch_is_rejected_on_load(saved):
    _, path, digest, lane = saved
    loaded = load_run(path, expected_digest=digest)
    other = enclosure_policy((16, 32, 64, 128, 256, 512, 1024))
    e = next(e for e in loaded.record["evidence"] if e["tolerances"] is not None)
    assert validate_evidence(e, loaded.store, registry(), expected_tolerances=other)["status"] == "policy_mismatch"
    ob = loaded_ideal_obligations(loaded, registry(), lane["ideal"], expected_policy=other)
    assert ob["ideal_geometric_verdict"]["verdict"] == "not_determined" and ob["outcome"] == "unknown"


def test_a_revision_mismatch_is_rejected_on_load_and_not_replayed(saved):
    _, path, digest, lane = saved
    loaded = load_run(path, expected_digest=digest)
    foreign = registry(revisions={IDEAL_CHECKER: "sha256:" + "0" * 64})
    e = next(e for e in loaded.record["evidence"] if e["checker"] == IDEAL_CHECKER[0])
    assert validate_evidence(e, loaded.store, foreign)["status"] == "checker_mismatch"
    ob = loaded_ideal_obligations(loaded, foreign, lane["ideal"], expected_policy=IDEAL_POLICY)
    assert ob["ideal_geometric_verdict"]["verdict"] == "not_determined"
    result = replay(loaded, foreign)
    assert result["outcome"] == "not_run"
    assert {r["reason"] for r in result["checks"] if r["name"] == IDEAL_CHECKER[0]} == \
        {"checker revision not available"}


def test_a_stale_prerequisite_revision_blocks_the_verdict(saved):
    _, path, digest, lane = saved
    loaded = load_run(path, expected_digest=digest)
    stale = registry(revisions={("two_rim.check.material", 2): "sha256:" + "1" * 64})
    ob = loaded_ideal_obligations(loaded, stale, lane["ideal"], expected_policy=IDEAL_POLICY)
    material_rows = [r for r in ob["requirements"] if r["role"] == "material"]
    assert all(r["outcome"] == "unknown" and r["invalid"] for r in material_rows)
    assert ob["ideal_geometric_verdict"]["verdict"] == "not_determined"


def test_an_edited_ideal_outcome_is_an_integrity_failure(saved, tmp_path):
    _, path, _, _ = saved
    data = json.loads(path.read_text(encoding="ascii"))
    e = next(e for e in data["evidence"] if e["claim"] == "two_rim.ideal.remaining_pairs_interiors_disjoint"
             and e["outcome"] == "fail")
    e["outcome"] = "pass"
    bad = tmp_path / "edited.json"
    bad.write_text(json.dumps(data), encoding="ascii")
    with pytest.raises(RunIntegrityError):
        load_run(bad)
