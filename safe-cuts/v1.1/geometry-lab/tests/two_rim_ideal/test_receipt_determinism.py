"""Stage 4B: repeated serialized results are byte-identical; nothing time-dependent enters a claim or a result."""
from glab.core.records import canonical_json
from glab.ideal_check.checker import IDEAL_POLICY
from glab.two_rim.ideal_search import ideal_candidate_search

from .helpers import E11, E11_DELTA, IDEAL_CHECKER, material, new_run


def _search():
    run = new_run()
    _, m = material(run, E11)
    result = ideal_candidate_search(run, m, E11_DELTA, expected_policy=IDEAL_POLICY, seams=["E4", "E9"])
    return run, result


def test_two_independent_runs_serialize_identically():
    run1, res1 = _search()
    run2, res2 = _search()
    assert canonical_json(res1) == canonical_json(res2)
    ev1 = [e for e in run1.evidence if e["checker"] == IDEAL_CHECKER[0]]
    ev2 = [e for e in run2.evidence if e["checker"] == IDEAL_CHECKER[0]]
    assert canonical_json(ev1) == canonical_json(ev2) and len(ev1) == 16
    assert run1.to_record()["states"] == run2.to_record()["states"]


def test_results_carry_no_timing_or_environment_values():
    _, res = _search()
    text = canonical_json(res)
    for token in ("seconds", "timing", "perf_counter", "python_version", "platform"):
        assert token not in text, token
