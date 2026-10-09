"""Stage 2: golden comparison with the pinned originals, and the independent oracle, on fixtures + 200 random."""
import pytest

from glab.check.two_rim_source import check_material, check_source
from glab.two_rim.material import build_material
from glab.two_rim.source import normalize_source
from tests.two_rim.golden_support import checked_claims, compare, fixtures, load_pinned, random_cases

NFI, NCS = load_pinned()
FIXTURES = fixtures()
CASES, STATS = random_cases()


def _all_pass(case):
    claims = checked_claims(case)
    assert len(claims) == 9  # 4 source + 5 material claims (v2), incl. matches_parent_source
    return [(c.predicate, c.receipt) for c in claims if c.outcome != "pass"]


def _golden_ok(r):
    return r["hull_match"] and r["hinges_match"] and r["rays_match"] and r["facets_match"]


@pytest.mark.parametrize("name", sorted(FIXTURES))
def test_fixture_matches_pinned_originals(name):
    r = compare(NFI, NCS, **FIXTURES[name])
    assert _golden_ok(r), r


@pytest.mark.parametrize("name", sorted(FIXTURES))
def test_fixture_passes_independent_oracle(name):
    assert _all_pass(FIXTURES[name]) == []


def test_random_generator_yields_200_valid_cases_with_counted_rejections():
    assert STATS["valid"] == len(CASES) == 200
    assert STATS["attempts"] == 200 + sum(STATS["rejected"].values())
    assert {c["input_kind"] for c in CASES} == {"cyclic_boundary", "point_set_hull"}


def test_random_cases_match_pinned_originals():
    bad = []
    for i, case in enumerate(CASES):
        r = compare(NFI, NCS, **case)
        if not _golden_ok(r):
            bad.append((i, case, r))
    assert bad == []


def test_random_cases_pass_independent_oracle():
    bad = [(i, fails) for i, case in enumerate(CASES) if (fails := _all_pass(case))]
    assert bad == []


def test_golden_comparison_can_fail(monkeypatch):
    """Negative control: a wrong hinge endpoint must break the comparison."""
    from tests.two_rim import golden_support

    def wrong(source):
        m = build_material(source)
        e = m["hinges"][0]
        others = [v["id"] for v in m["vertices"] if v["rim"] == "bottom" and v["id"] != e["lower"]]
        e["lower"] = others[0]
        return m
    monkeypatch.setattr(golden_support, "build_material", wrong)
    assert not compare(NFI, NCS, **FIXTURES["F2_nonnested_mixed"])["hinges_match"]


def test_supplementary_shared_normal_family():
    from tests.two_rim.golden_support import shared_normal_cases
    cases = shared_normal_cases()
    results = [compare(NFI, NCS, **c) for c in cases]
    assert all(_golden_ok(r) for r in results)
    assert all(_all_pass(c) == [] for c in cases)
    assert all(r["triangles"] == 0 for r in results[0::2])  # pure homothety: all trapezoids
    assert any(r["triangles"] > 0 for r in results[1::2])   # with an extra point: mixed
