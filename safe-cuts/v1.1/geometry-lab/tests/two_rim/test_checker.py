"""Stage 2 task 3 (updated in the D01-D03 repair): the independent checker and mutations it must catch.

Direct calls here pass no dependency context, so the correspondence claim is `unknown` by design;
correspondence is tested through registered runs in test_repairs_d01_d03.py. Mutations that now
break the record schema are caught there first; the oracle is also exercised directly below.
"""
import ast
import copy
from pathlib import Path

import pytest

from glab.check.two_rim_source import _oracle, check_material, check_source

CORR = "two_rim.material.matches_parent_source"
SCHEMA_M = "two_rim.material.record_schema"
from glab.core.records import content_hash
from glab.two_rim.material import build_material
from glab.two_rim.source import normalize_source

MIXED = ([[0, 0], [4, 0], [0, 4]], [[2, -1], [5, -1], [5, 2], [2, 2]], "2")
PERT = "300000000000000000001/100000000000000000000"
CASES = [MIXED, ([[2, 1], [4, 1], [4, 3], [2, 3]], [[0, 0], [2, 0], [2, 2], [0, 2]], "3/2"),
         ([[2, 1], [4, 1], [4, PERT], [2, 3]], [[0, 0], [2, 0], [2, 2], [0, 2]], "3/2")]


def state(kind, payload):
    return {"schema": "glab.state/1", "kind": kind, "parent": None, "representation": "exact", "payload": payload}


def outcomes(claims):
    return {c.predicate: c.outcome for c in claims}


def src_state(top, bottom, h, kind="cyclic_boundary"):
    return state("two_rim.source", normalize_source(top, bottom, h, kind))


def mat_state(top, bottom, h, kind="cyclic_boundary"):
    return state("two_rim.material", build_material(normalize_source(top, bottom, h, kind)))


def rehash(payload):
    payload["identity"] = content_hash({k: v for k, v in payload.items() if k != "identity"})
    return payload


def test_checker_imports_no_generator_code():
    path = Path(__file__).resolve().parents[2] / "glab" / "check" / "two_rim_source.py"
    tree = ast.parse(path.read_text(encoding="utf-8"))
    mods = [n.module or "" for n in ast.walk(tree) if isinstance(n, ast.ImportFrom)]
    mods += [a.name for n in ast.walk(tree) if isinstance(n, ast.Import) for a in n.names]
    assert not any("two_rim" in m.replace("two_rim_source", "") for m in mods), mods
    assert all(m in ("__future__", "fractions", "itertools", "math", "pathlib") or m.startswith("core") or
               m.startswith("glab.core") or m == "" for m in mods), mods


@pytest.mark.parametrize("case", CASES)
def test_all_claims_pass_on_valid_inputs(case):
    for claims in (check_source(src_state(*case), {}), check_material(mat_state(*case), {})):
        assert all(c.outcome == "pass" for c in claims if c.predicate != CORR),             [(c.predicate, c.receipt) for c in claims if c.outcome != "pass"]
        assert all(c.outcome == "unknown" for c in claims if c.predicate == CORR)  # no context supplied
        assert all(c.method == "exact_computation" and c.numeric_domain == "exact_rational" and c.coverage == "all"
                   for c in claims)


def test_hull_input_provenance_is_checked():
    s = src_state(MIXED[0] + [[1, 1], [2, 0]], MIXED[1], "2", "point_set_hull")
    assert set(outcomes(check_source(s, {})).values()) == {"pass"}
    bad = copy.deepcopy(s)
    bad["payload"]["normalization"]["top"]["removed"].pop()
    assert outcomes(check_source(bad, {}))["two_rim.source.normalization_accounts_for_input"] == "fail"
    bad = copy.deepcopy(s)
    bad["payload"]["normalization"]["top"]["removed"][0]["reason"] = "boundary_non_vertex"
    assert outcomes(check_source(bad, {}))["two_rim.source.normalization_accounts_for_input"] == "fail"


def test_source_mutations_detected():
    s = src_state(*MIXED)
    nonconvex = copy.deepcopy(s)
    nonconvex["payload"]["normalized"]["top"] = [["0", "0"], ["1", "1"], ["0", "4"], ["4", "0"]]
    assert outcomes(check_source(nonconvex, {}))["two_rim.source.rims_strictly_convex_clockwise"] == "fail"
    moved = copy.deepcopy(s)
    moved["payload"]["normalized"]["top"][1] = ["0", "5"]
    assert outcomes(check_source(moved, {}))["two_rim.source.normalization_accounts_for_input"] == "fail"
    flat = copy.deepcopy(s)
    flat["payload"]["normalized"]["height"] = "0"
    assert outcomes(check_source(flat, {}))["two_rim.source.height_positive"] == "fail"


def test_material_mutations_detected():
    m = mat_state(*MIXED)
    key = "two_rim.material.facets_match_supporting_plane_oracle"
    inc = "two_rim.material.incidence_and_rings"

    stale = copy.deepcopy(m)
    stale["payload"]["height"] = "3"
    assert outcomes(check_material(stale, {}))["two_rim.material.identity_hash"] == "fail"

    moved = copy.deepcopy(m)
    moved["payload"]["vertices"][0]["xyz"][0] = "1/3"
    assert outcomes(check_material(state("two_rim.material", rehash(moved["payload"])), {}))[key] == "fail"

    dropped = copy.deepcopy(m)
    dropped["payload"]["faces"].pop()
    res = outcomes(check_material(state("two_rim.material", rehash(dropped["payload"])), {}))
    assert res[SCHEMA_M] == "fail" and res[key] == "unknown" and res[inc] == "unknown"  # hinge count != face count
    assert _oracle(dropped["payload"])[0] is False  # the oracle alone also rejects it

    swapped = copy.deepcopy(m)
    e = swapped["payload"]["hinges"][0]
    e["lower"], e["upper"] = e["upper"], e["lower"]
    res = outcomes(check_material(state("two_rim.material", rehash(swapped["payload"])), {}))
    assert res[SCHEMA_M] == "fail" and res[inc] == "unknown"  # a hinge's lower end must be a B vertex


def test_diagonal_split_of_a_trapezoid_is_not_an_original_facet():
    m = mat_state([[2, 1], [4, 1], [4, 3], [2, 3]], [[0, 0], [2, 0], [2, 2], [0, 2]], "3/2")
    p = copy.deepcopy(m["payload"])
    f = p["faces"][0]
    ring = f["boundary"]
    f["boundary"], f["shape"] = ring[:3], "triangle"
    extra = dict(copy.deepcopy(f), id="F_diag", boundary=[ring[0], ring[2], ring[3]])
    p["faces"].insert(1, extra)
    assert outcomes(check_material(state("two_rim.material", rehash(p)), {}))[SCHEMA_M] == "fail"
    assert _oracle(p)[0] is False  # not an original maximal facet


def test_merging_nearly_coplanar_triangles_is_detected():
    m = mat_state([[2, 1], [4, 1], [4, PERT], [2, 3]], [[0, 0], [2, 0], [2, 2], [0, 2]], "3/2")
    p = copy.deepcopy(m["payload"])
    tris = [i for i, f in enumerate(p["faces"]) if f["shape"] == "triangle"]
    a, b = tris[0], tris[1]
    merged = sorted(set(p["faces"][a]["boundary"]) | set(p["faces"][b]["boundary"]))
    p["faces"][a]["boundary"] = merged
    p["faces"][a]["shape"] = "trapezoid"
    del p["faces"][b]
    assert outcomes(check_material(state("two_rim.material", rehash(p)), {}))[SCHEMA_M] == "fail"
    assert _oracle(p)[0] is False  # the two nearly coplanar triangles are distinct exact facets
