"""Stage 2 task 3: original material structure and targeted geometric controls."""
from fractions import Fraction
from pathlib import Path

import pytest

from glab.two_rim.material import build_material
from glab.two_rim.source import normalize_source

SQ = [[0, 0], [2, 0], [2, 2], [0, 2]]
PRISM_TOP = [[2, 1], [4, 1], [4, 3], [2, 3]]
MIXED_TOP, MIXED_BOTTOM = [[0, 0], [4, 0], [0, 4]], [[2, -1], [5, -1], [5, 2], [2, 2]]
PERT = "300000000000000000001/100000000000000000000"


def mat(top, bottom, h="3/2", kind="cyclic_boundary"):
    return build_material(normalize_source(top, bottom, h, kind))


def shapes(m):
    return [f["shape"] for f in m["faces"]]


def test_structure_chain_rings_and_edges():
    m = mat(MIXED_TOP, MIXED_BOTTOM, "2")
    n = len(m["faces"])
    assert n == len(m["hinges"]) == 5
    ends = {e["id"]: (e["lower"], e["upper"]) for e in m["hinges"]}
    ends.update({r["id"]: tuple(r["ends"]) for r in m["rim_edges"]})
    for t, f in enumerate(m["faces"]):
        assert f["entry"] == f"E{t}" and f["exit"] == f"E{(t + 1) % n}"
        ring = f["boundary"]
        assert len(ring) == (3 if f["shape"] == "triangle" else 4)
        for k, eid in enumerate(f["boundary_edges"]):
            assert set(ends[eid]) == {ring[k], ring[(k + 1) % len(ring)]}
    assert {c["id"] for c in m["caps"]} == {"C_TOP", "C_BOTTOM"}
    assert m["identity"].startswith("sha256:")


def test_shared_edge_normals_give_only_trapezoids():
    m = mat(PRISM_TOP, SQ)
    assert shapes(m) == ["trapezoid"] * 4


def test_normals_on_one_rim_give_triangles_and_mixed_shapes():
    m = mat(MIXED_TOP, MIXED_BOTTOM, "2")
    assert shapes(m).count("triangle") == 3 and shapes(m).count("trapezoid") == 2
    assert [1, 1] in [f["outward_ray"] for f in m["faces"]]  # the hypotenuse normal exists only on the top rim


def test_opposite_normals_are_not_merged():
    m = mat([[0, 0], [4, 0], [2, 3]], [[0, 3], [2, 0], [4, 3]], "1")
    rays = [f["outward_ray"] for f in m["faces"]]
    assert [0, -1] in rays and [0, 1] in rays


def test_multi_face_rim_vertex():
    m = mat(MIXED_TOP, MIXED_BOTTOM, "2")
    fan = {v["id"]: sum(v["id"] in f["boundary"] for f in m["faces"]) for v in m["vertices"]}
    assert max(fan.values()) >= 3


def test_tiny_positive_height():
    m = mat(MIXED_TOP, MIXED_BOTTOM, "1/" + "1" + "0" * 30)
    assert m["height"] == "1/" + "1" + "0" * 30 and len(m["faces"]) == 5


def test_perturbation_below_float_resolution_stays_in_the_material():
    m = mat([[2, 1], [4, 1], [4, PERT], [2, 3]], SQ)
    assert shapes(m).count("triangle") == 2 and len(m["faces"]) == 5
    assert any(v["xyz"][1] == PERT for v in m["vertices"])
    assert float(Fraction(PERT)) == 3.0  # the distinction would vanish in float64


def test_identity_ignores_presentation_but_not_geometry():
    base = mat(MIXED_TOP, MIXED_BOTTOM, "2")
    rev = mat(MIXED_TOP[::-1], MIXED_BOTTOM[2:] + MIXED_BOTTOM[:2], "2")
    hull = mat(MIXED_TOP + [[1, 1], [2, 0], [0, 0]], MIXED_BOTTOM + [[3, 0], [5, 0]], "2", "point_set_hull")
    assert base == rev == hull
    assert mat(MIXED_TOP, MIXED_BOTTOM, "3")["identity"] != base["identity"]


def test_no_float_or_trigonometry_decides_topology():
    root = Path(__file__).resolve().parents[2] / "glab"
    # Scoped to the exact Stage 2 source/material modules; Stage 3 float modules (develop.py and the
    # development checker) are approximate placements by design and are tested separately.
    exact = [root / "two_rim" / n for n in ("source.py", "material.py", "actions.py")] + \
        [root / "check" / "two_rim_source.py"]
    for path in exact:
        text = path.read_text(encoding="utf-8")
        for token in ("float(", "import math\n", "atan", "sqrt", "numpy"):
            assert token not in text, (path.name, token)


def test_material_vertices_equal_parent_source_rims():
    src = normalize_source(MIXED_TOP, MIXED_BOTTOM, "2", "cyclic_boundary")
    m = build_material(src)
    top = [v["xyz"][:2] for v in m["vertices"] if v["rim"] == "top"]
    bottom = [v["xyz"][:2] for v in m["vertices"] if v["rim"] == "bottom"]
    assert top == src["normalized"]["top"] and bottom == src["normalized"]["bottom"]
    assert all(v["xyz"][2] == ("2" if v["rim"] == "top" else "0") for v in m["vertices"])


def test_unsupported_source_schema_rejected():
    from glab.two_rim.material import MaterialError
    with pytest.raises(MaterialError):
        build_material({"schema": "two_rim.source/9"})
