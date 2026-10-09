"""Stage 2 task 2: exact source normalization (glab.two_rim.source)."""
import copy

import pytest

from glab.two_rim.source import SourceInputError, normalize_source

SQ_CCW = [[0, 0], [2, 0], [2, 2], [0, 2]]           # counterclockwise
SQ_CW = [[0, 0], [0, 2], [2, 2], [2, 0]]            # clockwise, starts at the minimum
TRI = [[0, 0], [4, 0], [0, 4]]


def norm(top=SQ_CCW, bottom=TRI, height="3/2", kind="cyclic_boundary"):
    return normalize_source(top, bottom, height, kind)


def test_payload_shape_and_conventions():
    s = norm()
    assert s["schema"] == "two_rim.source/1" and s["units"] == "unitless"
    assert s["number_domain"] == "exact_rational" and "z = 0" in s["coordinate_convention"]
    assert s["input"] == {"top": SQ_CCW, "bottom": TRI, "height": "3/2", "input_kind": "cyclic_boundary"}
    assert s["normalized"]["height"] == "3/2"


def test_cyclic_ccw_is_reversed_to_clockwise_from_the_minimum():
    s = norm()
    assert s["normalized"]["top"] == [["0", "0"], ["0", "2"], ["2", "2"], ["2", "0"]]
    d = s["normalization"]["top"]
    assert d == {"input_kind": "cyclic_boundary", "input_count": 4, "input_orientation": "counterclockwise",
                 "reversed": True, "start_input_index": 0, "removed": []}


def test_cyclic_presentations_normalize_identically():
    base = norm(top=SQ_CW)["normalized"]
    for top in (SQ_CW[2:] + SQ_CW[:2], SQ_CCW, SQ_CCW[1:] + SQ_CCW[:1], SQ_CW[::-1]):
        assert norm(top=top)["normalized"] == base
    rotated = norm(top=SQ_CW[2:] + SQ_CW[:2])["normalization"]["top"]
    assert rotated["reversed"] is False and rotated["start_input_index"] == 2


def test_exact_spellings_normalize_to_canonical_strings():
    s = norm(top=[["0.0", 0], ["1/2", "0.5"], ["0", "2/2"]], height="0.25")
    assert s["normalized"]["top"] == [["0", "0"], ["0", "1"], ["1/2", "1/2"]]
    assert s["normalized"]["height"] == "1/4"


def test_tiny_perturbation_stays_exact():
    p = "300000000000000000001/100000000000000000000"
    s = norm(top=[[2, 1], [4, 1], [4, p], [2, 3]], bottom=SQ_CCW)
    assert ["4", p] in s["normalized"]["top"]


@pytest.mark.parametrize("bad,msg", [
    ({"top": [[0, 0], [1], [0, 1]]}, "exactly two coordinates"),
    ({"top": [[0, 0], [1, 0, 0], [0, 1]]}, "exactly two coordinates"),
    ({"top": [[0, 0], "1,0", [0, 1]]}, "exactly two coordinates"),
    ({"top": "not a list"}, "list of points"),
    ({"top": []}, "at least 3"),
    ({"top": [[0, 0], [1, 0]]}, "at least 3"),
    ({"top": [[0, 0.5], [1, 0], [0, 1]]}, "exact"),
    ({"top": [[True, 0], [1, 0], [0, 1]]}, "exact"),
    ({"height": "0"}, "height must be positive"),
    ({"height": "-1/3"}, "height must be positive"),
    ({"height": 1.5}, "exact"),
    ({"kind": "mesh"}, "input_kind"),
])
def test_invalid_inputs_fail_clearly(bad, msg):
    kw = {"top": SQ_CCW, "bottom": TRI, "height": "1", "kind": "cyclic_boundary", **bad}
    with pytest.raises(SourceInputError, match=msg):
        norm(**kw)


@pytest.mark.parametrize("top,msg", [
    ([[0, 0], [1, 0], [2, 0], [2, 2], [0, 2]], "not strictly convex"),       # collinear boundary point
    ([[0, 0], [2, 0], [2, 2], [0, 2], [0, 0]], "repeats a point"),           # repeated closing point
    ([[0, 0], [4, 0], [1, 1], [0, 4]], "not strictly convex"),              # reflex vertex
    ([[0, 0], [2, 2], [2, 0], [0, 2]], "not strictly convex"),              # bowtie
    ([[0, 0], [5, 3], [-1, 3], [4, 0], [2, 5]], "not a simple"),            # star: winds twice
    ([[0, 0], [1, 1], [2, 2]], "empty interior"),                          # collinear whole rim
])
def test_malformed_cyclic_input_is_never_repaired(top, msg):
    with pytest.raises(SourceInputError, match=msg):
        norm(top=top)


def test_point_set_hull_records_every_removed_point():
    pts = [[0, 0], [2, 0], [1, 0], [1, 1], [2, 2], [0, 2], [2, 0], [0, 1]]
    s = norm(top=pts, kind="point_set_hull")
    assert s["normalized"]["top"] == [["0", "0"], ["0", "2"], ["2", "2"], ["2", "0"]]
    d = s["normalization"]["top"]
    assert d["input_kind"] == "point_set_hull" and d["input_count"] == 8 and d["hull_vertex_count"] == 4
    assert d["removed"] == [
        {"input_index": 2, "point": ["1", "0"], "reason": "boundary_non_vertex"},
        {"input_index": 3, "point": ["1", "1"], "reason": "interior"},
        {"input_index": 6, "point": ["2", "0"], "reason": "duplicate"},
        {"input_index": 7, "point": ["0", "1"], "reason": "boundary_non_vertex"},
    ]


def test_point_set_hull_needs_positive_area():
    with pytest.raises(SourceInputError, match="empty interior"):
        norm(bottom=[[0, 0], [1, 1], [3, 3], [1, 1]], kind="point_set_hull")
    with pytest.raises(SourceInputError, match="empty interior"):
        norm(bottom=[[5, 5]], kind="point_set_hull")


def test_inputs_are_not_mutated():
    top = copy.deepcopy(SQ_CCW)
    norm(top=top)
    assert top == SQ_CCW
