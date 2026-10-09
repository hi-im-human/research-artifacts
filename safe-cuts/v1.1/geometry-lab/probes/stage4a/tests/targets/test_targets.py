"""Stage 4A targets (isolated prototype), run only after the controls in tests/controls/ pass."""
import pytest

from probes.stage4a.run_probe import historical_reference, scan, square_prism, targets
from probes.stage4a.specimens import E11, prepare


@pytest.fixture(scope="module")
def prepared():
    return prepare(E11)


@pytest.fixture(scope="module")
def t(prepared):
    return targets(prepared)


@pytest.fixture(scope="module")
def scanned(prepared):
    return scan(prepared)[0]


def test_t1_retained_neighbour_contact_is_decided_exactly(t):
    row = t["T1"]["row"]
    assert t["T1"]["source_linked"] is True
    assert row["outcome"] == "pass" and row["method"] == "shared_hinge_exact"
    sh = row["shared_hinge"]
    assert sorted(sh["sides"].values()) == [-1, 1] and not sh["problems"]
    # The same pair on intervals alone stays unknown at every precision: contact along the shared hinge.
    only = t["T1"]["same_pair_intervals_only"]
    assert only["outcome"] == "unknown" and only["reason"] == "budget_exhausted"
    assert [a["bits"] for a in only["attempts"]] == [16, 32, 64, 128, 256, 512]


def test_t2_robust_separation_is_certified_by_an_axis(t):
    row = t["T2"]["row"]
    assert row["outcome"] == "pass" and row["method"] == "separating_axis"
    assert row["certificate"]["euclidean_gap_lower_bound"] > 0


def test_t3_known_overlap_is_certified_by_an_interior_witness(t):
    row = t["T3"]["row"]
    assert sorted(row["pair"]) == ["F10", "F7"]
    assert row["outcome"] == "fail" and row["method"] == "interior_witness"
    assert row["certificate"]["cross_lower_bound"] > 0


def test_float_placement_is_a_diagnostic_near_the_ideal_enclosure(t):
    d = t["E9_float_placement_vs_ideal_enclosure"]
    assert d["label"].startswith("diagnostic") and d["max_distance"] < 1e-9 and d["mirror"] is False


def test_square_prism_is_decided_on_the_exact_path():
    res = square_prism()["seams"]
    assert len(res) == 8
    for key, s in res.items():
        assert s["seam_verdict"] == "pass", key
        assert s["all_box_widths_zero"], key
        assert "shared_hinge_exact" in s["methods"] and "separating_axis" in s["methods"], key


def test_scan_decides_every_pair_of_every_seam(scanned):
    assert len(scanned) == 11
    for seam, s in scanned.items():
        assert s["source_linked"] is True, seam
        assert s["shared_hinge_pass"] == 10, seam
        assert s["unknown"] == [], seam
        assert s["seam_verdict"] in ("pass", "fail"), seam


def test_historical_reference_after_classification(prepared, scanned):
    ref = historical_reference(prepared, scanned)
    assert all(r["comparison"] == "agree" for r in ref["classes"]), ref["classes"]
    assert len(ref["historical_witness_points"]) == 4
    assert all(w["certified_inside_both_faces_of_D"] for w in ref["historical_witness_points"])
