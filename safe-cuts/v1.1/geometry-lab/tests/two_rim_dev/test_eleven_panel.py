"""Stage 3 required natural-overlap regression: the historical exact eleven-panel source."""
from fractions import Fraction

import numpy as np
import pytest

from glab.two_rim.search import enumerated_candidate_search
from tests.two_rim_dev.eleven_panel import build_mapping, load_certificate, mapped_expectations
from tests.two_rim_dev.helpers import E11, E11_DELTA, material, new_run

PAIRS = "two_rim.development.face_interiors_disjoint_all_pairs"
CERT = load_certificate()


@pytest.fixture(scope="module")
def searched():
    run = new_run()
    s, m = material(run, E11)
    mat = run.get(m)["payload"]
    mapping = build_mapping(mat, CERT)
    report = enumerated_candidate_search(run, m, E11_DELTA)
    return run, mat, mapping, mapped_expectations(CERT, mapping), report


def test_source_matches_the_historical_certificate(searched):
    run, mat, mapping, exp, report = searched
    assert len(mat["faces"]) == 11 and mapping["n"] == 11
    assert exp["delta"] == E11_DELTA == "1/10000" and exp["height"] == mat["height"] == "1/10000"
    tops = sorted(tuple(v["xyz"][:2]) for v in mat["vertices"] if v["rim"] == "top")
    assert tops == sorted(tuple(p) for p in CERT["top"])


def test_search_is_labeled_and_covers_every_seam(searched):
    run, mat, mapping, exp, report = searched
    assert report["label"] == "enumerated_candidate_search" and "not the manuscript" in report["disclaimer"]
    assert [r["seam"] for r in report["results"]] == [e["id"] for e in mat["hinges"]]


def test_cut6_strict_overlap_is_not_a_numerical_pass(searched):
    run, mat, mapping, exp, report = searched
    row = next(r for r in report["results"] if r["seam"] == exp["cut6"]["seam"])
    assert row["trimmed_claims"][PAIRS] == "fail"
    ev = next(e for e in run.evidence if e["subject"] == row["trimmed"] and e["claim"] == PAIRS)
    pair = sorted(exp["cut6"]["faces"])
    hit = [r for r in ev["receipt"]["rows"] if sorted(r["pair"]) == pair]
    assert hit and hit[0]["outcome"] == "fail" and hit[0]["reason"] == "interior_overlap"


def test_historical_witness_point_is_interior_to_both_mapped_faces(searched):
    """Place the historical cut-6 frame onto ours via the seam copy of the first panel, then test the point."""
    run, mat, mapping, exp, report = searched
    row = next(r for r in report["results"] if r["seam"] == exp["cut6"]["seam"])
    trimmed = run.get(row["trimmed"])["payload"]
    maps = {m["face"]: m for m in trimmed["maps"]}
    pts = {k: np.array([float(Fraction(c)) for c in v["xyz"]]) for k, v in trimmed["trim_points"].items()}

    def image(face, key):
        m = maps[face]
        return np.array(m["linear"]) @ pts[key] + np.array(m["offset"])
    first = run.get(row["cut"])["payload"]["face_order"][0]
    seam = exp["cut6"]["seam"]
    b0, a0 = image(first, f"{seam}@lo"), image(first, f"{seam}@hi")  # historical (0,0) and (L,0)
    ex = (a0 - b0) / np.linalg.norm(a0 - b0)
    ey = np.array([-ex[1], ex[0]])
    nxt = run.get(row["cut"])["payload"]["face_order"][0]
    exit_hinge = next(f["exit"] for f in mat["faces"] if f["id"] == nxt)
    if np.dot(image(first, f"{exit_hinge}@lo") - b0, ey) < 0:  # historical first panel lies at +y
        ey = -ey
    px, py = (float(Fraction(c)) for c in exp["cut6"]["point"])
    y = b0 + px * ex + py * ey
    faces = {f["face"]: f["boundary"] for f in trimmed["faces"]}
    for face in exp["cut6"]["faces"]:
        ring = np.array([image(face, k) for k in faces[face]])
        def cross2(u, v):
            return u[0] * v[1] - u[1] * v[0]
        crosses = [cross2(ring[(i + 1) % 4] - ring[i], y - ring[i]) for i in range(4)]
        assert all(c > 1e-3 for c in crosses) or all(c < -1e-3 for c in crosses), (face, crosses)


def test_classification_comparison_with_the_historical_certificate(searched):
    run, mat, mapping, exp, report = searched
    ours = {r["seam"]: r["trimmed_claims"][PAIRS] for r in report["results"]}
    unsafe_detected = [s for s in exp["unsafe_seams"] if ours[s] == "fail"]
    assert unsafe_detected, "at least one naturally unsafe seam must be detected without mutation"
    assert all(ours[s] != "pass" for s in exp["unsafe_seams"])  # no historical overlap receives a pass
    assert all(ours[s] != "fail" for s in exp["safe_seams"]), {s: ours[s] for s in exp["safe_seams"]}


def test_checker_and_generator_never_see_the_historical_labels():
    from pathlib import Path
    root = Path(__file__).resolve().parents[2] / "glab"
    text = "\n".join(p.read_text(encoding="utf-8") for p in root.rglob("*.py"))
    for token in ("beveled", "39037647", "unsafe_cuts", "SAFE_CUTS", "1693/100"):
        assert token not in text, token
