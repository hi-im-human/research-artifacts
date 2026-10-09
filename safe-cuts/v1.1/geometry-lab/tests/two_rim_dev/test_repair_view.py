"""Stage 3 repair S01: the view description keeps local and source-linked statuses separate."""
from glab.core.runfile import load_run
from glab.two_rim.search import enumerated_candidate_search
from glab.two_rim.view_export import view_data
from glab.view.static import render_svg
from tests.two_rim_dev.helpers import fixture, material, new_run


def test_view_carries_local_and_source_linked_statuses(tmp_path):
    run = new_run()
    _, m = material(run, fixture("F2_nonnested_mixed"))
    row = enumerated_candidate_search(run, m, "1/4")["results"][1]
    p = tmp_path / "run.json"
    loaded = load_run(p, expected_digest=run.save(p))
    statuses = {"local": row["trimmed_obligations"], "source_linked": row["source_linked_trimmed_obligations"]}
    view = view_data(loaded, row["trimmed"], statuses=statuses)
    assert view["schema"] == "geometry-lab.view/3" and view["statuses"] == statuses
    svg = render_svg(view)
    assert "local chain status" in svg and "source-linked status" in svg


def test_view_without_statuses_says_so(tmp_path):
    run = new_run()
    _, m = material(run, fixture("F2_nonnested_mixed"))
    row = enumerated_candidate_search(run, m, "1/4")["results"][0]
    p = tmp_path / "run.json"
    loaded = load_run(p, expected_digest=run.save(p))
    view = view_data(loaded, row["trimmed"])
    assert view["statuses"] is None
    assert "aggregate statuses not supplied" in render_svg(view)
