"""Stage 3: static view consumes saved data only; package import boundaries."""
import ast
import json
import sys
from pathlib import Path

from glab.core.runfile import load_run
from glab.two_rim.view_export import view_data
from glab.view.static import render_obj, render_svg
from tests.two_rim_dev.helpers import developed, fixture, new_run

GLAB = Path(__file__).resolve().parents[2] / "glab"


def imports(path):
    out = []
    for node in ast.walk(ast.parse(path.read_text(encoding="utf-8"))):
        if isinstance(node, ast.Import):
            out += [(0, a.name) for a in node.names]
        elif isinstance(node, ast.ImportFrom):
            out.append((node.level, node.module or ""))
    return out


def stdlib(mod):
    return mod.split(".")[0] in sys.stdlib_module_names or mod == "__future__"


def test_view_is_built_from_a_saved_run_and_renders_polygons(tmp_path):
    run = new_run()
    d = developed(run, fixture("F2_nonnested_mixed"), seam="E1", delta="1/4")
    ev = run.check("two_rim.check.trimmed_development", 2, d["trimmed"], {})
    p = tmp_path / "run.json"
    loaded = load_run(p, expected_digest=run.save(p))
    view = view_data(loaded, d["trimmed"])
    assert view["subject_state"] == d["trimmed"] and view["derived"].startswith("display cache")
    assert {e["claim"]: e["outcome"] for e in view["evidence"]} == {e["claim"]: e["outcome"] for e in ev}
    text = json.dumps(view)
    svg = render_svg(json.loads(text))
    mat = run.get(d["material"])["payload"]
    for f in mat["faces"]:
        assert f">{f['id']}<" in svg
    assert "seam" in svg and "face_interiors_disjoint_all_pairs" in svg
    band, planar = render_obj(json.loads(text))
    assert sum(1 for l in band.splitlines() if l.startswith("f ")) == len(mat["faces"])
    assert [len(l.split()) - 1 for l in planar.splitlines() if l.startswith("f ")] == [4] * len(mat["faces"])
    band_faces = [len(l.split()) - 1 for l in band.splitlines() if l.startswith("f ")]
    assert sorted(band_faces) == sorted(len(f["boundary"]) for f in mat["faces"])  # original polygons, no triangulation


def test_viewer_imports_only_the_standard_library():
    for level, mod in imports(GLAB / "view" / "static.py"):
        assert level == 0 and stdlib(mod), mod


def test_development_checker_never_imports_the_generator():
    for level, mod in imports(GLAB / "check" / "two_rim_development.py"):
        ok = (level == 0 and (stdlib(mod) or mod == "numpy")) or (level == 2 and mod.startswith("core"))
        assert ok, (level, mod)


def test_development_generator_is_stdlib_and_core_only():
    for name in ("cut.py", "develop.py", "trim.py", "dev_actions.py", "search.py", "view_export.py"):
        for level, mod in imports(GLAB / "two_rim" / name):
            ok = (level == 0 and stdlib(mod)) or (level == 1 and mod in ("cut", "develop", "trim", "dev_actions")) \
                or (level == 2 and mod.startswith("core"))
            assert ok, (name, level, mod)
    text = "\n".join(p.read_text(encoding="utf-8") for p in (GLAB / "two_rim").glob("*.py"))
    assert "PhysicalBridge(" not in text and "import midsection" not in text and "import numpy" not in text


def test_search_obligation_names_match_checker_claims():
    # search.py duplicates the claim names so it never imports the checker; this pins the two lists together.
    from glab.check import two_rim_development as chk
    from glab.two_rim import search
    assert search.CUT_OBLIGATIONS == chk.CUT_CLAIMS
    assert search.DEVELOPMENT_OBLIGATIONS == chk.DEV_EXACT + chk.NUMERICAL
    assert search.TRIM_OBLIGATIONS == chk.TRIM_EXACT + chk.NUMERICAL
    assert not set(chk.DIAGNOSTICS) & set(search.DEVELOPMENT_OBLIGATIONS + search.TRIM_OBLIGATIONS)
