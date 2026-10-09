"""Task 4: glab.core imports the standard library only (plus its own modules)."""
import ast
import sys
from pathlib import Path

CORE = Path(__file__).resolve().parents[2] / "glab" / "core"


def _imports(path):
    tree = ast.parse(path.read_text(encoding="utf-8"))
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for a in node.names:
                yield 0, a.name
        elif isinstance(node, ast.ImportFrom):
            yield node.level, node.module or ""


def test_core_uses_only_stdlib_and_itself():
    files = sorted(CORE.glob("*.py"))
    assert {f.name for f in files} >= {"numbers.py", "records.py", "registry.py", "evidence.py", "runfile.py"}
    bad = []
    for f in files:
        for level, mod in _imports(f):
            top = mod.split(".")[0]
            if level > 0:
                continue  # relative import inside glab.core
            if top == "__future__" or top in sys.stdlib_module_names:
                continue
            bad.append((f.name, mod))
    assert bad == []


def test_core_names_no_geometry_numeric_or_viewer_dependency():
    text = "\n".join(f.read_text(encoding="utf-8") for f in CORE.glob("*.py"))
    for forbidden in ("numpy", "scipy", "compas", "trimesh", "polyscope", "midsection", "two_rim",
                      "matplotlib", "importlib", "eval(", "exec(", "__import__", "subprocess"):
        assert forbidden not in text, forbidden
