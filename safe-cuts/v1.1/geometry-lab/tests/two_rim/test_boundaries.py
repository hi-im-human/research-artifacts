"""Stage 2: package import boundaries (core domain-free; checker independent of the generator)."""
import ast
import sys
from pathlib import Path

GLAB = Path(__file__).resolve().parents[2] / "glab"


def imports(pkg):
    out = []
    for path in sorted((GLAB / pkg).glob("*.py")):
        for node in ast.walk(ast.parse(path.read_text(encoding="utf-8"))):
            if isinstance(node, ast.Import):
                out += [(path.name, 0, a.name) for a in node.names]
            elif isinstance(node, ast.ImportFrom):
                out.append((path.name, node.level, node.module or ""))
    return out


def stdlib(mod):
    return mod.split(".")[0] in sys.stdlib_module_names or mod == "__future__"


def test_core_imports_no_domain_or_checker():
    for name, level, mod in imports("core"):
        assert (level == 1 and not mod.startswith(("two_rim", "check"))) or (level == 0 and stdlib(mod)), (name, mod)


def test_two_rim_imports_only_stdlib_core_and_itself():
    for name, level, mod in imports("two_rim"):
        # Stage 3 adds sibling modules (cut, develop, trim, dev_actions); still stdlib + core + siblings only.
        ok = (level == 0 and stdlib(mod)) or \
             (level == 1 and mod in ("source", "material", "cut", "develop", "trim", "dev_actions")) or \
             (level == 2 and mod.startswith("core"))
        assert ok, (name, level, mod)


def test_checker_imports_only_stdlib_and_core():
    for name, level, mod in imports("check"):
        numpy_ok = name == "two_rim_development.py" and mod == "numpy"  # Stage 3: pinned NumPy backend only here
        assert (level == 0 and (stdlib(mod) or numpy_ok)) or (level == 2 and mod.startswith("core")), (name, level, mod)
