"""Stage 4B: provenance of the ported geometry, import boundaries, the pinned contract and the checker revision."""
import ast
import hashlib
import sys
from pathlib import Path

from glab.ideal_check.checker import ANALYTIC_DEPENDENCY, IDEAL_CHECKER_REVISION, IDEAL_POLICY
from glab.core.registry import source_revision

ENGINE = Path(__file__).resolve().parents[2]
GLAB = ENGINE / "glab"
GEOMETRY = GLAB / "ideal_check" / "geometry.py"
PROTO = ENGINE / "probes" / "stage4a"
CONTRACT = ENGINE / "IDEAL-DEVELOPMENT-CONTRACT.md"

# Ported unchanged (AST-equal, docstrings included) from ideal.py (blob de3cae44) and classify.py (blob c82b5873).
FROM_IDEAL = ["sub", "dot", "cross", "FrozenDict", "freeze", "thaw", "ExactModel", "model_from_payloads",
              "face_checks", "_face_ok", "shared_hinge_decision", "enclose"]
FROM_CLASSIFY = ["SCHEDULE", "_mid", "_dot", "_signed_area2", "certify_separation", "_clip", "certify_witness",
                 "point_in_both", "decide_boxes", "_Enclosures", "classify_pair", "seam_total", "to_json"]
# Deliberately adapted or new (reviewed as new code): classify_seam (no isolated-prototype label),
# local_premises and verify_certificate (new), and everything Run-bound in the prototype is not ported.
ADAPTED_OR_NEW = {"classify_seam", "local_premises", "verify_certificate"}


def _defs(path):
    out = {}
    for node in ast.parse(path.read_text(encoding="utf-8")).body:
        if isinstance(node, (ast.FunctionDef, ast.ClassDef)):
            out[node.name] = ast.dump(node)
        elif isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            out[node.targets[0].id] = ast.dump(node)
    return out


def test_ported_functions_are_ast_identical_to_the_accepted_prototype():
    mine = _defs(GEOMETRY)
    ideal, classify = _defs(PROTO / "ideal.py"), _defs(PROTO / "classify.py")
    for name in FROM_IDEAL:
        assert mine[name] == ideal[name], name
    for name in FROM_CLASSIFY:
        assert mine[name] == classify[name], name
    assert ADAPTED_OR_NEW <= set(mine)
    assert "load_subject" not in mine and "Subject" not in mine and "applies_to" not in mine


def _imports(path):
    for node in ast.walk(ast.parse(path.read_text(encoding="utf-8"))):
        if isinstance(node, ast.Import):
            for a in node.names:
                yield 0, a.name
        elif isinstance(node, ast.ImportFrom):
            yield node.level, node.module or ""


def test_checker_side_never_imports_the_generator_numpy_or_the_prototype():
    for path in (GLAB / "ideal_check" / "geometry.py", GLAB / "ideal_check" / "checker.py"):
        for level, mod in _imports(path):
            if level == 0:
                top = mod.split(".")[0]
                assert top == "__future__" or top in sys.stdlib_module_names, (path.name, mod)
            else:
                assert mod.split(".")[0] in ("core", "rigorous", "geometry"), (path.name, mod)
        text = path.read_text(encoding="utf-8")
        for forbidden in ("importlib", "__import__", "exec(", "eval("):
            assert forbidden not in text, (path.name, forbidden)


def test_generator_side_does_no_geometry_and_imports_only_the_core():
    for path in (GLAB / "two_rim" / "ideal_actions.py",):
        for level, mod in _imports(path):
            if level == 0:
                assert mod.split(".")[0] in ("__future__",) or mod.split(".")[0] in sys.stdlib_module_names
            else:
                assert mod.split(".")[0] == "core", (path.name, mod)
        assert "rigorous" not in path.read_text(encoding="utf-8")


def test_the_explanatory_contract_is_pinned_by_the_policy():
    data = CONTRACT.read_bytes().replace(b"\r\n", b"\n")
    assert hashlib.sha256(data).hexdigest() == ANALYTIC_DEPENDENCY["contract_sha256_lf"]
    assert IDEAL_POLICY["analytic_dependencies"] == ANALYTIC_DEPENDENCY
    text = data.decode("utf-8")
    for pin in ("bb32b132469d0dfe5098f9d0d76ddde5113cc49d", "e60cb7f1bdcb4589084e7716adc0ca7dd727b012"):
        assert pin in text and pin in ANALYTIC_DEPENDENCY["sources"].values()
    for phrase in ("not machine-checked", "not Lean results", "τ_δ(y) = y − (δ‖G_k‖, 0)", "chain position",
                   "more-trimmed", "less-trimmed", "continuous motion"):
        assert phrase in text or phrase.upper() in text or phrase.capitalize() in text, phrase


def test_the_checker_revision_covers_every_file_that_affects_arithmetic_or_claims():
    assert IDEAL_CHECKER_REVISION == source_revision(GLAB, "ideal_check/checker.py", "ideal_check/geometry.py",
                                                     "rigorous/ratint.py")
