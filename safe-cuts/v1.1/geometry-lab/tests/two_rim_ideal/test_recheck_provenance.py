"""Stage 4B: the test-side re-checker copy keeps the accepted verification core unchanged (AST comparison only;
runs without mpmath, so it is part of the maintained suite)."""
import ast
import sys
from pathlib import Path

ENGINE = Path(__file__).resolve().parents[2]
ACCEPTED = ENGINE / "probes" / "stage4a" / "recheck_mpmath.py"           # blob cb483479, unchanged
COPY = ENGINE / "tests" / "two_rim_ideal_recheck" / "recheck_ideal_mpmath.py"

UNCHANGED = ["canonical_json", "chash", "exact_str", "I", "endpoints", "sub3", "dot3", "cross3", "ivmul", "ivsub",
             "Data", "theorem_s", "own_enclosure", "parse_box", "axis_ok", "witness_ok", "_local_geometry",
             "PREC", "ORIENTATION", "NORMALIZATION", "ORDERS", "CANON", "COUNTERS", "CERT_KEYS", "SHARED_KEYS"]
ADAPTED = {"_binding", "_shape", "check_seam", "main", "BUNDLE_SCHEMA", "DEFINITION", "ROW_KEYS",
           "DIAGNOSTIC_FIELDS", "SCOPE"}
NEW = {"_evidence", "_declared", "IDEAL_SCHEMA", "IDEAL_KEYS", "CHAIN_KINDS", "CHECKER", "EVIDENCE_SCHEMA", "CLAIMS",
       "SIDES", "THEOREM_S", "REMAINING", "METHODS"}
REMOVED = {"SPEC_KEYS", "STATE_KINDS"}


def _defs(path):
    out = {}
    for node in ast.parse(path.read_text(encoding="utf-8")).body:
        if isinstance(node, (ast.FunctionDef, ast.ClassDef)):
            out[node.name] = ast.dump(node)
        elif isinstance(node, ast.Assign):
            names = [t.id for t in node.targets if isinstance(t, ast.Name)] or \
                [e.id for t in node.targets if isinstance(t, ast.Tuple) for e in t.elts]
            for name in names:
                out[name] = ast.dump(node)
    return out


def test_the_verification_core_is_the_accepted_code():
    accepted, copy = _defs(ACCEPTED), _defs(COPY)
    for name in UNCHANGED:
        assert copy[name] == accepted[name], name
    for name in ADAPTED:
        assert copy[name] != accepted[name], name
    assert set(copy) == set(accepted) - REMOVED | NEW
    assert set(accepted) == set(UNCHANGED) | ADAPTED | REMOVED


def test_the_copy_names_its_source_and_imports_only_stdlib_and_mpmath():
    text = COPY.read_text(encoding="utf-8")
    assert "cb483479" in text and "adapted ONLY in its binding layer" in text
    for node in ast.walk(ast.parse(text)):
        mods = [a.name for a in node.names] if isinstance(node, ast.Import) else \
            [node.module] if isinstance(node, ast.ImportFrom) else []
        for mod in mods:
            top = mod.split(".")[0]
            assert top in ("__future__", "mpmath") or top in sys.stdlib_module_names, mod
