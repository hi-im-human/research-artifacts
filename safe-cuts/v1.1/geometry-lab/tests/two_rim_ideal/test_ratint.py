"""Stage 4B step 1: the maintained rational intervals (glab.rigorous.ratint).

Controls C1-C3 of the Stage 4A prototype (probes/stage4a/tests/controls/test_c1_c3_arithmetic.py, blob 349a31f7),
run against the maintained module, plus provenance and import-boundary checks.
"""
import ast
import sys
from fractions import Fraction as F
from pathlib import Path

import pytest

from glab.rigorous.ratint import Interval, IntervalError, rsqrt, sqrt_enclosure

ENGINE = Path(__file__).resolve().parents[2]
MAINTAINED = ENGINE / "glab" / "rigorous" / "ratint.py"
PROTOTYPE = ENGINE / "probes" / "stage4a" / "ratint.py"     # blob b4f5c150, kept unchanged


# ---------------------------------------------------------------- C1 endpoint and sign cases

@pytest.mark.parametrize("lo, hi, sign", [
    (0, 0, "zero"),
    (0, 1, "undecided"),              # nonnegative is not positive
    (-1, 0, "undecided"),
    (-1, 1, "undecided"),
    (F(1, 10**30), 1, "positive"),
    (-2, F(-1, 10**30), "negative"),
    (5, 5, "positive"),
])
def test_four_way_sign(lo, hi, sign):
    assert Interval(lo, hi).sign() == sign


def test_products_with_mixed_signs():
    assert (Interval(-2, -1) * Interval(3, 4)).as_tuple() == (F(-8), F(-3))
    assert (Interval(-1, 2) * Interval(3, 4)).as_tuple() == (F(-4), F(8))
    assert (Interval(-1, 2) * Interval(-3, 4)).as_tuple() == (F(-6), F(8))
    assert (Interval(-1, 2) * Interval(3, 4)).sign() == "undecided"


def test_dependency_is_not_hidden_as_exact_zero():
    x = Interval(1, 2)
    assert (x - x).as_tuple() == (F(-1), F(1)) and (x - x).sign() == "undecided"
    y = Interval.exact(F(7, 3))
    assert (y - y).sign() == "zero"


def test_outward_rounding_only_widens_to_dyadics():
    third = Interval.exact(F(1, 3))
    r = third.rounded(8)
    assert r.lo <= F(1, 3) <= r.hi and r.lo < r.hi
    assert (r.lo * 256).denominator == 1 and (r.hi * 256).denominator == 1
    assert Interval.exact(F(3, 4)).rounded(8).as_tuple() == (F(3, 4), F(3, 4))  # already dyadic: unchanged
    assert Interval(F(-1, 3), F(1, 3)).rounded(0).as_tuple() == (F(-1), F(1))
    assert Interval.exact(F(1, 3)).rounded(None).as_tuple() == (F(1, 3), F(1, 3))  # None keeps exact endpoints


def test_floats_and_empty_intervals_are_refused():
    with pytest.raises(TypeError):
        Interval(0.5, 1)
    with pytest.raises(TypeError):
        Interval.exact(True)
    with pytest.raises(TypeError):
        Interval.exact("1/2")
    with pytest.raises(ValueError):
        Interval(2, 1)


def test_containment_helpers_and_json():
    a, b = Interval(1, 3), Interval(0, 4)
    assert a.within(b) and not b.within(a)
    assert a.contains(2) and not a.contains(F(7, 2))
    assert Interval(F(-1, 3), F(2)).to_json() == ["-1/3", "2"]


# ---------------------------------------------------------------- C2 zero denominators

@pytest.mark.parametrize("den", [Interval(-1, 1), Interval(0, 0), Interval(0, 1), Interval(-1, 0)])
def test_zero_containing_denominator_is_an_error_record(den):
    with pytest.raises(IntervalError) as exc:
        Interval(1, 2) / den
    assert exc.value.kind == "zero_denominator"


def test_division_away_from_zero_is_exact():
    assert (Interval(1, 2) / Interval(4, 8)).as_tuple() == (F(1, 8), F(1, 2))
    assert (Interval(1, 2) / Interval(-8, -4)).as_tuple() == (F(-1, 2), F(-1, 8))


# ---------------------------------------------------------------- C3 square-root bounds

RADICANDS = [F(0), F(1), F(4), F(9, 16), F(2), F(1, 3), F(10**40 + 1), F(1, 10**40), F(1693, 100),
             F(2**61 - 1, 3**40)]


@pytest.mark.parametrize("a", RADICANDS)
@pytest.mark.parametrize("bits", [0, 1, 8, 64, 200])
def test_square_root_enclosure_is_checked_exactly(a, bits):
    iv, rec = sqrt_enclosure(a, bits)
    assert iv.lo >= 0 and iv.lo * iv.lo <= a <= iv.hi * iv.hi
    assert rec["checked"] is True and F(rec["lo"]) == iv.lo and F(rec["hi"]) == iv.hi


@pytest.mark.parametrize("a, root", [(F(0), F(0)), (F(1), F(1)), (F(4), F(2)), (F(9, 16), F(3, 4)),
                                     (F(1, 9), F(1, 3)), (F(49, 25), F(7, 5))])
def test_perfect_squares_are_exact_including_non_dyadic(a, root):
    iv, rec = sqrt_enclosure(a, 16)
    assert iv.as_tuple() == (root, root) and rec["exact"] is True


def test_square_root_narrows_monotonically_with_precision():
    widths = [sqrt_enclosure(F(2), bits)[0].width() for bits in (8, 16, 32, 64)]
    assert all(w2 < w1 for w1, w2 in zip(widths, widths[1:]))


def test_negative_radicand_is_an_error_record():
    with pytest.raises(IntervalError) as exc:
        sqrt_enclosure(F(-1, 7), 32)
    assert exc.value.kind == "negative_radicand"


def test_reciprocal_square_root_of_zero_is_an_error_record():
    with pytest.raises(IntervalError) as exc:
        rsqrt(F(0), 64)
    assert exc.value.kind == "zero_denominator"


def test_reciprocal_square_root_is_relative_to_the_radicand_denominator():
    iv, _ = rsqrt(F(2, 10**40), 8)
    assert iv.lo > 0 and iv.lo * iv.lo * F(2, 10**40) <= 1 <= iv.hi * iv.hi * F(2, 10**40)


def test_insufficient_absolute_precision_surfaces_as_a_zero_denominator():
    tiny = Interval.exact(F(1, 10**40)).rounded(8)  # outward rounding to 2^-8 now straddles 0
    assert tiny.contains(0)
    with pytest.raises(IntervalError) as exc:
        Interval.exact(1) / tiny
    assert exc.value.kind == "zero_denominator"
    ok = Interval.exact(F(1, 10**40)).rounded(200)
    assert (Interval.exact(1) / ok).sign() == "positive"


def test_square_root_rejects_non_exact_inputs():
    with pytest.raises(TypeError):
        sqrt_enclosure(2.0, 32)


# ---------------------------------------------------------------- provenance and boundaries

def _code_without_docstring(path):
    body = ast.parse(path.read_text(encoding="utf-8")).body
    if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) \
            and isinstance(body[0].value.value, str):
        body = body[1:]
    return ast.dump(ast.Module(body=body, type_ignores=[]))


def test_maintained_code_is_the_accepted_prototype_code():
    """Only the module docstring differs from probes/stage4a/ratint.py (blob b4f5c150)."""
    assert _code_without_docstring(MAINTAINED) == _code_without_docstring(PROTOTYPE)
    assert "PROTOTYPE" not in ast.get_docstring(ast.parse(MAINTAINED.read_text(encoding="utf-8")))


def test_rigorous_package_uses_only_the_standard_library():
    files = sorted(MAINTAINED.parent.glob("*.py"))
    assert {f.name for f in files} == {"__init__.py", "ratint.py"}
    for f in files:
        for node in ast.walk(ast.parse(f.read_text(encoding="utf-8"))):
            mods = [a.name for a in node.names] if isinstance(node, ast.Import) else \
                [node.module or ""] if isinstance(node, ast.ImportFrom) and node.level == 0 else []
            for mod in mods:
                top = mod.split(".")[0]
                assert top == "__future__" or top in sys.stdlib_module_names, (f.name, mod)
