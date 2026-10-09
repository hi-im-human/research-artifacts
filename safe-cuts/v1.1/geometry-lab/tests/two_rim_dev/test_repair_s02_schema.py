"""Stage 3 repair S02: development and trim record schemas enforce their declared meaning."""
import pytest

from glab.check.two_rim_development import DIAGNOSTICS, NUMERICAL, TRIM_EXACT, DEV_EXACT
from glab.core.registry import ActionSpec, StateDraft
from glab.core.runfile import Run
from glab.two_rim.develop import develop_static
from glab.two_rim.trim import apply_trim
from tests.two_rim_dev.helpers import E11, developed, outcomes, registry

SQ = [[0, 0], [0, 2], [2, 2], [2, 0]]
SQUARE = {"top": SQ, "bottom": SQ, "height": "3", "input_kind": "cyclic_boundary"}


def _run_with(mutate_dev=None, mutate_trim=None, params=SQUARE, delta="1/4"):
    reg = registry()
    if mutate_dev:
        def dev(st, p, seed):
            payload = develop_static(st["payload"])
            mutate_dev(payload)
            return StateDraft("two_rim.development", payload, "mixed")
        reg.register_action(ActionSpec("test.develop", 1, "two_rim.cut", {}, "test-1", dev))
    if mutate_trim:
        def trim(st, p, seed):
            payload = apply_trim(st["payload"], delta)
            mutate_trim(payload)
            return StateDraft("two_rim.trimmed_development", payload, "mixed")
        reg.register_action(ActionSpec("test.trim", 1, "two_rim.development", {}, "test-1", trim))
    run = Run(reg)
    d = developed(run, params, seam="E0")
    if mutate_dev:
        d["development"] = run.apply("test.develop", 1, {}, d["cut"])["output"]
    if mutate_trim:
        d["trimmed"] = run.apply("test.trim", 1, {}, d["development"])["output"]
    return run, d


def dev_out(run, h):
    return outcomes(run.check("two_rim.check.development", 2, h, {}))


def trim_out(run, h):
    return outcomes(run.check("two_rim.check.trimmed_development", 2, h, {}))


def _dependents_unknown(out, exact_claims):
    return all(out[c] == "unknown" for c in exact_claims[1:] + NUMERICAL + DIAGNOSTICS)


@pytest.mark.parametrize("mutate", [
    lambda p: p.update(map_convention="image = linear @ [x, y, z] - offset"),
    lambda p: p["generator"].update(sum_q="-6.2"),
    lambda p: p["generator"].update(turns_q=p["generator"]["turns_q"][:-1]),
    lambda p: p["generator"].pop("port_of"),
    lambda p: p["generator"].update(extra=1),
    lambda p: p.update(generator=[]),
    lambda p: p.update(cut="not an object"),
    lambda p: p["maps"][0]["linear"][0].__setitem__(0, True),
], ids=["subtracted_offset", "sum_q_string", "turns_q_length", "generator_missing_key",
        "generator_extra_key", "generator_not_object", "cut_not_object", "bool_in_map"])
def test_unsupported_development_records_are_not_all_green(mutate):
    run, d = _run_with(mutate_dev=mutate)
    out = dev_out(run, d["development"])
    assert out[DEV_EXACT[0]] == "fail"
    assert _dependents_unknown(out, DEV_EXACT)


def test_non_finite_generator_values_never_reach_a_record():
    # NaN/inf are not JSON: the core refuses the action output, so no development state exists to check.
    reg = registry()

    def dev(st, p, seed):
        payload = develop_static(st["payload"])
        payload["generator"]["sum_q"] = float("nan")
        return StateDraft("two_rim.development", payload, "mixed")
    reg.register_action(ActionSpec("test.develop", 1, "two_rim.cut", {}, "test-1", dev))
    run = Run(reg)
    d = developed(run, SQUARE, seam="E0")
    got = run.apply("test.develop", 1, {}, d["cut"])
    assert got["status"] != "succeeded" and got["output"] is None


def _first_point(p):
    return p["trim_points"][sorted(p["trim_points"])[0]]


def _noncanonical(s):
    """Same value, non-canonical spelling (numerator and denominator doubled)."""
    n, _, d = s.partition("/")
    return f"{2 * int(n)}/{2 * int(d or 1)}"


@pytest.mark.parametrize("mutate", [
    lambda p: p.update(height_parameter="absolute z, not normalized height"),
    lambda p: _first_point(p)["xyz"].__setitem__(0, False),
    lambda p: _first_point(p)["xyz"].__setitem__(0, 0.0),
    lambda p: _first_point(p)["xyz"].__setitem__(0, 0),
    lambda p: _first_point(p)["xyz"].pop(),
    lambda p: _first_point(p)["xyz"].append("0"),
    lambda p: _first_point(p).update(extra="x"),
    lambda p: _first_point(p).update(t=0.25),
    lambda p: _first_point(p).update(hinge=0),
    lambda p: p["trim_points"].update({sorted(p["trim_points"])[0]: ["0", "0", "0"]}),
    lambda p: _first_point(p)["xyz"].__setitem__(2, _noncanonical(_first_point(p)["xyz"][2])),
    lambda p: _first_point(p).update(t=_noncanonical(_first_point(p)["t"])),
    lambda p: _first_point(p)["xyz"].__setitem__(0, " " + _first_point(p)["xyz"][0]),
], ids=["height_parameter", "bool_coordinate", "float_coordinate", "int_coordinate", "two_coordinates",
        "four_coordinates", "extra_point_key", "float_t", "int_hinge", "point_not_object", "noncanonical_coordinate",
        "noncanonical_t", "leading_space"])
def test_unsupported_or_malformed_trim_records_fail_the_schema(mutate):
    run, d = _run_with(mutate_trim=mutate)
    out = trim_out(run, d["trimmed"])
    assert out[TRIM_EXACT[0]] == "fail"
    assert _dependents_unknown(out, TRIM_EXACT)


def test_canonical_but_wrong_trim_point_is_a_valid_record_that_fails_the_band():
    run, d = _run_with(mutate_trim=lambda p: _first_point(p)["xyz"].__setitem__(2, "1/7"))
    out = trim_out(run, d["trimmed"])
    assert out[TRIM_EXACT[0]] == "pass" and out[TRIM_EXACT[2]] == "fail"


def test_valid_canonical_records_with_negative_and_fractional_coordinates_pass_the_schemas():
    run = Run(registry())
    d = developed(run, E11, seam="E9", delta="1/10000")
    run2, t = run, d["trimmed"]
    payload = run2.get(t)["payload"]
    spellings = [c for pt in payload["trim_points"].values() for c in pt["xyz"]]
    assert any(c.startswith("-") and "/" in c for c in spellings)
    dev = dev_out(run2, d["development"])
    tr = trim_out(run2, t)
    assert dev[DEV_EXACT[0]] == dev[DEV_EXACT[1]] == "pass"
    assert tr[TRIM_EXACT[0]] == tr[TRIM_EXACT[1]] == tr[TRIM_EXACT[2]] == "pass"
