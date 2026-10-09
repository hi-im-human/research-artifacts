"""Tiny integer domain used only by tests: the core stays domain-free."""
from glab.core.numbers import format_exact, parse_exact
from glab.core.registry import ActionSpec, CheckerSpec, Claim, Param, Registry, StateDraft

REV = "test-local-toy-v1"


def _source(state, params, seed):
    return StateDraft("toy.int", {"value": format_exact(parse_exact(params["value"]))}, "exact")


def _add(state, params, seed):
    value = parse_exact(state["payload"]["value"]) + params["k"]
    return StateDraft("toy.int", {"value": format_exact(value)}, "exact")


def _halve_float(state, params, seed):
    return StateDraft("toy.float", {"value": float(parse_exact(state["payload"]["value"])) / 2}, "approximate")


def _divide(state, params, seed):
    return StateDraft("toy.int", {"value": format_exact(parse_exact(state["payload"]["value"]) / params["d"])},
                      "exact")


def _explode(state, params, seed):
    raise RuntimeError("deliberate construction failure")


def _bad_draft(state, params, seed):
    return StateDraft("toy.int", {"value": 0.5}, "exact")  # float in an exact state


def _mutate_input(state, params, seed):
    state["payload"]["value"] = "666"  # must not reach the stored parent
    return StateDraft("toy.int", {"value": "1"}, "exact")


def _is_even(state, params):
    v = parse_exact(state["payload"]["value"])
    ok = v.denominator == 1 and v.numerator % 2 == 0
    return [Claim("toy.even", "pass" if ok else "fail", "exact_computation", "exact_rational",
                  receipt={"value": state["payload"]["value"]})]


def _nonnegative(state, params):
    v = parse_exact(state["payload"]["value"])
    return [Claim("toy.nonnegative", "pass" if v >= 0 else "fail", "exact_computation", "exact_rational")]


def _float_near_int(state, params):
    """A tolerance check on an approximate state: near an integer boundary it must say unknown."""
    x, tol = state["payload"]["value"], params["tol"]
    frac = abs(x - round(x))
    outcome = "pass" if frac > float(parse_exact(tol)) else "unknown"
    return [Claim("toy.not_integer", outcome, "numerical_diagnostic", "float64",
                  tolerances={"abs": tol}, receipt={"distance_to_integer": frac})]


def _prime_guess(state, params):
    v = parse_exact(state["payload"]["value"])
    if v.denominator != 1 or v.numerator > 1000:
        return [Claim("toy.prime", "unknown", "numerical_diagnostic", "exact_rational",
                      receipt={"reason": "outside the toy checker's decidable range"})]
    n = v.numerator
    prime = n > 1 and all(n % p for p in range(2, int(n ** 0.5) + 1))
    return [Claim("toy.prime", "pass" if prime else "fail", "exact_computation", "exact_rational")]


def registry() -> Registry:
    r = Registry()
    r.register_action(ActionSpec("toy.int.source", 1, None, {"value": Param.exact()}, REV, _source))
    r.register_action(ActionSpec("toy.int.add", 1, "toy.int", {"k": Param.int()}, REV, _add))
    r.register_action(ActionSpec("toy.int.halve_float", 1, "toy.int", {}, REV, _halve_float))
    r.register_action(ActionSpec("toy.int.divide", 1, "toy.int", {"d": Param.int()}, REV, _divide))
    r.register_action(ActionSpec("toy.int.explode", 1, "toy.int", {}, REV, _explode))
    r.register_action(ActionSpec("toy.int.bad_draft", 1, "toy.int", {}, REV, _bad_draft))
    r.register_action(ActionSpec("toy.int.mutate_input", 1, "toy.int", {}, REV, _mutate_input))
    r.register_checker(CheckerSpec("toy.check.even", 1, "toy.int", {}, REV, _is_even))
    r.register_checker(CheckerSpec("toy.check.nonnegative", 1, "toy.int", {}, REV, _nonnegative))
    r.register_checker(CheckerSpec("toy.check.not_integer", 1, "toy.float", {"tol": Param.exact()}, REV,
                                   _float_near_int))
    r.register_checker(CheckerSpec("toy.check.prime", 1, "toy.int", {}, REV, _prime_guess))
    return r
