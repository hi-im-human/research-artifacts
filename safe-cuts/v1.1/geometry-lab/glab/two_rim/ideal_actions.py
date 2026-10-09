"""Ideal-development lane, generator side: the two_rim.ideal_trim/1 payload and action two_rim.ideal.define v1.

The state names the ideal trimmed development D of IDEAL-DEVELOPMENT-CONTRACT.md for one exact cut and one exact
positive trim. It records an exact copy of the parent cut, the canonical trim depth and the fixed orientation,
normalization and definition identifiers. It carries no coordinates, maps or verdicts: the independent checker
reconstructs everything from the actual ancestor states. `exact` describes the inputs and the definition, not the
(irrational) image coordinates of D. One module, standard library and glab.core only (the inherited boundary tests
fix the sibling modules two_rim modules may import). Registration is explicit and additive.
"""
from __future__ import annotations

import copy
from fractions import Fraction
from pathlib import Path

from ..core.numbers import ExactInputError, format_exact, parse_exact
from ..core.registry import ActionSpec, Param, StateDraft, source_revision

__all__ = ["IdealInputError", "IDEAL_KIND", "IDEAL_SCHEMA", "DEFINITION", "ORIENTATION", "NORMALIZATION",
           "canonical_delta", "define_ideal", "register_ideal_actions", "IDEAL_ACTION_REVISION"]

IDEAL_ACTION_REVISION = source_revision(Path(__file__).resolve().parent, "ideal_actions.py")
IDEAL_KIND = "two_rim.ideal_trimmed_development"
IDEAL_SCHEMA = "two_rim.ideal_trim/1"
DEFINITION = "two_rim.ideal_development/1"   # the Stage 4A definition stage4a.ideal_development/1, unchanged
ORIENTATION = "outward: each face map preserves orientation with respect to that face's outward normal"
NORMALIZATION = "N0: first chain face's entry-hinge low trim point at (0, 0); that hinge along +x"


class IdealInputError(ValueError):
    """Outside the supported positive-trim domain: no ideal subject is defined (never an overlap verdict)."""


def canonical_delta(delta) -> Fraction:
    """delta must be a canonical exact string ('n/d' in lowest terms, or 'n') with 0 < delta < 1/2."""
    if not isinstance(delta, str):
        raise IdealInputError(f"delta must be a canonical exact string, got {type(delta).__name__}")
    try:
        d = parse_exact(delta)
    except ExactInputError as exc:
        raise IdealInputError(f"delta is not an exact rational: {exc}") from None
    if format_exact(d) != delta:
        raise IdealInputError(f"delta {delta!r} is not in canonical form {format_exact(d)!r}")
    if not Fraction(0) < d < Fraction(1, 2):
        raise IdealInputError(f"delta {delta} is outside the supported domain 0 < delta < 1/2")
    return d


def define_ideal(cut: dict, delta) -> dict:
    """two_rim.ideal_trim/1 payload for an exact two_rim.cut/1 payload and a canonical positive trim."""
    if not isinstance(cut, dict) or cut.get("schema") != "two_rim.cut/1":
        raise IdealInputError(f"unsupported cut schema {cut.get('schema') if isinstance(cut, dict) else cut!r}")
    d = canonical_delta(delta)
    return {"schema": IDEAL_SCHEMA, "definition": DEFINITION, "delta": format_exact(d), "orientation": ORIENTATION,
            "normalization": NORMALIZATION, "cut": copy.deepcopy(cut)}


def _define(state, params, seed):
    return StateDraft(IDEAL_KIND, define_ideal(state["payload"], params["delta"]), "exact")


def register_ideal_actions(registry) -> None:
    """two_rim.ideal.define v1: parent two_rim.cut (never a float state), parameter delta (exact, canonical)."""
    registry.register_action(ActionSpec("two_rim.ideal.define", 1, "two_rim.cut", {"delta": Param.exact()},
                                        IDEAL_ACTION_REVISION, _define))
