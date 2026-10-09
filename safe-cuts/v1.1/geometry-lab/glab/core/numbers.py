"""Exact input parsing. Standard library only.

Never place ``glab/core`` itself on ``sys.path``: this module would shadow the
standard library's ``numbers``. Import it as ``glab.core.numbers``.
"""
from __future__ import annotations

import re
from fractions import Fraction

__all__ = ["ExactInputError", "parse_exact", "format_exact"]

_EXACT = re.compile(
    r"[+-]?(?:[0-9]+(?:/[0-9]+)?"             # integer or p/q
    r"|[0-9]+\.[0-9]*(?:[eE][+-]?[0-9]+)?"    # 1.  1.5  1.5e-3
    r"|\.[0-9]+(?:[eE][+-]?[0-9]+)?"          # .5
    r"|[0-9]+[eE][+-]?[0-9]+)"                # 1e-20
)


class ExactInputError(ValueError):
    """A value is not an exact finite number in an accepted spelling."""


def parse_exact(value) -> Fraction:
    """Integers (not bools) or ASCII exact strings; floats are rejected, never converted."""
    if isinstance(value, bool):
        raise ExactInputError("booleans are not numbers")
    if isinstance(value, int):
        return Fraction(value)
    if isinstance(value, float):
        raise ExactInputError(f"float {value!r} rejected: a rounded binary float is not an exact input; "
                              "pass a string such as '1/10'")
    if not isinstance(value, str):
        raise ExactInputError(f"unsupported type {type(value).__name__}")
    text = value.strip()
    if not _EXACT.fullmatch(text):
        raise ExactInputError(f"not an exact finite number: {value!r}")
    if "/" in text and int(text.split("/")[1]) == 0:
        raise ExactInputError(f"zero denominator: {value!r}")
    return Fraction(text)


def format_exact(q: Fraction) -> str:
    """Canonical text: 'n' or 'n/d' in lowest terms."""
    if not isinstance(q, Fraction):
        raise ExactInputError("format_exact expects a Fraction")
    return str(q.numerator) if q.denominator == 1 else f"{q.numerator}/{q.denominator}"
