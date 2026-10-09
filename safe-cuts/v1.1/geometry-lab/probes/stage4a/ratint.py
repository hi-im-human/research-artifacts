"""ISOLATED STAGE 4A PROTOTYPE: outward rational intervals and verified square roots (standard library only).

Every operation encloses the exact real operation on the input sets:
  +, -, *        exact endpoint arithmetic on Fractions (no rounding at all);
  1/x, /         exact, refused (IntervalError "zero_denominator") when the denominator contains 0;
  sqrt(a)        a an exact rational N/D >= 0: r = isqrt(N*D*4^P) gives
                 r/(D*2^P) <= sqrt(a) < (r+1)/(D*2^P); the bound lo^2 <= a <= hi^2 is re-checked exactly;
  rounded(P)     optional outward rounding of both endpoints to multiples of 2^-P (only widens).
Precision P never enters a containment argument; it only controls width. Floats are refused.
"""
from __future__ import annotations

from fractions import Fraction
from math import isqrt

__all__ = ["Interval", "IntervalError", "sqrt_enclosure", "rsqrt", "exact"]


class IntervalError(ArithmeticError):
    """A recorded arithmetic refusal (never converted into a pass or fail)."""

    def __init__(self, kind: str, detail: str = ""):
        super().__init__(f"{kind}: {detail}" if detail else kind)
        self.kind = kind
        self.detail = detail


def exact(x) -> Fraction:
    """Exact rational from int or Fraction; floats, bools and strings are refused here."""
    if isinstance(x, bool) or not isinstance(x, (int, Fraction)):
        raise TypeError(f"exact rational (int or Fraction) required, got {type(x).__name__}")
    return Fraction(x)


class Interval:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        lo = exact(lo)
        hi = lo if hi is None else exact(hi)
        if lo > hi:
            raise ValueError(f"empty interval [{lo}, {hi}]")
        self.lo, self.hi = lo, hi

    @classmethod
    def exact(cls, q) -> "Interval":
        return cls(q, q)

    # -- arithmetic (exact endpoints) ------------------------------------------------------
    @staticmethod
    def _coerce(o) -> "Interval":
        return o if isinstance(o, Interval) else Interval.exact(o)

    def __add__(self, o):
        o = self._coerce(o)
        return Interval(self.lo + o.lo, self.hi + o.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, o):
        o = self._coerce(o)
        return Interval(self.lo - o.hi, self.hi - o.lo)

    def __rsub__(self, o):
        return self._coerce(o) - self

    def __mul__(self, o):
        o = self._coerce(o)
        p = (self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi)
        return Interval(min(p), max(p))

    __rmul__ = __mul__

    def recip(self) -> "Interval":
        if self.lo <= 0 <= self.hi:
            raise IntervalError("zero_denominator", f"[{self.lo}, {self.hi}] contains 0")
        return Interval(1 / self.hi, 1 / self.lo)

    def __truediv__(self, o):
        return self * self._coerce(o).recip()

    def __rtruediv__(self, o):
        return self._coerce(o) * self.recip()

    # -- queries ---------------------------------------------------------------------------
    def sign(self) -> str:
        """Four-way: positive, negative, zero (exact), or undecided. Undecided is never a sign."""
        if self.lo > 0:
            return "positive"
        if self.hi < 0:
            return "negative"
        if self.lo == self.hi == 0:
            return "zero"
        return "undecided"

    def width(self) -> Fraction:
        return self.hi - self.lo

    def contains(self, q) -> bool:
        q = exact(q)
        return self.lo <= q <= self.hi

    def within(self, other: "Interval") -> bool:
        return other.lo <= self.lo and self.hi <= other.hi

    def mid(self) -> Fraction:
        return (self.lo + self.hi) / 2

    def rounded(self, bits: int | None) -> "Interval":
        """Outward rounding to multiples of 2^-bits (None: keep exact endpoints)."""
        if bits is None:
            return self
        scale = 1 << bits
        lo = Fraction((self.lo.numerator * scale) // self.lo.denominator, scale)
        hi = Fraction(-((-self.hi.numerator * scale) // self.hi.denominator), scale)
        return Interval(lo, hi)

    def as_tuple(self):
        return (self.lo, self.hi)

    def to_json(self):
        return [str(self.lo), str(self.hi)]

    def __repr__(self):
        return f"Interval({self.lo}, {self.hi})"


def sqrt_enclosure(a, bits: int):
    """(Interval, record) enclosing sqrt(a) for an exact rational a >= 0; the record is re-checkable."""
    a = exact(a)
    if a < 0:
        raise IntervalError("negative_radicand", str(a))
    if a == 0:
        return Interval.exact(0), {"radicand": "0", "lo": "0", "hi": "0", "exact": True, "checked": True}
    n, d = a.numerator, a.denominator
    target = n * d << (2 * bits)
    r = isqrt(target)
    lo = Fraction(r, d << bits)
    hi = lo if r * r == target else Fraction(r + 1, d << bits)
    if not (lo >= 0 and lo * lo <= a <= hi * hi):  # exact re-check of the certificate
        raise IntervalError("sqrt_check_failed", str(a))
    return Interval(lo, hi), {"radicand": str(a), "lo": str(lo), "hi": str(hi), "exact": lo == hi,
                              "checked": True}


def rsqrt(a, bits: int):
    """(Interval, record) enclosing 1/sqrt(a); a zero root is refused as a zero denominator."""
    root, rec = sqrt_enclosure(a, bits)
    return root.recip(), rec
