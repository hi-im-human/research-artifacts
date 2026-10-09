"""Independent checker two_rim.check.ideal_trimmed_development v1: claims about the ideal trimmed development D.

Package glab.ideal_check, outside glab/check: the inherited boundary tests keep every glab/check module to the
standard library and glab.core, and this checker also uses the shared arithmetic glab.rigorous. Contextual: the
parent cut and the grandparent material are read through the core's read-only DependencyContext, and D is
reconstructed from those ACTUAL ancestors (never from the carried copy, never from a float state, never from
generator code: this package does not import the generator package two_rim). Standard library only.

Claims (IDEAL_CLAIMS; the contract is TWO-RIM-IDEAL-SCHEMA.md, the mathematics IDEAL-DEVELOPMENT-CONTRACT.md):
  1 record_schema                      exact   the declared key set and the supported literals, canonical delta
  2 cut_copy_matches_parent            exact   carried cut == parent cut; that cut's material == its parent material
  3 delta_in_supported_domain          exact   0 < delta < 1/2
  4 local_premises                     exact   the exact premises the construction and certificates use
  5 retained_hinge_sides_opposite      exact   S1-S4 and the side values sigma on every retained hinge
  6 retained_neighbours_interiors_disjoint     Theorem S applied to 4 and 5; names the pinned analytic dependency;
                                               never fail
  7 remaining_pairs_interiors_disjoint rigorous_enclosure on every other pair: certified axis -> pass, certified
                                               interior witness -> fail, otherwise unknown
  8 pair_coverage_complete             exact   6 and 7 partition the unordered chain pairs
Claims 6 and 7 declare IDEAL_POLICY (instance-independent) in Claim.tolerances; the others declare none.
Unsupported input is never an overlap: after a schema fault nothing is interpreted, and after a domain or premise
failure every later claim is unknown. Every reported quantitative bound is re-verified exactly before it is
recorded (verify_certificate); a row that fails that self-check is recorded as unknown.
"""
from __future__ import annotations

import copy
from fractions import Fraction
from itertools import combinations
from pathlib import Path

from ..core.numbers import ExactInputError, format_exact, parse_exact
from ..core.registry import CheckerSpec, Claim, source_revision
from ..core.runfile import ContextError
from .geometry import (SCHEDULE, _Enclosures, _face_ok, classify_pair, face_checks, local_premises,
                             model_from_payloads, shared_hinge_decision, to_json, verify_certificate)

__all__ = ["register_ideal_checkers", "check_ideal", "ideal_claims", "enclosure_policy", "IDEAL_CLAIMS",
           "IDEAL_POLICY", "ANALYTIC_DEPENDENCY", "SUPPORTED", "CHECKED_FIELDS", "DIAGNOSTIC_FIELDS",
           "IDEAL_CHECKER_REVISION"]

_GLAB = Path(__file__).resolve().parents[1]
# Every file that affects the arithmetic or the meaning of a claim.
IDEAL_CHECKER_REVISION = source_revision(_GLAB, "ideal_check/checker.py", "ideal_check/geometry.py",
                                         "rigorous/ratint.py")

IDEAL_CLAIMS = ("two_rim.ideal.record_schema", "two_rim.ideal.cut_copy_matches_parent",
                "two_rim.ideal.delta_in_supported_domain", "two_rim.ideal.local_premises",
                "two_rim.ideal.retained_hinge_sides_opposite", "two_rim.ideal.retained_neighbours_interiors_disjoint",
                "two_rim.ideal.remaining_pairs_interiors_disjoint", "two_rim.ideal.pair_coverage_complete")
(_SCHEMA, _COPY, _DOMAIN, _PREMISES, _SIDES, _THEOREM_S, _REMAINING, _COVERAGE) = IDEAL_CLAIMS
_POLICY_CLAIMS = (_THEOREM_S, _REMAINING)
_COVERAGE_TOKENS = {_SIDES: "retained_hinge_pairs", _THEOREM_S: "retained_hinge_pairs",
                    _REMAINING: "pairs_not_decided_by_theorem_s"}

# The only record conventions this checker interprets (its own literals; never imported from the generator).
SUPPORTED = {"schema": "two_rim.ideal_trim/1", "definition": "two_rim.ideal_development/1",
             "orientation": "outward: each face map preserves orientation with respect to that face's outward normal",
             "normalization": "N0: first chain face's entry-hinge low trim point at (0, 0); that hinge along +x"}
_IDEAL_KEYS = {"schema", "definition", "delta", "orientation", "normalization", "cut"}

# Edition 1.1 export: the contract SHA-256 and source blobs below pin this export's sanitized copies of the
# analytic documents; the historical originals and their pins are retained privately.
ANALYTIC_DEPENDENCY = {
    "contract": "engine/IDEAL-DEVELOPMENT-CONTRACT.md",
    "contract_sha256_lf": "714efae50c2309ae89d1aeb0fd34958dc9857f1317bf53d45af564bc815dda61",
    "lemmas": ["L1 orientation and side transfer", "L2 existence and uniqueness of the oriented plane isometry",
               "Theorem S: retained neighbours lie in opposite closed half-planes of their shared hinge line",
               "separating-axis lemma", "interior-witness lemma"],
    "sources": {"engine/STAGE-4A-DESIGN.md": "bb32b132469d0dfe5098f9d0d76ddde5113cc49d",
                "engine/probes/stage4a/L4-CORRESPONDENCE.md": "e60cb7f1bdcb4589084e7716adc0ca7dd727b012"},
    "status": "reviewed written derivations (System, an AI reviewer); not machine-checked; not Lean results; "
              "not human peer review",
}


def enclosure_policy(schedule=SCHEDULE) -> dict:
    """The instance-independent evidence policy for claims 6 and 7 (the registered checker uses SCHEDULE)."""
    return {
        "policy": "two_rim.ideal.evidence/1",
        "subject": "the ideal trimmed development D of one two_rim.ideal_trimmed_development state (definition "
                   "two_rim.ideal_development/1); never a float state",
        "arithmetic": "exact rational interval endpoints (Python int and fractions.Fraction); + - * exact; the "
                      "reciprocal of an interval containing 0 is refused (zero_denominator)",
        "root_rule": "sqrt(a) for exact a = N/D >= 0: r = isqrt(N*D*4^P), lo = r/(D*2^P), hi = lo when r^2 = N*D*4^P "
                     "else (r+1)/(D*2^P); lo^2 <= a <= hi^2 re-checked exactly",
        "rounding": "absolute outward rounding to multiples of 2^-P of every intermediate interval that has width; "
                    "zero-width values are kept exact",
        "precision_schedule": list(schedule),
        "budget": "per pair, stop at the first decision; after the last precision the pair is unknown "
                  "(budget_exhausted); an arithmetic refusal is recorded and the next precision is tried (unknown "
                  "with error:<kind> when none decides)",
        "decision_rules": {
            "pass": "a certified separating axis: max sup(d.P) <= min inf(d.Q), or symmetrically, on the enclosing "
                    "boxes; boundary contact allowed",
            "fail": "a certified interior witness: both trimmed rings exactly strictly convex and counterclockwise "
                    "about their normals, and every cross2(v_{i+1} - v_i, y - v_i) with a positive lower bound",
            "otherwise": "unknown; never converted into pass or fail"},
        "reported_bounds": "axis_gap recomputed on the recorded boxes; euclidean_gap_lower_bound b with b >= 0 and "
                           "b^2 (d.d) <= axis_gap^2; cross_lower_bound b with 0 < b <= the recomputed smallest lower "
                           "bound; all exact, before recording",
        "trusted_base": "CPython int, fractions.Fraction, math.isqrt and glab.rigorous.ratint, with the written "
                        "lemmas named in analytic_dependencies",
        "analytic_dependencies": copy.deepcopy(ANALYTIC_DEPENDENCY),
    }


IDEAL_POLICY = enclosure_policy()

# Row fields of claim 7: checked at issuance (and by the separate re-check), versus recorded diagnostics.
CHECKED_FIELDS = ["pair", "positions", "method", "outcome", "bits", "certificate.method", "certificate.axis",
                  "certificate.order", "certificate.axis_gap", "certificate.euclidean_gap_lower_bound",
                  "certificate.witness", "certificate.cross_lower_bound"]
DIAGNOSTIC_FIELDS = ["attempts", "reason", "shared_hinge (on a retained pair routed to intervals)",
                     "self_check_rejected"]


# ------------------------------------------------------------------ claim helpers

def _make(predicate, outcome, receipt, policy):
    method = "rigorous_enclosure" if predicate == _REMAINING else "exact_computation"
    domain = "rational_interval" if predicate == _REMAINING else "exact_rational"
    return Claim(predicate, outcome, method, domain, coverage=_COVERAGE_TOKENS.get(predicate, "all"),
                 tolerances=copy.deepcopy(policy) if predicate in _POLICY_CLAIMS else None, receipt=receipt)


def _pass(ok):
    return "pass" if ok else "fail"


def _rest(claims, reason, policy):
    return claims + [_make(c, "unknown", {"not_interpreted": reason}, policy) for c in IDEAL_CLAIMS[len(claims):]]


def _guard(fn):
    try:
        return fn()
    except ContextError:
        raise
    except (KeyError, IndexError, TypeError, ValueError, ZeroDivisionError, ExactInputError) as exc:
        return False, {"malformed": f"{type(exc).__name__}: {exc}"}


def _canonical_exact(s):
    if not isinstance(s, str):
        return False
    try:
        return format_exact(parse_exact(s)) == s
    except ExactInputError:
        return False


def _schema(p):
    if not isinstance(p, dict) or set(p) != _IDEAL_KEYS:
        return False, {"supported": SUPPORTED, "problems": [f"ideal keys must be {sorted(_IDEAL_KEYS)}"]}
    problems = [f"unsupported {key} {p[key]!r}" for key, value in SUPPORTED.items() if p[key] != value]
    if not _canonical_exact(p["delta"]):
        problems.append("delta must be a canonical exact string")
    if not isinstance(p["cut"], dict):
        problems.append("cut must be an object")
    return not problems, {"supported": SUPPORTED, "problems": problems}


def _ancestors(context):
    """[cut payload, material payload] from the actual parent chain, or None."""
    out, state = [], context.get(context.subject)
    for kind in ("two_rim.cut", "two_rim.material"):
        if state["parent"] is None:
            return None
        state = context.get(state["parent"])
        if state["kind"] != kind:
            return None
        out.append(state["payload"])
    return out


def _premises(material, cut, delta):
    try:
        return local_premises(material, cut, delta)
    except (KeyError, IndexError, TypeError, ValueError, ZeroDivisionError, ExactInputError) as exc:
        return {"ok": False, "problems": [{"code": "malformed", "detail": f"{type(exc).__name__}: {exc}"}],
                "chain": None, "faces": {}}


def _self_check(rows, encl, checks):
    """Re-verify every certificate on the boxes it used; a failing row becomes unknown (never pass or fail)."""
    out, failed, checked = [], [], 0
    for r in rows:
        if r.get("method") in ("separating_axis", "interior_witness"):
            checked += 1
            a, b = r["pair"]
            status, enc = encl.get(r["bits"])
            oriented = _face_ok(checks[a]) and _face_ok(checks[b])
            ok, why = verify_certificate(r, enc["boxes"][a], enc["boxes"][b], oriented) if status == "ok" \
                else (False, "no enclosure at the recorded precision")
            if not ok:
                failed.append({"pair": list(r["pair"]), "reason": why})
                kept = {k: r[k] for k in ("pair", "positions", "shared_hinge", "attempts") if k in r}
                r = dict(kept, outcome="unknown", reason=f"certificate_self_check_failed: {why}",
                         self_check_rejected=r["certificate"])
        out.append(r)
    return out, {"checked_rows": checked, "failed": failed}


# ------------------------------------------------------------------ the checker

def ideal_claims(state, context, schedule=SCHEDULE) -> list:
    """All eight claims for one ideal state. The registered checker uses the policy schedule SCHEDULE; another
    schedule declares a different policy (tests use it to exercise honest unknowns)."""
    policy = enclosure_policy(schedule)
    p = state["payload"]
    ok, rec = _guard(lambda: _schema(p))
    claims = [_make(_SCHEMA, _pass(ok), rec, policy)]
    if not ok:
        return _rest(claims, "ideal record schema invalid; nothing is interpreted", policy)
    delta = parse_exact(p["delta"])
    in_domain = Fraction(0) < delta < Fraction(1, 2)
    domain = _make(_DOMAIN, _pass(in_domain), {"delta": p["delta"], "supported_domain": "0 < delta < 1/2"}, policy)
    anc = _ancestors(context)
    if anc is None:
        claims.append(_make(_COPY, "fail", {"problems": ["ancestors must be two_rim.cut then two_rim.material"],
                                            "cut_copy_matches_parent_cut": None,
                                            "cut_material_copy_matches_material": None}, policy))
        return _rest(claims + [domain], "no exact cut and material ancestors to reconstruct D from", policy)
    cut, material = anc
    copy_ok, material_ok = p["cut"] == cut, isinstance(cut, dict) and cut.get("material") == material
    claims.append(_make(_COPY, _pass(copy_ok and material_ok),
                        {"cut_copy_matches_parent_cut": copy_ok, "cut_material_copy_matches_material": material_ok,
                         "seam": cut.get("seam") if isinstance(cut, dict) else None,
                         "problems": [m for m, bad in (("the carried cut differs from the parent cut", not copy_ok),
                                                       ("the parent cut's material copy differs from its parent "
                                                        "material", not material_ok)) if bad]}, policy))
    claims.append(domain)
    if not in_domain:
        return _rest(claims, "unsupported input: delta outside the supported domain 0 < delta < 1/2; no D is "
                             "defined", policy)
    pre = _premises(material, cut, delta)
    claims.append(_make(_PREMISES, _pass(pre["ok"]),
                        {"problems": pre["problems"], "codes": sorted({x["code"] for x in pre["problems"]}),
                         "chain": pre["chain"], "faces": pre["faces"]}, policy))
    if not pre["ok"]:
        return _rest(claims, "unsupported input: local premises failed (see two_rim.ideal.local_premises); no "
                             "decision is made about D", policy)
    model = model_from_payloads(material, cut, p["delta"])
    checks = face_checks(model)
    chain = list(model.chain)
    side_rows = [shared_hinge_decision(model, a, b, model.faces[a]["exit"]) for a, b in zip(chain, chain[1:])]
    sides_ok = all(r["outcome"] == "pass" for r in side_rows)
    claims.append(_make(_SIDES, _pass(sides_ok), {"rows": to_json(side_rows), "pairs": len(side_rows),
                                                  "passed": sum(r["outcome"] == "pass" for r in side_rows)}, policy))
    decided = [list(r["pair"]) for r in side_rows if r["outcome"] == "pass"]
    claims.append(_make(_THEOREM_S, "pass" if sides_ok else "unknown", {
        "inference": "Theorem S (IDEAL-DEVELOPMENT-CONTRACT.md section 4): the images of two retained neighbours lie "
                     "in opposite closed half-planes of their one shared hinge line, so their interiors are disjoint",
        "premise_claims": [_PREMISES, _SIDES], "analytic_dependency": copy.deepcopy(ANALYTIC_DEPENDENCY),
        "decided_pairs": decided,
        "undecided_pairs": [list(r["pair"]) for r in side_rows if r["outcome"] != "pass"],
        "note": "never fail: a retained pair whose premises do not hold is decided, if at all, by the enclosures"},
        policy))
    done = {tuple(x) for x in decided}
    encl = _Enclosures(model)
    rows = [classify_pair(model, a, b, schedule, encl, checks) for a, b in combinations(chain, 2) if (a, b) not in done]
    rows, self_check = _self_check(rows, encl, checks)
    used = sorted({r["bits"] for r in rows if "bits" in r})
    outs = {r["outcome"] for r in rows}
    claims.append(_make(_REMAINING, "fail" if "fail" in outs else ("pass" if outs <= {"pass"} else "unknown"), {
        "rows": to_json(rows), "pairs": len(rows),
        "counts": {"separating_axis": sum(r.get("method") == "separating_axis" for r in rows),
                   "interior_witness": sum(r.get("method") == "interior_witness" for r in rows),
                   "unknown": sum(r["outcome"] == "unknown" for r in rows)},
        "enclosures": {str(b): {"boxes": to_json(encl.get(b)[1]["boxes"]), "sqrt_records": encl.get(b)[1]["sqrt_records"]}
                       for b in used},
        "attempted_precisions": sorted(encl.cache),
        "enclosure_errors": {str(b): v for b, (s, v) in sorted(encl.cache.items()) if s == "error"},
        "max_bits_needed": used[-1] if used else None, "self_check": self_check,
        "checked_fields": CHECKED_FIELDS, "diagnostic_fields": DIAGNOSTIC_FIELDS,
        "boxes_note": "the checker's own outward enclosures of D at every precision used by a decision; containment "
                      "follows from the policy's arithmetic and is confirmed independently only by a separate "
                      "re-check"}, policy))
    expected = list(combinations(chain, 2))
    covered = [tuple(x) for x in decided] + [tuple(r["pair"]) for r in rows]
    duplicated = sorted({x for x in covered if covered.count(x) > 1})
    missing = [x for x in expected if x not in covered]
    claims.append(_make(_COVERAGE, _pass(not missing and not duplicated and len(covered) == len(expected)), {
        "expected_pairs": len(expected), "theorem_s_pairs": len(decided), "enclosure_pairs": len(rows),
        "missing": [list(x) for x in missing], "duplicated": [list(x) for x in duplicated]}, policy))
    return claims


def check_ideal(state, params, context):
    return ideal_claims(state, context)


def register_ideal_checkers(registry) -> None:
    """two_rim.check.ideal_trimmed_development v1 (contextual; accepts only two_rim.ideal_trimmed_development)."""
    registry.register_checker(CheckerSpec("two_rim.check.ideal_trimmed_development", 1,
                                          "two_rim.ideal_trimmed_development", {}, IDEAL_CHECKER_REVISION,
                                          check_ideal, uses_context=True))
