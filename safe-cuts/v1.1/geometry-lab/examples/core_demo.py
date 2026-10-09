"""Core demo: a tiny integer domain defined HERE, not in glab.core (run format glab.run/2).

Covers: two successful actions, a rejected JSON-typed request (version=True), a failed action,
a single-claim check, a multi-claim check with an unknown, a zero-claim check, a failed checker
attempt, save, an external-anchor comparison (matched, and a forged rewrite rejected), load and replay.

Usage (from engine/):  python examples/core_demo.py OUT_DIR
"""
from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from glab.core.evidence import Requirement, summarize  # noqa: E402
from glab.core.numbers import format_exact, parse_exact  # noqa: E402
from glab.core.registry import (ActionSpec, CheckerSpec, Claim, Param, Registry, StateDraft,  # noqa: E402
                                source_revision)
from glab.core.runfile import Run, RunIntegrityError, load_run, replay  # noqa: E402

DEMO_REV = source_revision(Path(__file__).resolve().parent, Path(__file__).name)


def _source(state, params, seed):
    return StateDraft("demo.int", {"value": format_exact(parse_exact(params["value"]))}, "exact")


def _add(state, params, seed):
    return StateDraft("demo.int", {"value": format_exact(parse_exact(state["payload"]["value"]) + params["k"])},
                      "exact")


def _divide(state, params, seed):
    return StateDraft("demo.int", {"value": format_exact(parse_exact(state["payload"]["value"]) / params["d"])},
                      "exact")


def _even(state, params):
    v = parse_exact(state["payload"]["value"])
    return [Claim("demo.even", "pass" if v.denominator == 1 and v.numerator % 2 == 0 else "fail",
                  "exact_computation", "exact_rational")]


def _profile(state, params):
    """Multi-claim checker: one decided claim and one it cannot decide."""
    v = parse_exact(state["payload"]["value"])
    claims = [Claim("demo.nonnegative", "pass" if v >= 0 else "fail", "exact_computation", "exact_rational")]
    if v.denominator != 1 or v.numerator > 1000:
        claims.append(Claim("demo.prime", "unknown", "numerical_diagnostic", "exact_rational",
                            receipt={"reason": "outside this toy checker's decidable range (<= 1000)"}))
    else:
        n = v.numerator
        ok = n > 1 and all(n % p for p in range(2, int(n ** 0.5) + 1))
        claims.append(Claim("demo.prime", "pass" if ok else "fail", "exact_computation", "exact_rational"))
    return claims


def _notes(state, params):
    """Completes with nothing to report: a zero-claim check."""
    return []


def _fragile(state, params):
    """Crashes on large values: an execution failure of the attempt, not a predicate outcome."""
    if parse_exact(state["payload"]["value"]) > 1000:
        raise OverflowError("demo checker cannot handle values above 1000")
    return [Claim("demo.small", "pass", "exact_computation", "exact_rational")]


def demo_registry() -> Registry:
    r = Registry()
    r.register_action(ActionSpec("demo.int.source", 1, None, {"value": Param.exact()}, DEMO_REV, _source))
    r.register_action(ActionSpec("demo.int.add", 1, "demo.int", {"k": Param.int()}, DEMO_REV, _add))
    r.register_action(ActionSpec("demo.int.divide", 1, "demo.int", {"d": Param.int()}, DEMO_REV, _divide))
    r.register_checker(CheckerSpec("demo.check.even", 1, "demo.int", {}, DEMO_REV, _even))
    r.register_checker(CheckerSpec("demo.check.profile", 1, "demo.int", {}, DEMO_REV, _profile))
    r.register_checker(CheckerSpec("demo.check.notes", 1, "demo.int", {}, DEMO_REV, _notes))
    r.register_checker(CheckerSpec("demo.check.fragile", 1, "demo.int", {}, DEMO_REV, _fragile))
    return r


def build(reg: Registry, value: str) -> Run:
    run = Run(reg)
    a = run.apply("demo.int.source", 1, {"value": value})["output"]
    b = run.apply("demo.int.add", 1, {"k": 2}, a)["output"]
    run.apply("demo.int.add", True, {"k": 2}, b)          # rejected; version stored as JSON true
    run.apply("demo.int.divide", 1, {"d": 0}, b)          # failed action attempt
    run.check("demo.check.even", 1, b, {})                # one claim
    run.check("demo.check.profile", 1, b, {})             # two claims, one unknown
    run.check("demo.check.notes", 1, b, {})               # zero claims, still recorded
    try:
        run.check("demo.check.fragile", 1, b, {})         # failed checker attempt, recorded then raised
    except OverflowError:
        pass
    return run


def sha(p: Path) -> str:
    return "sha256:" + hashlib.sha256(p.read_bytes()).hexdigest()


def write_json(p: Path, obj) -> None:
    p.write_text(json.dumps(obj, indent=1, sort_keys=True) + "\n", encoding="ascii", newline="\n")


def main(out: Path) -> dict:
    out.mkdir(parents=True, exist_ok=True)
    reg = demo_registry()
    run = build(reg, "1200")
    b = run.actions[1]["output"]
    requirements = [Requirement("demo.even", b), Requirement("demo.nonnegative", b), Requirement("demo.prime", b)]
    digest = run.save(out / "demo.run.json")
    (out / "retained-digest.txt").write_text(digest + "\n", encoding="ascii", newline="\n")

    forged = out / "forged-rewrite.run.json"            # a different, internally consistent history
    build(reg, "1300").save(forged)
    try:
        load_run(forged, expected_digest=digest)
        forged_result = "ACCEPTED (unexpected)"
    except RunIntegrityError as exc:
        forged_result = f"rejected: {exc}"
    forged_unanchored = load_run(forged)

    loaded = load_run(out / "demo.run.json", expected_digest=digest)
    as_loaded = summarize(loaded.record["evidence"], requirements, loaded.store, reg)
    report = replay(loaded, reg)
    after = report["run"].summarize(requirements)
    history = loaded.record["history"]
    result = {
        "run_digest": digest,
        "history": [{"seq": h["seq"], "schema": h["schema"], "name": h.get("action", h.get("checker")),
                     "version": h["version"], "status": h["status"],
                     "failure": h["failure"] and {"stage": h["failure"]["stage"], "type": h["failure"]["type"]},
                     "evidence_count": len(h["evidence"]) if "evidence" in h else None} for h in history],
        "evidence": [{"claim": e["claim"], "outcome": e["outcome"], "attempt": e["attempt"]}
                     for e in loaded.record["evidence"]],
        "load": {"integrity": loaded.integrity, "anchor": loaded.anchor, "authenticated": loaded.authenticated},
        "external_anchor": {"forged_rewrite_unanchored_load": forged_unanchored.integrity,
                            "forged_rewrite_against_retained_digest": forged_result},
        "summary_as_loaded": {"outcome": as_loaded["outcome"], "verified": as_loaded["verified"]},
        "replay": {k: v for k, v in report.items() if k != "run"},
        "summary_after_replay": after,
    }
    write_json(out / "demo.report.json", result)
    write_json(out / "MANIFEST.json", {p.name: sha(p) for p in sorted(out.iterdir()) if p.name != "MANIFEST.json"})
    return result


if __name__ == "__main__":
    r = main(Path(sys.argv[1]))
    print("run_digest", r["run_digest"])
    for h in r["history"]:
        print(" ", h["seq"], h["schema"], h["name"], "v" + str(h["version"]), h["status"],
              h["failure"] or "", "" if h["evidence_count"] is None else f"evidence={h['evidence_count']}")
    print("evidence", [(e["claim"], e["outcome"]) for e in r["evidence"]])
    print("load", r["load"])
    print("external anchor", r["external_anchor"])
    print("summary as loaded", r["summary_as_loaded"])
    print("replay", r["replay"]["outcome"], "| digest reproduced:", r["replay"]["run_digest_reproduced"],
          "| partial:", r["replay"]["partial_comparison"])
    print("summary after replay", {k: r["summary_after_replay"][k] for k in ("outcome", "verified")})
