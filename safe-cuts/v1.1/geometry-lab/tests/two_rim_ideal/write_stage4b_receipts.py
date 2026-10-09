"""Write the Stage 4B result receipts (test-side script; maintained .venv; nothing installed).

Usage, from engine/:  python -B -m tests.two_rim_ideal.write_stage4b_receipts OUT_DIR
Writes the eleven-panel ideal search, its summary, the historical comparison (read only after classification), the
port-equivalence digests against the accepted prototype, the prism cases, a re-check bundle, the saved Run file and
a manifest. Wall-clock timing goes to timing.json, which the manifest excludes; everything else is deterministic.
"""
from __future__ import annotations

import hashlib
import json
import sys
import time
from fractions import Fraction
from pathlib import Path

from glab.core.records import canonical_json
from glab.ideal_check.checker import IDEAL_CHECKER_REVISION, IDEAL_CLAIMS, IDEAL_POLICY
from glab.two_rim.ideal_actions import IDEAL_ACTION_REVISION
from glab.two_rim.ideal_search import AGGREGATE, ideal_candidate_search
from probes.stage4a.classify import classify_seam, to_json
from probes.stage4a.ideal import model_from_payloads
from tests.two_rim_ideal.helpers import E11, E11_DELTA, NEAR_HALF, NEAR_ZERO, NONDYADIC, SQUARE, material, new_run
from tests.two_rim_ideal_recheck.bundle import ideal_bundle

SIDES, THEOREM_S, REMAINING = IDEAL_CLAIMS[4], IDEAL_CLAIMS[5], IDEAL_CLAIMS[6]
LABEL = "Stage 4B maintained ideal lane (glab); verdicts concern the ideal trimmed development D only"


def _write(path: Path, obj):
    path.write_text(json.dumps(obj, indent=1, sort_keys=True, ensure_ascii=True) + "\n", encoding="ascii",
                    newline="\n")


def _sha(obj):
    return "sha256:" + hashlib.sha256(canonical_json(obj).encode("ascii")).hexdigest()


def _claims(run, ideal):
    evs = [e for e in run.evidence if e["subject"] == ideal and e["checker"] == "two_rim.check.ideal_trimmed_development"]
    last = max(e["attempt"] for e in evs)
    return {e["claim"]: e for e in evs if e["attempt"] == last}


def e11_receipts(out: Path, timing: dict):
    run = new_run()
    _, m = material(run, E11)
    t0 = time.perf_counter()
    search = ideal_candidate_search(run, m, E11_DELTA, expected_policy=IDEAL_POLICY)
    timing["e11_search_seconds"] = time.perf_counter() - t0
    _write(out / "e11-ideal-search.json", search)
    summary, equivalence = {}, {}
    for row in search["results"]:
        seam, ideal = row["seam"], row["ideal"]
        claims = _claims(run, ideal)
        rem = claims[REMAINING]["receipt"]
        summary[seam] = {"ideal_state": ideal, AGGREGATE: row[AGGREGATE],
                         "ideal_geometric_verdict": row["ideal_geometric_verdict"]["verdict"],
                         "claims": {c: claims[c]["outcome"] for c in IDEAL_CLAIMS},
                         "theorem_s_pairs": len(claims[THEOREM_S]["receipt"]["decided_pairs"]),
                         "counts": rem["counts"], "max_bits_needed": rem["max_bits_needed"],
                         "attempted_precisions": rem["attempted_precisions"],
                         "witness_pairs": [r["pair"] for r in rem["rows"] if r.get("method") == "interior_witness"]}
        cut = run.get(row["cut"])["payload"]
        proto = to_json(classify_seam(model_from_payloads(run.get(m)["payload"], cut, E11_DELTA)))["rows"]
        mine_s, mine_r = claims[SIDES]["receipt"]["rows"], rem["rows"]
        proto_s = [r["shared_hinge"] for r in proto if r.get("method") == "shared_hinge_exact"]
        proto_r = [r for r in proto if r.get("method") != "shared_hinge_exact"]
        equivalence[seam] = {"theorem_s_rows": {"maintained": _sha(mine_s), "prototype": _sha(proto_s),
                                                "identical": mine_s == proto_s},
                             "enclosure_rows": {"maintained": _sha(mine_r), "prototype": _sha(proto_r),
                                                "identical": mine_r == proto_r}}
    totals = {"pairs": sum(s["theorem_s_pairs"] + sum(s["counts"].values()) for s in summary.values()),
              "theorem_s": sum(s["theorem_s_pairs"] for s in summary.values()),
              "separating_axis": sum(s["counts"]["separating_axis"] for s in summary.values()),
              "interior_witness": sum(s["counts"]["interior_witness"] for s in summary.values()),
              "unknown": sum(s["counts"]["unknown"] for s in summary.values()),
              "max_bits_needed": max(s["max_bits_needed"] for s in summary.values()),
              "verdicts": {v: sorted((k for k, s in summary.items() if s["ideal_geometric_verdict"] == v),
                                     key=lambda k: int(k[1:])) for v in ("pass", "fail", "unknown", "not_determined")}}
    digest = run.save(out / "e11-ideal-run.json")
    _write(out / "e11-ideal-summary.json", {"label": LABEL, "delta": E11_DELTA, "expected_policy": IDEAL_POLICY,
                                            "checker_revision": IDEAL_CHECKER_REVISION,
                                            "action_revision": IDEAL_ACTION_REVISION, "run_digest": digest,
                                            "totals": totals, "seams": summary})
    _write(out / "e11-port-equivalence.json", {
        "label": "maintained claim rows versus the accepted Stage 4A prototype (probes/stage4a, unchanged) on the "
                 "same exact inputs", "all_identical": all(v["theorem_s_rows"]["identical"] and
                                                           v["enclosure_rows"]["identical"] for v in equivalence.values()),
        "seams": equivalence})
    from tests.two_rim_dev.eleven_panel import build_mapping, load_certificate   # reference, read afterwards
    cert = load_certificate()
    mapping = build_mapping(run.get(m)["payload"], cert)
    rows = []
    for k in range(mapping["n"]):
        seam = mapping["cuts"][k]
        historical = "unsafe" if k in cert["unsafe_cuts"] else "safe"
        ours = summary[seam]["ideal_geometric_verdict"]
        rows.append({"historical_cut": k, "seam": seam, "historical_exact_class": historical, "ideal_verdict": ours,
                     "comparison": {("unsafe", "fail"): "agree", ("safe", "pass"): "agree"}.get((historical, ours),
                                                                                               "DISAGREE")})
    _write(out / "e11-historical-comparison.json", {
        "label": "historical classes read only after classification; agreement on this fixture is not a universal "
                 "proof", "mapping_rotation": mapping["rotation_current_minus_historical"], "classes": rows})
    _write(out / "e11-recheck-bundle.json", ideal_bundle(run, {r["seam"]: r["ideal"] for r in search["results"]}))
    return totals


def prism_receipts(out: Path):
    cases = {}
    for name, params, deltas in (("square", SQUARE, ["1/4", "1/3", "1/7", "1/10000", NEAR_ZERO, NEAR_HALF]),
                                 ("nondyadic", NONDYADIC, ["1/3", "1/7"])):
        for delta in deltas:
            run = new_run()
            _, m = material(run, params)
            search = ideal_candidate_search(run, m, delta, expected_policy=IDEAL_POLICY)
            for row in search["results"]:
                rem = _claims(run, row["ideal"])[REMAINING]["receipt"]
                widths = {Fraction(hi) - Fraction(lo) for level in rem["enclosures"].values()
                          for boxes in level["boxes"].values() for v in boxes for lo, hi in v}
                cases[f"{name}:{row['seam']}@{delta}"] = {
                    "verdict": row["ideal_geometric_verdict"]["verdict"], AGGREGATE: row[AGGREGATE],
                    "all_box_widths_zero": widths == {0}, "methods": sorted({r["method"] for r in rem["rows"]})}
    _write(out / "prisms.json", {"label": LABEL, "square": SQUARE, "nondyadic": NONDYADIC, "cases": cases})
    return cases


def main(out: Path):
    out.mkdir(parents=True, exist_ok=True)
    timing = {}
    totals = e11_receipts(out, timing)
    prisms = prism_receipts(out)
    manifest = {p.name: "sha256:" + hashlib.sha256(p.read_bytes()).hexdigest()
                for p in sorted(out.iterdir()) if p.name not in ("MANIFEST.json", "timing.json")}
    _write(out / "MANIFEST.json", manifest)
    (out / "timing.json").write_text(json.dumps({"label": "wall-clock, not reproducible", **timing}, indent=1) + "\n",
                                     encoding="ascii", newline="\n")
    return totals, prisms


if __name__ == "__main__":
    t, p = main(Path(sys.argv[1]))
    print(json.dumps(t, indent=1, sort_keys=True))
    print("prism cases:", len(p), "all pass:", all(v["verdict"] == "pass" for v in p.values()),
          "all zero width:", all(v["all_box_widths_zero"] for v in p.values()))
