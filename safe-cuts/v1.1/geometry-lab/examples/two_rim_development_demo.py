"""Stage 3 demo: cut -> static development -> trim -> independent checks -> enumerated seam search
-> saved/replayed run -> static inspection view, on the historical eleven-panel source and F2.

Requires the full repository checkout: the eleven-panel mapping and historical comparison use the
test-side support module (tests/two_rim_dev/eleven_panel.py); historical labels never reach the checkers.
Each seam reports a LOCAL total (the cut chain from the material down) and a SOURCE-LINKED total (plus the
Stage 2 source/material bundles, including matches_parent_source); the two are kept separate.
Usage (from engine/):  python examples/two_rim_development_demo.py OUT_DIR
"""
from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ENGINE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ENGINE))

from glab.core.runfile import load_run, replay  # noqa: E402
from glab.two_rim.search import enumerated_candidate_search  # noqa: E402
from glab.two_rim.view_export import view_data  # noqa: E402
from glab.view.static import main as render  # noqa: E402
from tests.two_rim_dev.eleven_panel import build_mapping, load_certificate, mapped_expectations  # noqa: E402
from tests.two_rim_dev.helpers import E11, E11_DELTA, fixture, material, new_run  # noqa: E402

PAIRS = "two_rim.development.face_interiors_disjoint_all_pairs"
UNGLUED = "two_rim.development.diagnostic.unglued_pairs_disjoint"


def sha(p: Path) -> str:
    return "sha256:" + hashlib.sha256(p.read_bytes()).hexdigest()


def write(p: Path, obj) -> None:
    p.write_text(json.dumps(obj, indent=1, sort_keys=True) + "\n", encoding="ascii", newline="\n")


def summary_rows(run, report):
    rows = []
    for r in report["results"]:
        ev = next(e for e in run.evidence if e["subject"] == r["trimmed"] and e["claim"] == PAIRS)
        rows.append({"seam": r["seam"], "trimmed_local": r["trimmed_obligations"],
                     "trimmed_source_linked": r["source_linked_trimmed_obligations"],
                     "full_local": r["full_obligations"], "full_source_linked": r["source_linked_full_obligations"],
                     "trimmed_all_pairs": r["trimmed_claims"][PAIRS],
                     "trimmed_unglued_pairs": r["trimmed_claims"][UNGLUED],
                     "full_all_pairs": r["full_claims"][PAIRS],
                     "pair_counts": ev["receipt"]["counts"],
                     "interior_overlaps": [{"pair": x["pair"], "overlap_area": x["overlap_area"]}
                                           for x in ev["receipt"]["rows"] if x["reason"] == "interior_overlap"]})
    return rows


def main(out: Path) -> dict:
    out.mkdir(parents=True, exist_ok=True)
    run = new_run()
    _, m11 = material(run, E11)
    _, mf2 = material(run, fixture("F2_nonnested_mixed"))
    cert = load_certificate()
    mapping = build_mapping(run.get(m11)["payload"], cert)
    exp = mapped_expectations(cert, mapping)
    s11 = enumerated_candidate_search(run, m11, E11_DELTA)
    sf2 = enumerated_candidate_search(run, mf2, "1/4")
    digest = run.save(out / "stage3.run.json")
    (out / "retained-digest.txt").write_text(digest + "\n", encoding="ascii", newline="\n")

    rows = summary_rows(run, s11)
    inverse = {v: k for k, v in mapping["cuts"].items()}
    comparison = []
    for r in rows:
        k = inverse[r["seam"]]
        historical = "unsafe" if k in cert["unsafe_cuts"] else "safe"
        ours = r["trimmed_all_pairs"]
        agreement = {("unsafe", "fail"): "agree (overlap detected)", ("safe", "pass"): "agree",
                     ("safe", "unknown"): "not contradicted (unresolved near-contact)",
                     ("unsafe", "unknown"): "NOT DETECTED (unresolved)", ("unsafe", "pass"): "DISAGREE",
                     ("safe", "fail"): "DISAGREE"}[(historical, ours)]
        comparison.append({"historical_cut": k, "current_seam": r["seam"], "historical_exact_class": historical,
                           "current_trimmed_all_pairs": ours, "current_unglued_pairs": r["trimmed_unglued_pairs"],
                           "current_trimmed_local": r["trimmed_local"],
                           "current_trimmed_source_linked": r["trimmed_source_linked"],
                           "comparison": agreement, "interior_overlaps": r["interior_overlaps"]})
    comparison.sort(key=lambda c: c["historical_cut"])
    write(out / "eleven-panel-comparison.json",
          {"mapping": {"rotation_current_minus_historical": mapping["rotation_current_minus_historical"],
                       "hinges": {str(k): v for k, v in mapping["hinges"].items()},
                       "faces": {str(k): v for k, v in mapping["faces"].items()},
                       "cuts": {str(k): v for k, v in mapping["cuts"].items()}},
           "historical_cut6": exp["cut6"], "delta": E11_DELTA, "comparison": comparison,
           "note": "historical classes are exact certificates for this specified ordinary trim only; current "
                   "results are float64 numerical diagnostics"})
    write(out / "search-E11.json", {"search": {k: v for k, v in s11.items() if k != "results"}, "rows": rows})
    e9 = next(r for r in rows if r["seam"] == exp["cut6"]["seam"])
    write(out / "search-F2.json", {"search": {k: v for k, v in sf2.items() if k != "results"},
                                   "rows": summary_rows(run, sf2)})

    loaded = load_run(out / "stage3.run.json", expected_digest=digest)
    report = replay(loaded, new_run()._registry)
    cut6 = next(r for r in s11["results"] if r["seam"] == exp["cut6"]["seam"])
    view = view_data(loaded, cut6["trimmed"],
                     statuses={"local": e9["trimmed_local"], "source_linked": e9["trimmed_source_linked"]})
    write(out / "view-E11-cut6-trimmed.json", view)
    render(["static", str(out / "view-E11-cut6-trimmed.json"), str(out / "E11-cut6-trimmed")])
    result = {"run_digest": digest,
              "load": {"integrity": loaded.integrity, "anchor": loaded.anchor, "authenticated": loaded.authenticated},
              "replay": {k: v for k, v in report.items() if k not in ("run", "actions", "checks")},
              "eleven_panel": [{k: c[k] for k in ("historical_cut", "current_seam", "historical_exact_class",
                                                  "current_trimmed_all_pairs", "current_trimmed_local",
                                                  "current_trimmed_source_linked", "comparison")} for c in comparison],
              "prerequisites": {"E11": s11["prerequisites"], "F2": sf2["prerequisites"]},
              "F2_search": [{k: r[k] for k in ("seam", "trimmed_all_pairs", "trimmed_unglued_pairs", "full_all_pairs",
                                               "trimmed_local", "trimmed_source_linked")}
                            for r in summary_rows(run, sf2)],
              "inspection_view": {"subject": cut6["trimmed"], "seam": exp["cut6"]["seam"],
                                  "problem_pairs": view["problem_pairs"]}}
    write(out / "demo.report.json", result)
    write(out / "MANIFEST.json", {p.name: sha(p) for p in sorted(out.iterdir()) if p.name != "MANIFEST.json"})
    return result


if __name__ == "__main__":
    r = main(Path(sys.argv[1]))
    print("run_digest", r["run_digest"])
    print("load", r["load"])
    print("replay", r["replay"])
    for c in r["eleven_panel"]:
        print(" ", c)
    for f in r["F2_search"]:
        print("  F2", f)
