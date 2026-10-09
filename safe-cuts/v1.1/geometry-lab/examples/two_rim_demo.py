"""Stage 2 headless demo: exact two-rim source -> original material -> independent checks -> save/replay.

Updated in the D01-D03 repair: v2 checkers and the complete requirement set (source record and
geometry, material record and geometry, and material-to-parent-source correspondence), plus one
deliberately faulty registered builder (height-4 material under the height-2 F2 source) that only the
correspondence claim can catch. No floating placements, cuts, trims or rendering.
Usage (from engine/):  python examples/two_rim_demo.py OUT_DIR
"""
from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ENGINE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ENGINE))

from glab.check.two_rim_source import MATERIAL_CLAIMS, SOURCE_CLAIMS, register_checkers  # noqa: E402
from glab.core.evidence import Requirement, summarize  # noqa: E402
from glab.core.registry import ActionSpec, Registry, StateDraft  # noqa: E402
from glab.core.runfile import Run, load_run, replay  # noqa: E402
from glab.two_rim.actions import register_actions  # noqa: E402
from glab.two_rim.material import build_material, material_identity  # noqa: E402
from glab.two_rim.source import normalize_source  # noqa: E402

FIXTURES = ENGINE / "tests" / "two_rim" / "fixtures"
RENAME = {"cyclic_convex_polygon": "cyclic_boundary", "point_set_hull": "point_set_hull"}
CLAIMS = {"two_rim.source": list(SOURCE_CLAIMS), "two_rim.material": list(MATERIAL_CLAIMS)}


def fixture(name):
    p = json.loads((FIXTURES / f"{name}.json").read_text(encoding="utf-8"))["params"]
    return dict(p, input_kind=RENAME[p["input_kind"]])


def _wrong_height_builder(subject, params, seed):
    """Deliberately faulty demo builder: a valid material of a DIFFERENT (height 4) source."""
    other = dict(fixture("F2_nonnested_mixed"), height="4")
    m = build_material(normalize_source(**other))
    m["identity"] = material_identity(m)
    return StateDraft("two_rim.material", m, "exact")


def registry():
    reg = Registry()
    register_actions(reg)
    register_checkers(reg)
    reg.register_action(ActionSpec("demo.faulty.material_from_other_source", 1, "two_rim.source", {},
                                   "demo-faulty-1", _wrong_height_builder))
    return reg


def sha(p: Path) -> str:
    return "sha256:" + hashlib.sha256(p.read_bytes()).hexdigest()


def main(out: Path) -> dict:
    out.mkdir(parents=True, exist_ok=True)
    reg = registry()
    run = Run(reg)
    f2 = fixture("F2_nonnested_mixed")
    inputs = {"F2": f2,
              "F2_reversed_rotated": dict(f2, top=f2["top"][::-1], bottom=f2["bottom"][2:] + f2["bottom"][:2]),
              "F3_perturbed_1e-20": fixture("F3_near_degenerate_prism"),
              "X_point_set_hull": fixture("X_pinned_hard_flat")}
    built, requirements = {}, []
    for label, params in inputs.items():
        s = run.apply("two_rim.source.normalize", 1, params)["output"]
        m = run.apply("two_rim.material.build", 1, {}, s)["output"]
        run.check("two_rim.check.source", 2, s, {})
        run.check("two_rim.check.material", 2, m, {})
        requirements += [Requirement(c, s) for c in CLAIMS["two_rim.source"]]
        requirements += [Requirement(c, m) for c in CLAIMS["two_rim.material"]]
        built[label] = (s, m)
    s_f2 = built["F2"][0]
    wrong = run.apply("demo.faulty.material_from_other_source", 1, {}, s_f2)["output"]
    wrong_claims = {e["claim"]: e["outcome"] for e in run.check("two_rim.check.material", 2, wrong, {})}
    wrong_reqs = [Requirement(c, wrong) for c in CLAIMS["two_rim.material"]]
    failed = run.apply("two_rim.source.normalize", 1, dict(f2, top=[[0, 0], [4, 0], [1, 1], [0, 4]]))
    rejected = run.apply("two_rim.source.normalize", 1, dict(f2, top=[[0, 0], [4, 0.5], [0, 4]]))
    digest = run.save(out / "two_rim.run.json")
    (out / "retained-digest.txt").write_text(digest + "\n", encoding="ascii", newline="\n")

    loaded = load_run(out / "two_rim.run.json", expected_digest=digest)
    as_loaded = summarize(loaded.record["evidence"], requirements, loaded.store, reg)
    report = replay(loaded, reg)
    after = report["run"].summarize(requirements)
    materials = {}
    for label, (s, m) in built.items():
        src, mat = run.get(s)["payload"], run.get(m)["payload"]
        materials[label] = {
            "source_state": s, "material_state": m, "material_identity": mat["identity"],
            "faces": len(mat["faces"]), "triangles": sum(f["shape"] == "triangle" for f in mat["faces"]),
            "trapezoids": sum(f["shape"] == "trapezoid" for f in mat["faces"]),
            "hinges": [[e["id"], e["lower"], e["upper"]] for e in mat["hinges"]],
            "normalization": src["normalization"]}
    result = {
        "run_digest": digest,
        "materials": materials,
        "presentation_check": {
            "F2_vs_reversed_same_identity": materials["F2"]["material_identity"] ==
            materials["F2_reversed_rotated"]["material_identity"],
            "F2_vs_reversed_different_states": built["F2"] != built["F2_reversed_rotated"]},
        "perturbation_exact": any(v["xyz"][1] == "300000000000000000001/100000000000000000000"
                                  for v in run.get(built["F3_perturbed_1e-20"][1])["payload"]["vertices"]),
        "faulty_builder_height4_under_height2_source": {
            "claims": wrong_claims,
            "summary_after_replay": report["run"].summarize(wrong_reqs)["outcome"]},
        "failed_attempt": {"status": failed["status"], "type": failed["failure"]["type"]},
        "rejected_attempt": {"status": rejected["status"], "message": rejected["failure"]["message"]},
        "load": {"integrity": loaded.integrity, "anchor": loaded.anchor, "authenticated": loaded.authenticated},
        "summary_as_loaded": {"outcome": as_loaded["outcome"], "verified": as_loaded["verified"]},
        "replay": {k: v for k, v in report.items() if k != "run"},
        "summary_after_replay": {"outcome": after["outcome"], "verified": after["verified"],
                                 "requirements": len(after["requirements"])},
    }
    (out / "two_rim.report.json").write_text(json.dumps(result, indent=1, sort_keys=True) + "\n",
                                            encoding="ascii", newline="\n")
    manifest = {p.name: sha(p) for p in sorted(out.iterdir()) if p.name != "MANIFEST.json"}
    (out / "MANIFEST.json").write_text(json.dumps(manifest, indent=1) + "\n", encoding="ascii", newline="\n")
    return result


if __name__ == "__main__":
    r = main(Path(sys.argv[1]))
    print("run_digest", r["run_digest"])
    for label, m in r["materials"].items():
        print(f"  {label}: faces={m['faces']} (triangles {m['triangles']}, trapezoids {m['trapezoids']}) "
              f"identity={m['material_identity'][:23]}...")
    print("presentation", r["presentation_check"], "| 1e-20 kept exactly:", r["perturbation_exact"])
    print("faulty builder (height-4 material under height-2 F2 source):",
          r["faulty_builder_height4_under_height2_source"])
    print("failed", r["failed_attempt"], "| rejected", r["rejected_attempt"]["status"])
    print("load", r["load"])
    print("summary as loaded", r["summary_as_loaded"])
    print("replay", r["replay"]["outcome"], "| digest reproduced:", r["replay"]["run_digest_reproduced"],
          "| partial:", r["replay"]["partial_comparison"])
    print("summary after replay", r["summary_after_replay"])
