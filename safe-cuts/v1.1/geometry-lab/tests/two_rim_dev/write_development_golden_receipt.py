"""Golden comparison of glab.two_rim.develop against the pinned historical bridge, every seam of every case.

Cases: the 4 assessment fixtures, the eleven-panel source, the 200 seeded random pairs and the
50 supplementary shared-normal pairs from Stage 2. Records the maximum absolute deviation.
Usage (from engine/):  python -m tests.two_rim_dev.write_development_golden_receipt OUT.json
"""
import json
import sys
from fractions import Fraction

import numpy as np

from glab.two_rim.cut import open_cut
from glab.two_rim.develop import develop_static
from glab.two_rim.material import build_material
from glab.two_rim.source import normalize_source
from tests.two_rim.golden_support import SEED, fixtures, random_cases, shared_normal_cases
from tests.two_rim_dev.bridge_support import load_bridge
from tests.two_rim_dev.helpers import E11


def compare_case(bridge_mod, case):
    mat = build_material(normalize_source(case["top"], case["bottom"], case["height"], case["input_kind"]))
    top = [(Fraction(v["xyz"][0]), Fraction(v["xyz"][1])) for v in mat["vertices"] if v["rim"] == "top"]
    bottom = [(Fraction(v["xyz"][0]), Fraction(v["xyz"][1])) for v in mat["vertices"] if v["rim"] == "bottom"]
    bridge = bridge_mod.PhysicalBridge(top, bottom, Fraction(mat["height"]))
    xyz = {v["id"]: np.array([float(Fraction(c)) for c in v["xyz"]]) for v in mat["vertices"]}
    worst_lin, worst_off, seams = 0.0, 0.0, 0
    for e in mat["hinges"]:
        k = next(i for i in range(bridge.n) if np.array_equal(bridge.low[i], xyz[e["lower"]])
                 and np.array_equal(bridge.high[i], xyz[e["upper"]]))
        ours = develop_static(open_cut(mat, e["id"]))["maps"]
        for mine, ref in zip(ours, bridge.maps(k)):
            worst_lin = max(worst_lin, float(np.max(np.abs(np.array(mine["linear"]) - ref.linear))))
            worst_off = max(worst_off, float(np.max(np.abs(np.array(mine["offset"]) - ref.offset))))
        seams += 1
    return {"faces": len(mat["faces"]), "seams": seams, "max_abs_linear_dev": worst_lin, "max_abs_offset_dev": worst_off}


def main(out):
    bridge_mod = load_bridge()
    groups = {"fixtures": list(fixtures().values()) + [E11], "random_200": random_cases()[0],
              "supplementary_50": shared_normal_cases()}
    result = {"seed_random": SEED, "seed_supplementary": SEED + 1, "groups": {}}
    for name, cases in groups.items():
        rows = [compare_case(bridge_mod, c) for c in cases]
        result["groups"][name] = {"cases": len(rows), "seams": sum(r["seams"] for r in rows),
                                  "max_abs_linear_dev": max(r["max_abs_linear_dev"] for r in rows),
                                  "max_abs_offset_dev": max(r["max_abs_offset_dev"] for r in rows)}
    result["note"] = ("golden agreement establishes implementation consistency with the historical floating "
                      "diagnostic, not correctness or a proof")
    with open(out, "w", encoding="ascii", newline="\n") as f:
        f.write(json.dumps(result, indent=1, sort_keys=True) + "\n")
    print(json.dumps(result, indent=1))


if __name__ == "__main__":
    main(sys.argv[1])
