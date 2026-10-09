"""Write receipts for the fixture + 200-random golden/oracle comparison.

Usage (from engine/):  python -m tests.two_rim.write_golden_receipt OUT.json
"""
import json
import sys
from collections import Counter

from glab.check.two_rim_source import check_material, check_source
from glab.two_rim.material import build_material
from glab.two_rim.source import normalize_source
from tests.two_rim.golden_support import (SEED, checked_claims, compare, fixtures, load_pinned, random_cases,
                                          shared_normal_cases)


def run_case(nfi, ncs, case):
    g = compare(nfi, ncs, **case)
    src = normalize_source(case["top"], case["bottom"], case["height"], case["input_kind"])
    mat = build_material(src)
    claims = checked_claims(case)
    return {"input": case, "golden": g, "material_identity": mat["identity"],
            "oracle": {c.predicate: c.outcome for c in claims}}


def main(out):
    nfi, ncs = load_pinned()
    cases, stats = random_cases()
    fx = {name: run_case(nfi, ncs, case) for name, case in fixtures().items()}
    rnd = [run_case(nfi, ncs, case) for case in cases]
    ok = lambda r: all(r["golden"][k] for k in ("hull_match", "hinges_match", "rays_match", "facets_match")) \
        and set(r["oracle"].values()) == {"pass"}
    summary = {"seed": SEED, "generator": "tests/two_rim/golden_support.py random_cases: each rim 3-8 points, "
               "coordinates p/q with |p| <= 60 and q in {1,2,3,5,7}, height p/q with p in 1..40 and "
               "q in {1,2,3,7,10,1000}, input kind uniform; cyclic rims built from the points' hull with "
               "random orientation and start", **stats,
               "fixtures_all_ok": all(ok(r) for r in fx.values()),
               "random_all_ok": all(ok(r) for r in rnd), "random_ok_count": sum(ok(r) for r in rnd),
               "oracle_coverage": "all 200 random cases and all 4 fixtures (no subset)",
               "input_kinds": dict(Counter(r["input"]["input_kind"] for r in rnd)),
               "faces_histogram": dict(sorted(Counter(r["golden"]["faces"] for r in rnd).items())),
               "cases_with_triangles": sum(r["golden"]["triangles"] > 0 for r in rnd),
               "cases_all_trapezoids": sum(r["golden"]["triangles"] == 0 for r in rnd),
               "nonzero_rotation_offsets": sum(r["golden"]["rotation"] != 0 for r in rnd)}
    sup = [run_case(nfi, ncs, case) for case in shared_normal_cases()]
    summary["supplementary_shared_normal_family"] = {
        "seed": SEED + 1, "cases": len(sup), "all_ok": all(ok(r) for r in sup),
        "all_trapezoid_cases": sum(r["golden"]["triangles"] == 0 for r in sup),
        "note": "extra coverage for shared normals; not counted toward the 200 random cases"}
    data = {"summary": summary, "fixtures": fx, "random": rnd, "supplementary": sup}
    with open(out, "w", encoding="ascii", newline="\n") as f:
        f.write(json.dumps(data, indent=1, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main(sys.argv[1])
