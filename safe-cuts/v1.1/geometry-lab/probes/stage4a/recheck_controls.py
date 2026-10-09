"""ISOLATED STAGE 4A PROTOTYPE: negative controls for the independent re-checker (standard library only).

Writes deliberately corrupted copies of a re-check bundle; each must make recheck_mpmath.py report failures.
Usage:  python recheck_controls.py BUNDLE.json OUT_DIR
"""
from __future__ import annotations

import copy
import json
import sys
from fractions import Fraction
from pathlib import Path


def _write(path, bundle):
    path.write_text(json.dumps(bundle, indent=None, sort_keys=True) + "\n", encoding="ascii", newline="\n")


def main(bundle_path, out_dir):
    base = json.loads(Path(bundle_path).read_text(encoding="ascii"))
    out = Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)
    seam = "E9"
    S = base["seams"][seam]
    f0 = S["chain"][5]
    cases = {}

    # 1. A probe box shifted by more than twice its own width: containment must fail.
    b = copy.deepcopy(base)
    box = b["seams"][seam]["boxes"][f0][2][0]
    shift = 2 * (Fraction(box[1]) - Fraction(box[0])) + Fraction(1, 2**200)
    b["seams"][seam]["boxes"][f0][2][0] = [str(Fraction(box[0]) + shift), str(Fraction(box[1]) + shift)]
    cases["shifted_box"] = b

    # 2. An axis certificate whose recorded gap is changed: confirmation must fail.
    b = copy.deepcopy(base)
    row = next(r for r in b["seams"][seam]["rows"] if r.get("method") == "separating_axis")
    row["certificate"]["axis_gap"] = str(Fraction(row["certificate"]["axis_gap"]) + 1)
    cases["altered_axis_gap"] = b

    # 3. A witness moved outside one face: confirmation must fail.
    b = copy.deepcopy(base)
    row = next(r for r in b["seams"][seam]["rows"] if r.get("method") == "interior_witness")
    row["certificate"]["witness"] = ["1000", "1000"]
    cases["moved_witness"] = b

    # 4. A recorded side value altered: Theorem S confirmation must fail.
    b = copy.deepcopy(base)
    row = next(r for r in b["seams"][seam]["rows"] if r.get("method") == "shared_hinge_exact")
    face = row["pair"][0]
    label = next(iter(row["shared_hinge"]["sigma"][face]))
    row["shared_hinge"]["sigma"][face][label] = "12345"
    cases["altered_sigma"] = b

    # 5. A wrong face normal in the exact inputs (inward plane): side checks must fail.
    b = copy.deepcopy(base)
    fid = S["chain"][4]
    for f in b["faces"]:
        if f["id"] == fid:
            f["plane"] = [-c for c in f["plane"]]
    cases["inward_normal_input"] = b

    for name, bundle in cases.items():
        bundle["seams"] = {seam: bundle["seams"][seam]}
        _write(out / f"{name}.json", bundle)
    print(sorted(cases))


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
