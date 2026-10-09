"""Derive the two Figure 1 panel-pair images for the illustrated candidate from the supplied composite.

Usage: python make_figure_panels.py SOURCE_PNG OUT_DIR
Deterministic crop only: no resampling, recolouring or regeneration. The source must be the supplied
figure/out/safe-cuts-e4-e9-comparison.png (SHA-256 pinned below). Crop boxes were chosen from measured blank
pixel bands of that image: blank columns 1736-1747 separate panel (b) from panel (c), and the panels occupy rows
75-1016 above the footer line (rows 1127-1146), which the article reproduces as typeset text instead.
"""
import hashlib
import json
import sys
from pathlib import Path

from PIL import Image

SOURCE_SHA256 = "ae53ede5ed9a8e2f91807d1ff7c18c0c387e7dd1d727f3a52996dc45c1b5e47c"
BOXES = {  # (left, upper, right, lower) in source pixels; right/lower exclusive
    "figure-1-panels-a-b.png": (140, 50, 1742, 1035),
    "figure-1-panels-c-d.png": (1742, 50, 3390, 1035),
}


def main():
    src, out = Path(sys.argv[1]), Path(sys.argv[2])
    raw = src.read_bytes()
    if hashlib.sha256(raw).hexdigest() != SOURCE_SHA256:
        raise SystemExit("source PNG is not the supplied figure; nothing written")
    im = Image.open(src)
    im.load()
    out.mkdir(parents=True, exist_ok=True)
    record = {"source": "figure/out/safe-cuts-e4-e9-comparison.png", "source_sha256": SOURCE_SHA256,
              "source_pixels": list(im.size), "dpi": 200, "operation": "crop only (no scaling)", "outputs": {}}
    for name, box in BOXES.items():
        crop = im.crop(box)
        path = out / name
        crop.save(path, format="PNG", dpi=(200, 200))
        data = path.read_bytes()
        record["outputs"][name] = {"box": list(box), "pixels": list(crop.size),
                                   "sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}
    print(json.dumps(record, indent=1))


if __name__ == "__main__":
    main()
