"""Map the historical eleven-panel certificate convention to Geometry Lab IDs, then compare classifications.

Historical convention (beveled_source_certificate.py + mixed_fixture_certificate.iv_unfold at commit-11):
  hinge t   = cycle.original_edges(HEIGHT)[t], recorded in the certificate as original_hinges[t]
  face f    = the panel between hinges f and f+1 (mod n)
  cut k     = seam at hinge k; panel position s of cut k is face (k+s) mod n
The mapping uses exact coordinates only; no numeric label is assumed to survive normalization.
"""
from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from pathlib import Path

HISTORICAL = Path(__file__).resolve().parent / "historical"
CERT_BLOB = "c571469284a97f9cd2df75b1f047bda3c0bcc7fc"
# Edition 1.1 export: VERIFIER_BLOB identifies the export copy of beveled_source_certificate.py.txt, in which
# one folder name was replaced by a placeholder; the historical blob is 2471d2d11ee2f8ae9ec3f0717f99d35d90a2e2aa.
VERIFIER_BLOB = "e4c31e89df2d279f26ceeab1276829bc5772c7fe"


def git_blob(path: Path) -> str:
    data = path.read_bytes().replace(b"\r\n", b"\n")
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def load_certificate() -> dict:
    cert = HISTORICAL / "beveled_source_certificate.json"
    if git_blob(cert) != CERT_BLOB or git_blob(HISTORICAL / "beveled_source_certificate.py.txt") != VERIFIER_BLOB:
        raise RuntimeError("historical certificate copies differ from their pinned blobs")
    return json.loads(cert.read_text(encoding="utf-8"))


def build_mapping(material: dict, cert: dict) -> dict:
    xyz = {v["id"]: tuple(Fraction(c) for c in v["xyz"]) for v in material["vertices"]}
    ours = {(xyz[e["lower"]], xyz[e["upper"]]): e["id"] for e in material["hinges"]}
    n = len(cert["original_hinges"])
    hinge_map = {}
    for t, (lo, hi) in enumerate(cert["original_hinges"]):
        key = (tuple(Fraction(c) for c in lo), tuple(Fraction(c) for c in hi))
        if key not in ours:
            raise AssertionError(f"historical hinge {t} has no current hinge with equal exact coordinates")
        hinge_map[t] = ours[key]
    if len(set(hinge_map.values())) != n or n != len(material["hinges"]):
        raise AssertionError("hinge mapping is not a bijection")
    index = {e["id"]: i for i, e in enumerate(material["hinges"])}
    rotation = (index[hinge_map[0]]) % n
    if any(index[hinge_map[t]] != (t + rotation) % n for t in range(n)):
        raise AssertionError("historical hinge order is not a cyclic rotation of the current order")
    faces = {f["entry"]: f for f in material["faces"]}
    face_map = {}
    for f in range(n):
        face = faces[hinge_map[f]]
        if face["exit"] != hinge_map[(f + 1) % n]:
            raise AssertionError(f"historical face {f} does not map to a face between the mapped hinges")
        face_map[f] = face["id"]
    return {"rotation_current_minus_historical": rotation, "hinges": hinge_map, "faces": face_map,
            "cuts": dict(hinge_map), "n": n}


def mapped_expectations(cert: dict, mapping: dict) -> dict:
    """Historical labels translated to current IDs (used only to COMPARE; never given to the checker)."""
    col = cert["interior_collision"]
    return {"unsafe_seams": sorted(mapping["cuts"][k] for k in cert["unsafe_cuts"]),
            "safe_seams": sorted(mapping["cuts"][k] for k in cert["safe_cuts"]),
            "cut6": {"seam": mapping["cuts"][col["cut"]],
                     "faces": [mapping["faces"][f] for f in col["original_face_indices"]],
                     "panel_positions": col["panel_positions"], "point": col["point"]},
            "delta": cert["depth"], "height": cert["height"]}
