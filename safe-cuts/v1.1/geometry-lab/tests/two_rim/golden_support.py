"""Golden comparison against byte-verified pinned originals, plus the seeded random case generator.

The pinned originals are loaded by file path with importlib (no sys.path edits); nothing is
written into the historical Observatory directories. A golden match establishes consistency
with the original implementation only; the independent oracle is separate evidence.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
import random
import sys
from fractions import Fraction
from pathlib import Path

from glab.core.numbers import format_exact
from glab.core.records import StateStore
from glab.core.runfile import DependencyContext
from glab.two_rim.material import build_material
from glab.two_rim.source import SourceInputError, hull2, normalize_source

HERE = Path(__file__).resolve().parent
PINNED = {"normal_fan_inputs.py": "5445ec10af581ae031cb386d1732de4a81dffee9",
          "cyclic_normal_splice.py": "314b1938fb80416a5c867a0e9db7807ed3e9133a"}
# Edition 1.1 export: the F1 and X pins identify sanitized fixture copies (provenance text only; coordinates
# unchanged); the historical fixtures and pins are retained privately.
FIXTURE_BLOBS = {"F1_translated_square_prism": "133ddb0f05798d64bb8dd5879d94f7b609e4f9e1",
                 "F2_nonnested_mixed": "2b6cf505d945712f8f220b6812e48c658f4e1315",
                 "F3_near_degenerate_prism": "ba932ca4e1b1652367801947a177c55da3f55c24",
                 "X_pinned_hard_flat": "2e144606766a5361ba87d7b4fa05248dd0faee05"}
KIND_RENAME = {"cyclic_convex_polygon": "cyclic_boundary", "point_set_hull": "point_set_hull"}
SEED = 20260928
N_VALID = 200


def checked_claims(case):
    """All v2 claims for one case: source + material, the material checked with its real source context."""
    from glab.check.two_rim_source import check_material, check_source
    src = normalize_source(case["top"], case["bottom"], case["height"], case["input_kind"])
    mat = build_material(src)
    store = StateStore()
    s = store.put({"schema": "glab.state/1", "kind": "two_rim.source", "parent": None, "representation": "exact",
                   "payload": src})
    mstate = {"schema": "glab.state/1", "kind": "two_rim.material", "parent": s, "representation": "exact",
              "payload": mat}
    m = store.put(mstate)
    return check_source(store.get(s), {}) + check_material(store.get(m), {}, DependencyContext(store, m))


def git_blob(path: Path) -> str:
    data = path.read_bytes().replace(b"\r\n", b"\n")
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def load_pinned():
    """Return (normal_fan_inputs, cyclic_normal_splice) loaded from the verified copies."""
    for name, blob in PINNED.items():
        got = git_blob(HERE / "pinned" / name)
        if got != blob:
            raise RuntimeError(f"pinned {name} blob {got} != {blob}")
    saved = sys.modules.get("normal_fan_inputs")
    try:
        mods = []
        for name in ("normal_fan_inputs", "cyclic_normal_splice"):
            spec = importlib.util.spec_from_file_location(name, HERE / "pinned" / f"{name}.py")
            mod = importlib.util.module_from_spec(spec)
            sys.modules[name] = mod  # the splice module imports this exact name
            spec.loader.exec_module(mod)
            mods.append(mod)
        return tuple(mods)
    finally:
        for name in ("normal_fan_inputs", "cyclic_normal_splice"):
            sys.modules.pop(name, None)
        if saved is not None:
            sys.modules["normal_fan_inputs"] = saved


def fixtures():
    out = {}
    for name, blob in FIXTURE_BLOBS.items():
        path = HERE / "fixtures" / f"{name}.json"
        if git_blob(path) != blob:
            raise RuntimeError(f"fixture {name} differs from the assessment blob")
        p = json.loads(path.read_text(encoding="utf-8"))["params"]
        out[name] = dict(p, input_kind=KIND_RENAME[p["input_kind"]])
    return out


def _fr3(p):
    return tuple(Fraction(c) for c in p)


def compare(nfi, ncs, top, bottom, height, input_kind) -> dict:
    """Ours vs the pinned originals (as PhysicalBridge used them: reversed(hull2(points)))."""
    ours = build_material(normalize_source(top, bottom, height, input_kind))
    raw = lambda pts: [(Fraction(x), Fraction(y)) for x, y in ((str(a), str(b)) for a, b in pts)]
    a = list(reversed(nfi.hull2(raw(top))))
    b = list(reversed(nfi.hull2(raw(bottom))))
    cycle = ncs.splice_cycles(a, b)
    h = Fraction(str(height))
    orig_edges = [(_fr3(lo), _fr3(hi)) for lo, hi in cycle.original_edges(h)]
    orig_facets = [frozenset(_fr3(p) for p in f) for f in cycle.facets(h)]
    xyz = {v["id"]: _fr3(v["xyz"]) for v in ours["vertices"]}
    our_edges = [(xyz[e["lower"]], xyz[e["upper"]]) for e in ours["hinges"]]
    n = len(orig_edges)

    def rim(name):
        return {(Fraction(v["xyz"][0]), Fraction(v["xyz"][1])) for v in ours["vertices"] if v["rim"] == name}
    result = {"faces": len(ours["faces"]), "triangles": sum(f["shape"] == "triangle" for f in ours["faces"]),
              "same_hinge_count": len(our_edges) == n, "rotation": None, "hinges_match": False,
              "rays_match": False, "facets_match": False,
              "hull_match": rim("top") == set(a) and rim("bottom") == set(b)}
    if len(our_edges) != n:
        return result
    rot = next((r for r in range(n) if all(our_edges[t] == orig_edges[(t + r) % n] for t in range(n))), None)
    result["rotation"] = rot
    if rot is None:
        return result
    result["hinges_match"] = True
    result["rays_match"] = all(list(ours["faces"][t]["outward_ray"]) == list(cycle.rays[(t + 1 + rot) % n])
                               for t in range(n))
    # original facet i lies between hinge i-1 and hinge i; ours F_t between E_t and E_{t+1}
    result["facets_match"] = all(frozenset(xyz[v] for v in ours["faces"][t]["boundary"]) ==
                                 orig_facets[(t + 1 + rot) % n] for t in range(n))
    return result


def _rational(rng):
    return Fraction(rng.randint(-60, 60), rng.choice([1, 1, 1, 2, 3, 5, 7]))


def random_cases(seed=SEED, n_valid=N_VALID):
    """Deterministic valid cases plus rejection counts. Each rim: 3-8 points; |coords| <= 60."""
    rng = random.Random(seed)
    cases, rejected, attempts = [], {}, 0
    while len(cases) < n_valid:
        attempts += 1
        kind = rng.choice(["cyclic_boundary", "point_set_hull"])
        rims = []
        for _ in range(2):
            pts = [(_rational(rng), _rational(rng)) for _ in range(rng.randint(3, 8))]
            if kind == "cyclic_boundary":
                try:
                    ring = hull2(pts)  # a valid boundary ring built from the random points
                except SourceInputError:
                    ring = pts         # keep the invalid ring; normalization will reject it
                ring = ring[::-1] if rng.random() < 0.5 else ring
                k = rng.randrange(len(ring))
                pts = ring[k:] + ring[:k]
            rims.append([[format_exact(x) if x.denominator != 1 else int(x), format_exact(y)] for x, y in pts])
        height = format_exact(Fraction(rng.randint(1, 40), rng.choice([1, 2, 3, 7, 10, 1000])))
        try:
            normalize_source(rims[0], rims[1], height, kind)
        except SourceInputError as exc:
            reason = str(exc).split(":")[0]
            rejected[reason] = rejected.get(reason, 0) + 1
            continue
        cases.append({"top": rims[0], "bottom": rims[1], "height": height, "input_kind": kind})
    return cases, {"attempts": attempts, "valid": len(cases), "rejected": rejected}


def shared_normal_cases(seed=SEED + 1, n=50):
    """Supplementary family (not part of the 200): bottom = rational homothety of top, so every edge
    normal is shared (all trapezoids); every other case adds one outside point to the bottom, which
    creates some one-rim normals (mixed). Deterministic from `seed`."""
    rng = random.Random(seed)
    cases = []
    while len(cases) < n:
        pts = [(_rational(rng), _rational(rng)) for _ in range(rng.randint(3, 7))]
        try:
            top = hull2(pts)
        except SourceInputError:
            continue
        k = Fraction(rng.randint(1, 6), rng.randint(1, 3))
        shift = (_rational(rng), _rational(rng))
        bottom = [(k * x + shift[0], k * y + shift[1]) for x, y in top]
        if len(cases) % 2:
            cx = max(x for x, _ in bottom) + Fraction(rng.randint(1, 9), 2)
            bottom = bottom + [(cx, sum(y for _, y in bottom) / len(bottom))]
        fmt = lambda ring: [[format_exact(x), format_exact(y)] for x, y in ring]
        cases.append({"top": fmt(top), "bottom": fmt(bottom), "height": format_exact(Fraction(rng.randint(1, 9), 4)),
                      "input_kind": "point_set_hull"})
    return cases
