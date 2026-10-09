---
title: Two-rim domain schema and API (Stage 2)
author: Claude Code session agent, Claude Opus 5.5
date: 2026-09-28
status: Stage 2 domain contract; consumed by later stages only after review
dg-publish: false
---

# Conventions

- **Units:** `"unitless"`.
- **Numbers:** exact rationals, written as the canonical strings `"n"` or `"n/d"` from `format_exact`. Inputs may be integers or exact strings; floats and bools are rejected. **Execution is limited to represented rational inputs.**
- **Coordinates:** right-handed `xyz`. The bottom rim B lies at `z = 0` and the top rim A at `z = h`, following the manuscript's `K = conv(B×{0} ∪ A×{h})`.
- **Rim order:** each normalized rim is a strictly convex polygon in **clockwise** order (negative signed area in the `xy` plane). It starts at its lexicographically smallest vertex, comparing `x` and then `y`.
- **Hinge and face order:** the order of `splice_cycles` over the clockwise merged normal fan, which is the clockwise normal order of DRAFT-02 Proposition 3.1.
  - Hinge `E_t` is the original lateral edge for the gap that follows normal ray `t`.
  - Face `F_t` lies between entry hinge `E_t` and exit hinge `E_{t+1}` (indices mod `n`), and its outward normal is ray `t+1`. This is the manuscript's `F_i` between `E_i` and `E_{i+1}`.

# Source state, kind `two_rim.source` (representation `exact`)

```json
{"schema": "two_rim.source/1", "units": "unitless", "coordinate_convention": "<text above>",
 "number_domain": "exact_rational",
 "input": {"top": [[x, y], ...], "bottom": [...], "height": h, "input_kind": "..."},
 "normalized": {"top": [["x", "y"], ...], "bottom": [...], "height": "p/q"},
 "normalization": {"top": <decision>, "bottom": <decision>}}
```

**Input kinds:**

- **`cyclic_boundary`.** The input must already be a simple, strictly convex boundary ring with at least 3 points. Duplicates, collinear triples, reflex turns, self-crossing, and multiple winding are all rejected. Nothing is repaired.
  - The decision records `input_count`, `input_orientation` (`clockwise` or `counterclockwise`), `reversed`, `start_input_index` (the input index of the canonical start vertex), and `removed: []`.
- **`point_set_hull`.** An explicit hull operation, the ported `hull2`.
  - The decision records `input_count`, `hull_vertex_count`, and `removed`. Every input point that is not a canonical hull vertex appears in `removed` as `{"input_index", "point", "reason"}`. The reason is one of:
    - `duplicate`: equal to an earlier input point
    - `boundary_non_vertex`: on the hull boundary but not a vertex
    - `interior`: strictly inside the hull
  - Fewer than 3 hull vertices means the rim has empty interior, and the input is rejected.

**Other input rules:**

- A point is a list of exactly two exact numbers.
- `height` must be greater than 0.
- `input` preserves the presentation exactly as given. It is provenance, not identity.

# Material state, kind `two_rim.material` (representation `exact`, parent = its source)

```json
{"schema": "two_rim.material/1", "identity": "sha256:...",
 "units": "unitless", "coordinate_convention": "...", "number_domain": "exact_rational",
 "height": "p/q",
 "vertices": [{"id": "A0", "rim": "top", "xyz": ["x", "y", "h"]}, ..., {"id": "B0", "rim": "bottom", "xyz": [...]}],
 "rim_edges": [{"id": "RA0", "rim": "top", "ends": ["A0", "A1"]}, ...],
 "hinges": [{"id": "E0", "lower": "B3", "upper": "A0"}, ...],
 "faces": [{"id": "F0", "entry": "E0", "exit": "E1", "shape": "trapezoid" | "triangle",
            "boundary": ["B3", "A0", "A1", "B4"], "boundary_edges": ["E0", "RA0", "E1", "RB3"],
            "outward_ray": [ux, uy], "plane": [a, b, c, d]}, ...],
 "caps": [{"id": "C_TOP", "rim": "top", "boundary": [...], "boundary_edges": [...], "plane": [0, 0, q, p]},
          {"id": "C_BOTTOM", "rim": "bottom", ...}]}
```

**Identifiers:**

| ID | Meaning |
|---|---|
| `A{i}` / `B{j}` | the canonical clockwise index on the top or bottom rim |
| `RA{i}` | the top rim edge from `A{i}` to `A{i+1}` |
| `RB{j}` | the bottom rim edge from `B{j}` to `B{j+1}` |
| `E{t}` | a hinge |
| `F{t}` | a lateral face |
| `C_TOP` / `C_BOTTOM` | a cap |

**Faces:**

- A face's boundary ring is `[L_t, U_t, U_{t+1}, L_{t+1}]`. `L` and `U` are the lower (`B`) and upper (`A`) endpoints of its entry and exit hinges.
- **The ring always starts at `L_t`.** When a run vanishes, the *second* copy is dropped: `U_{t+1}` if it equals `U_t`, and `L_{t+1}` if it equals `L_t`. Clarified during Stage 2, after the independent checker's wrap-around de-duplication produced a rotated ring on a bottom-vanishing triangle.
- **The ring has 3 vertices (a triangle) exactly when one rim run vanishes**, and 4 otherwise (a trapezoid, which includes a parallelogram).
- `boundary_edges[k]` joins `boundary[k]` to `boundary[k+1]`.
- **Ring orientation:** counterclockwise as seen from outside, that is, right-handed about the outward normal. The checker requires every lateral ring to have the same strict orientation and reports it: `ring_orientation_about_outward_normal = [1]` on every fixture.
- No triangulation, diagonal, or rendering edge is ever added.

**Planes:**

- `plane` holds the primitive integers `(a, b, c, d)` with the outward normal `(a, b, c)`, where every point of `K` satisfies `a x + b y + c z ≤ d`.
- For a lateral face with primitive ray `u`, the plane is `u·x + ((σ_B(u) − σ_A(u))/h) z = σ_B(u)`, scaled to primitive integers (Proposition 3.1).
- Caps are **source faces only**, marked by their `rim` field. Nothing in this stage places or unfolds them.

**`identity`** is `content_hash` of every field above except `identity` itself. It does **not** include the parent, the input presentation, or the normalization decisions. So reversed or rotated presentations have different source hashes, and different material *state* hashes because the parents differ, but the **same material `identity`**. Units, the coordinate convention, and the number domain are inside the identity, because they affect meaning.

# Registered operations

| Name, version | Accepts | Parameters | Produces |
|---|---|---|---|
| `two_rim.source.normalize` v1 | none | `top`, `bottom`: `Param.list(Param.list(Param.exact()))`; `height`: `Param.exact()`; `input_kind`: `Param.enum(["cyclic_boundary", "point_set_hull"])` | `two_rim.source` |
| `two_rim.material.build` v1 | `two_rim.source` | none | `two_rim.material` |

Point dimension and polygon conditions are domain checks, not registry checks. A structurally valid parameter set that violates them is a **failed** attempt (execution stage), with type `SourceInputError`. A parameter-type violation, for example a float coordinate, is a **rejected** attempt.

**Checkers** (`glab.check.two_rim_source`, which imports only `glab.core`), **v2** since the D01–D03 repair. Version 1 is no longer registered. Every claim uses `exact_computation`, `exact_rational`, and coverage `all`.

| Checker | Accepts | Claims |
|---|---|---|
| `two_rim.check.source` v2 | `two_rim.source` | `two_rim.source.record_schema`, evaluated first; `two_rim.source.height_positive`; `two_rim.source.rims_strictly_convex_clockwise`; `two_rim.source.normalization_accounts_for_input` (a cyclic input is a rotation or reversal of the normalized ring; a hull input's normalized ring equals the brute-force extreme points, and every removed point and reason is verified) |
| `two_rim.check.material` v2, **contextual** (`uses_context=True`) | `two_rim.material` | `two_rim.material.record_schema`, evaluated first; `two_rim.material.identity_hash`; `two_rim.material.facets_match_supporting_plane_oracle` (brute-force exact supporting planes over the lifted rim vertices: lateral facets, caps, and plane coefficients); `two_rim.material.incidence_and_rings` (hinge chain, shared vertex pairs, convex and uniformly oriented lateral rings, each rim edge on exactly one face and one cap, every vertex on a hinge, **and each cap ring equal to its rim in canonical clockwise source order, with aligned edges**); **`two_rim.material.matches_parent_source`** |

**Record schemas (D02, D03).** A record's schema claim is checked **on the lists before any set or dict is built**. It covers:
- the supported schema version and the exact key sets
- units, the documented coordinate convention text, and the number domain
- planar points with exactly two coordinates
- exact input spellings kept as given, and canonical exact strings in normalized and material fields
- the shape of each normalization decision
- ID namespaces and uniqueness: `A0…A{m−1}` then `B0…B{k−1}`; `RA`/`RB` with consecutive ends; `E0…E{n−1}` and `F0…F{n−1}`; caps exactly `[C_TOP, C_BOTTOM]`
- counts and references

**If a record's schema claim fails, every other claim for that record is `unknown`, marked not interpreted.** An unknown version is never read as the old one.

**Correspondence (D01).** `two_rim.material.matches_parent_source` reads the material's actual immediate parent through the core's read-only `DependencyContext`, never by calling the generator. It compares:
- the normalized top and bottom coordinates, in canonical order, with the `A{i}`/`B{j}` association and counts
- the `z` heights and `height`
- the cap planes
- units, the coordinate convention, and the number domain

A missing parent, a parent of the wrong kind, an invalid parent schema, or any mismatch gives `fail`. A direct call without a context gives `unknown`. The context's closure is the check's recorded `dependencies`, so any change to the source makes the evidence stale.

**Still intrinsic.** The other material claims concern the material's own coordinates. A valid body attached under the wrong source passes them and fails only the correspondence claim. That is the intended separation.

# Python API

- **`glab.two_rim.source`:** `normalize_source(top, bottom, height, input_kind) -> dict` (the source payload), `hull2(points)` (ported), `SourceInputError`.
- **`glab.two_rim.material`:** `build_material(source_payload) -> dict` (the material payload), `splice_cycles(a_cw, b_cw)` (ported), `material_identity(payload)`.
- **`glab.two_rim.actions`:** `register_actions(registry)` and `TWO_RIM_REVISION`.
- **`glab.check.two_rim_source`:** `register_checkers(registry)` (v2), `CHECKER_REVISION`, `SOURCE_CLAIMS`, `MATERIAL_CLAIMS`, `check_source(state, params)`, and `check_material(state, params, context=None)`.
