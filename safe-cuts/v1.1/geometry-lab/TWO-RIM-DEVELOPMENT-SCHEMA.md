---
title: Two-rim development schema (Stage 3)
author: Claude Code session agent, Claude Opus 5.5
date: 2026-09-29
status: Stage 3 contract as repaired (S01-S04, 2026-09-29); exact topology and approximate (float64) placements kept distinct
dg-publish: false
---

# States

| Kind | Representation | Parent | Payload schema |
|---|---|---|---|
| `two_rim.cut` | `exact` | a `two_rim.material` | `two_rim.cut/1` |
| `two_rim.development` | `mixed` (exact IDs and copied material; **float64 maps**) | a `two_rim.cut` | `two_rim.development/1` |
| `two_rim.trimmed_development` | `mixed` (exact trim domain; float64 maps copied unchanged) | a `two_rim.development` | `two_rim.trim/1` |

## `two_rim.cut/1`

```json
{"schema": "two_rim.cut/1", "seam": "E3",
 "face_order": ["F3", "F4", "...", "F2"],
 "retained_hinges": ["E4", "...", "E2"],
 "occurrences": ["F3@B1", "..."],
 "glue_classes": [["F3@B1", "F4@B1"], ["..."]],
 "seam_copies": {"entry": {"face": "F3", "hinge": "E3"}, "exit": {"face": "F2", "hinge": "E3"}},
 "material": {"<exact copy of the parent two_rim.material/1 payload>": "..."}}
```

- **The seam** is one original hinge `E_k`, never a rendering edge.
- **The chain** is `F_k, F_{k+1}, …, F_{k−1}` (indices mod `n`), so the first face's entry and the last face's exit are the two copies of the seam.
- **`retained_hinges`** is every other hinge, in material order.
- **Occurrences** are `face@vertex`, listed in chain order and then boundary order.
- **Glue classes** follow the manuscript's `CutRelated` relation on vertices. For each material vertex, the faces containing it are split into maximal runs of consecutive chain positions, and each run is one class. A seam endpoint therefore has exactly two classes, and every other vertex has one.
- **Classes are ordered** by the material's vertex order (the order of `material.vertices`, not a sort by ID string) and then by chain position. The checker compares this list exactly, order included.
- **Coincident coordinates never glue** anything.

## `two_rim.development/1`

```json
{"schema": "two_rim.development/1", "numeric_domain": "float64",
 "map_convention": "image = linear @ [x, y, z] + offset; linear is 2x3 row-major; x, y, z are the exact material coordinates converted to float64",
 "maps": [{"face": "F3", "linear": [[a, b, c], [d, e, f]], "offset": [u, v]}, "..."],
 "cut": {"<exact copy of the parent two_rim.cut/1 payload>": "..."},
 "generator": {"name": "glab.two_rim.develop", "port_of": "midsection_bridge.py blob cce8c34f", "turns_q": ["..."], "sum_q": "..."}}
```

- There is one **full affine** map per lateral face, in chain order. **Translation is part of the map.**
- The maps follow DRAFT-02 §4 exactly as ported from `midsection_bridge.py`:
  - **Chart:** `ψ_i` has rows `[ν_i, −ξ_i]` and origin `M_i`, the midpoint of hinge `E_i`.
  - **Turn:** `q_i = φ(ν_i) − φ(ν_{i−1})`, where `φ(w)` is the angle between `w` and `G_i`.
  - **Transition:** `T_i(z) = R(q_{i+1}) z + (ℓ_i, 0)`.
  - **Composition:** `W_{k,j+1} = W_{k,j} ∘ T_{k+j}`.
- **The placement is approximate** (float64). The source and material remain exact.
- **What the checker enforces** (v2, repair S02):
  - the exact key set, `schema`, and `numeric_domain` `float64`
  - `map_convention` equal to the one supported string shown above; any other convention is unsupported, never reinterpreted
  - finite, non-bool map numbers of the right shape, one map per face in chain order
  - `cut` is an object
  - `generator` has exactly `name` and `port_of` (strings), `turns_q` (one finite number per face) and `sum_q` (finite)
- **The generator block is shape-checked only.** Its values are never evidence. NaN and infinity cannot enter a record at all, because the core refuses non-JSON output.

## `two_rim.trim/1`

```json
{"schema": "two_rim.trim/1", "delta": "1/10000", "height_parameter": "original normalized height t = z/h",
 "maps": ["<identical copy of the parent development maps>"],
 "trim_points": {"E0@lo": {"hinge": "E0", "t": "1/10000", "xyz": ["x", "y", "z"]}, "E0@hi": {"hinge": "E0", "t": "9999/10000", "xyz": ["..."]}},
 "faces": [{"face": "F0", "boundary": ["E0@lo", "E0@hi", "E1@hi", "E1@lo"]}, "..."]}
```

- `δ` is exact, with `0 < δ < 1/2`.
- On hinge `E_i`, the trim points are `L_i + δ G_i` (tagged `lo`) and `L_i + (1−δ) G_i` (tagged `hi`), computed exactly (§3.2).
- Each trimmed face is the quadrilateral on its entry and exit hinges. By (3.5), both of its runs are positive.
- **Maps are identical** to the parent's: no rescaling and no trim time.
- A trim of a trim is refused.
- **What the checker enforces** (v2, repair S02):
  - the exact key set and `schema`
  - `delta` is a canonical exact string
  - `height_parameter` equals `original normalized height t = z/h`; any other meaning is unsupported
  - every trim point is an object with exactly `hinge` (a string), `t` (a canonical exact string), and `xyz` (**exactly three canonical exact strings**)
  - canonical means `n` or `n/d` in lowest terms; bools, ints, floats, padded strings and spellings like `2/4` fail
  - faces are the material faces in material order, and maps are shaped as for the development
- **A canonically spelled wrong value** is a valid record that fails `domain_is_exact_band`.

# Actions (`glab/two_rim/dev_actions.py`, revision `DEV_REVISION`)

| Name, version | Accepts | Parameters | Produces |
|---|---|---|---|
| `two_rim.cut.open` v1 | `two_rim.material` | `seam`: `Param.str()` | `two_rim.cut` |
| `two_rim.develop.static` v1 | `two_rim.cut` | none | `two_rim.development` |
| `two_rim.trim.apply` v1 | `two_rim.development` | `delta`: `Param.exact()` | `two_rim.trimmed_development` |

- An unknown seam, or a `δ` outside `(0, 1/2)`, is a **failed** attempt with `DevelopmentInputError`.
- The wrong input kind is **rejected** by the registry.

# Checkers (`glab/check/two_rim_development.py`, contextual, NumPy)

All checkers read their ancestors only through `DependencyContext`, and never import `glab.two_rim`.

| Checker | Claims (method) |
|---|---|
| `two_rim.check.cut` **v1** (claim contract unchanged by the repair) | `two_rim.cut.record_schema`, `two_rim.cut.material_copy_matches_parent`, `two_rim.cut.exactly_one_original_seam_open`, `two_rim.cut.face_coverage_complete_unique`, `two_rim.cut.glue_classes_match_cut_relation`. All are exact and are reconstructed from the parent material. |
| `two_rim.check.development` **v2** | Exact: `two_rim.development.record_schema`, `two_rim.development.cut_copy_matches_parent`. Numerical diagnostics: `…face_maps_rigid`, `…no_reflected_face`, `…nonempty_face_images`, `…retained_hinges_and_glued_vertices_agree`, `…face_interiors_disjoint_all_pairs`. |
| `two_rim.check.trimmed_development` **v2** | Exact: `two_rim.trim.record_schema`, `two_rim.trim.maps_identical_to_parent`, `two_rim.trim.domain_is_exact_band`. Numerical diagnostics: the same five numerical claims on the trimmed domain. |

**Why v2.** The development and trimmed checkers' claim contracts changed in the repair:
- stricter record schemas (S02)
- the holonomy receipt fields (S03)
- `Claim.tolerances` populated (S04)

v1 is not registered, so v1 evidence validates as `checker_mismatch`.

- **Unsupported records.** When a record schema fails, every dependent claim is `unknown`.
- **Coverage.** The all-pairs claim uses coverage `all` and records every pair's classification in its receipt.
- **Diagnostics, not safety obligations:**
  - `…diagnostic.unglued_pairs_disjoint` (numerical; coverage `pairs_without_glued_material`)
  - `…diagnostic.float_representability` (exact)
  - `…diagnostic.circuit_holonomy` (numerical; repair S03)
- **No claim uses `rigorous_enclosure`.**
- **Pair policy:** see `STAGE-3-PLAN.md`, "Numerical overlap policy".

## Circuit holonomy receipt (v2)

- **`principal_rotation`** is the angle in (−π, π] between the two seam-copy images, with its `principal_rotation_sign`.
- **`lifted_total_turn`** is the checker's own reconstruction: the sum over chain faces of the principal angle from the entry-hinge image to the exit-hinge image, within that face's image.
  - **`lift_decided`** is true only if every increment satisfies |increment| ≤ π − 1e-9 (`min_branch_margin`).
  - **`lifted_total_turn_sign`** is `unknown` unless the lift is decided and |lift| > 1e-9.
- **`rotations_agree_mod_2pi`** compares the lift and the principal rotation by wrapped difference, never by absolute value.
- **`generator_sum_q`** is attributed to the generator, and **`generator_agrees_with_checker_lift`** reports the comparison. The generator's value is never used as evidence.
- **Outcome:**

  | Outcome | When |
  |---|---|
  | `pass` | the lift is decided, agrees with the principal rotation mod 2π, and agrees with the generator's value when that value is available |
  | `fail` | a decided lift disagrees with either one |
  | `unknown` | the lift is undecided |
- **Removed v1 fields:** `defect_sign` and `abs_values_agree`. They conflated the principal rotation with the lifted sum.
- The receipt also reports `translation_norm` and `pole_condition_1_over_2sin_half_rotation`, which comes from the principal rotation.

## Tolerance policy (`NUMERICAL_TOLERANCE_POLICY`, repair S04)

Every numerical claim and numerical diagnostic declares the same instance-independent policy in `Claim.tolerances` (`"policy": "two_rim.development.numerical/1"`). Its `status` says it is a heuristic tolerance, not a rigorous error bound.

| Part | Units | Value | Used for |
|---|---|---|---|
| `scale_rule` | | max(1, largest absolute float64 coordinate among material points and images) | all length and area thresholds |
| `length_tolerance` | length | τ = 1e-9 × scale | glued-point agreement, SAT separation depth |
| `rigidity_threshold` | dimensionless | 1e-8 | relative squared-distance error, Gram deviation |
| `area_threshold` | area | τ × scale | nonempty images |
| `angle_threshold` | radian | 1e-9 | holonomy branch margin, sign, and agreement mod 2π |

- Effective values (`scale`, `tau`, thresholds) stay in each receipt.
- Exact claims keep `tolerances: null`.
- `Run.validate(..., expected_tolerances=...)` and `Run.summarize(..., expected_tolerances=...)` report `policy_mismatch` or a non-pass result for any other policy.

# Enumerated search totals (`glab/two_rim/search.py`, repair S01)

The search runs every checker through the Run and reports two kinds of total per seam. Each requirement is on its own subject hash with coverage `all`.

| Total | Scope | Requirements |
|---|---|---|
| `full_obligations` | local | cut claims (cut) + all development claims (development) |
| `trimmed_obligations` | local | cut claims (cut) + development `record_schema` and `cut_copy_matches_parent` (development) + all trim claims (trimmed) |
| `source_linked_full_obligations` | source-linked | all source claims (source) + all material claims, including `matches_parent_source` (material) + the local full total |
| `source_linked_trimmed_obligations` | source-linked | all source claims + all material claims + the local trimmed total |

- **Prerequisites.** `two_rim.check.source` v2 and `two_rim.check.material` v2 run once per search on the material's actual parent source and on the material.
  - An unregistered checker leaves a rejected attempt in the history and no evidence, so the total is `not_run`.
  - A material without a `two_rim.source` parent gives `not_run` for both source-linked totals.
- **The trimmed totals never include the full development's numerical verdicts.** A trim is a smaller domain and may remove an overlap.
- **Changed in the repair:** the local trimmed total now includes the development's exact record and copy claims, which it previously omitted.
- **Optional policy.** `expected_numerical_tolerances=` holds numerical requirements to a stated policy, and exact requirements to `None`.
- **The report** includes `prerequisites` and `aggregate_definitions` (the scope and claim list of each total).
- **Checker versions.** The search runs cut v1 and development/trimmed v2.
- **Duplicated names.** The search duplicates the claim names so that it never imports a checker. Tests pin the duplicates to the checkers' own lists.
