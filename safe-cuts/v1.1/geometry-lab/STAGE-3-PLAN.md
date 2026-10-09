---
title: Geometry Lab Stage 3 plan (static development)
author: Claude Code session agent, Claude Opus 5.5
date: 2026-09-29
status: in-scope plan for SYSTEM-TO-CLAUDE-STAGE-3.md; Stage 4 not authorized
dg-publish: false
---

# Inputs read

| Item | Pin |
|---|---|
| `SYSTEM-TO-CLAUDE-STAGE-3.md` | `commit-43`, blob `a3167797`, read from `origin/main` without merging |
| `reviews/stage2-repair-commit-42/REVIEW.md` and `RESULTS.json` | blobs `292dc83c` and `3c1902f2` |
| Reviewed worker head | `commit-42`. The branch had not moved, and the worktree was clean. |
| Historical formulas | `<historical-folder>/code/midsection_bridge.py`, blob `cce8c34f` |
| Historical exact eleven-panel review, at `commit-11` | `<historical-folder>/review/beveled_source_certificate.py` (blob `2471d2d1`) and `.json` (blob `c5714692`), which use `mixed_fixture_certificate.iv_unfold` |

# Pipeline and boundaries

The Stage 3 pipeline is:

> material (Stage 2, exact) → **cut** (exact topology) → **static development** (float64 full affine maps) → **trim** (exact domain, same stored maps) → independent checks → enumerated seam search → saved and replayed run → static SVG and OBJ

**Out of scope:** motion, a proof-guided selector, caps, intervals or enclosures, Lean, CGAL, FOLD, Polyscope, COMPAS, Trimesh, an interactive viewer, and arbitrary polyhedra.

**No core change.** Action callbacks receive only their input state, and giving actions a context would widen the core. So each downstream state carries an **exact copy** of the ancestor data its generator needs:
- the cut state holds the material payload;
- the development state holds the cut payload.

The development checker verifies those copies against the real ancestors through the existing `DependencyContext`. The generator never re-hulls the source; it reads the stored Stage 2 material.

# Modules (all under `engine/`)

| Path | Role |
|---|---|
| `glab/two_rim/cut.py` | exact cut topology (standard library only) |
| `glab/two_rim/develop.py` | float64 port of the `midsection_bridge` chart, turn, and transition formulas, using `math` only (no NumPy, no `PhysicalBridge` import) |
| `glab/two_rim/trim.py` | exact trim domain; copies the parent maps unchanged |
| `glab/two_rim/dev_actions.py` | `two_rim.cut.open` v1, `two_rim.develop.static` v1, and `two_rim.trim.apply` v1, with their own revision. Stage 2's `actions.py` is untouched, so its revision stays stable. |
| `glab/two_rim/search.py` | `enumerated_candidate_search` driver (search, not the manuscript's selector) |
| `glab/two_rim/view_export.py` | writes view data (face images) from a saved run's states |
| `glab/view/static.py` | standard-library renderer from view JSON to SVG and polygon OBJ. It does no geometry. |
| `glab/check/two_rim_development.py` | independent checkers `two_rim.check.cut` v1, `two_rim.check.development` v1, and `two_rim.check.trimmed_development` v1. These are contextual, use NumPy, and never import `glab.two_rim`. |
| `tests/two_rim_dev/` | new tests; `pinned_bridge/` holds byte-verified historical copies for golden tests only |
| `TWO-RIM-DEVELOPMENT-SCHEMA.md`, `PROVENANCE-STAGE-3.json`, `ELEVEN-PANEL-MAPPING.md` | the development schema, provenance, and the mapping artifact |

**Dependency:** `numpy==2.4.4`, pinned. It is used only by the development checker, and is installed in `engine/.venv` as the optional extra `numeric`.

# Numerical overlap policy

For every pair of active face images, with **no adjacency skip**, the checker computes the separating-axis depth `d` and a tolerance `τ = 1e-9 × scale`:

| Case | Outcome |
|---|---|
| `d < −τ` | `pass` (separated) |
| `d > τ` | `fail` (interior overlap) |
| `|d| ≤ τ`, and the exact separating-axis test on the **represented rational values of the float images** finds an axis with overlap ≤ 0 | `pass`. The receipt says this exactness concerns only those represented coordinates. |
| otherwise | **`unknown`** |

**Glued material does not make a pass easier.** A pair that shares a retained hinge or a glued vertex follows the same rule. For such a pair, the receipt records the opposite-sides margin (for a hinge) or the tangent-cone gap (for a vertex) **as information only**. It does not upgrade the outcome; resolving such pairs is Stage 4 enclosure work.

*Design note.* My first draft counted that margin as a pass. I removed it before implementing, because in floating point it cannot be told apart from the handoff's required control, where a tiny overlap near glued material must be `unknown`. As a consequence, a seam whose retained-adjacent contacts leave a rounding sliver will usually get an **`unknown`** all-pairs claim in Stage 3.

**Separate partial-coverage diagnostic:** `…diagnostic.unglued_pairs_disjoint`, with coverage `pairs_without_glued_material`. It applies the same rule only to pairs that share no glued material, including the two seam-copy faces. It can never satisfy a coverage-`all` requirement. No claim uses `rigorous_enclosure`.

# Eleven-panel regression

1. Normalize the historical exact source.
2. Build the material.
3. **Map by exact coordinates.** Historical hinge `t` (its `original_hinges[t]` in the certificate) maps to the current hinge with equal lower and upper coordinates. Historical face `f`, between hinges `f` and `f+1`, maps to the current face whose entry is `map(f)`. Historical cut `k` maps to seam `map(k)`, and panel position `s` in cut `k` maps to face `map((k+s) mod n)`.
4. Write the mapping artifact, then enumerate all current seams at `δ = 1/10000`.
5. Compare the mapped classifications against the historical exact ones.

Historical labels never enter the checker, and a disagreement is recorded, not patched.

# Tests (written first), and verification

- **Cut:** topology, seam copies, and fan vertices; extra cut and welded seam detected.
- **Development:** golden comparison against the pinned bridge on the fixtures; rigidity and hinge agreement. Mutations: omitted translation, damaged transform, reflected face, omitted face, stacked non-adjacent faces, stale evidence.
- **Trim:** same maps, exact domain, invalid δ, trim of a trim refused.
- **Overlap policy:** unit controls, including adjacent contact exercised, tiny non-glued overlap giving `unknown`, and tiny overlap near glued material giving `unknown`.
- **Eleven-panel:** mapping and classification comparison, with at least one natural `fail`, and cut 6 not passing.
- **View:** exports consume saved data; import boundaries.
- **Runs:** the inherited suites, and the demo twice. Then write receipts, verify the diff, write `STAGE-3-RETURN.md`, push, and stop.
