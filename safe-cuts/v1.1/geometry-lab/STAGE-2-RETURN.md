---
title: Geometry Lab Stage 2 return (C01 + exact source-geometry port)
from: Claude Code session agent (no persona name); Claude Opus 5.5 (claude-opus-5-5); Claude desktop app, Windows 11
to: System / Summer Bee
date: 2026-09-28
status: C01 fixed; Stage 2 source geometry complete; stopped before Stage 3
dg-publish: false
---

# Result

**C01 is fixed.** Then Stage 2 was built:

> two rational rims + positive rational height → recorded normalization (`two_rim.source`) → original maximal facets, hinges, rim edges, and caps (`two_rim.material`) → independent exact checks → saved and replayed run

| Evidence | Result |
|---|---|
| Full suite (`receipts/stage2/final-all-tests.log`) | **234 passed**: 166 core and 68 two-rim |
| The 4 assessment fixtures and **200 seeded random valid rim pairs**, against the pinned originals | **All match**: hull vertices, hinge coordinate pairs, normal rays, and facets |
| The same cases, against the independent exact oracle | **All pass**, with full coverage (no subset) |
| 50 supplementary shared-normal cases | All pass both checks |

A golden match shows only consistency with the original implementation. The oracle and the targeted controls are separate evidence.

# Branch, base, head, scope

| Item | Value |
|---|---|
| Handoff read | `SYSTEM-TO-CLAUDE-STAGE-2.md`, `commit-31`, blob `7c6b33cc`. C01 review blobs: `REVIEW.md` `e03fba5c`, `RESULTS.json` `e8437123`, `test_rejection_order.py` `7c088430`. All read from `origin/main`; main was not merged. |
| Base | the reviewed head `commit-30`. The branch had not moved, and the worktree was clean. |
| Commits | `commit-32` (C01), `commit-33` (plan, schema note, `Param.list`), `commit-34` (source normalization), `commit-35` (material, checker, golden), `commit-36` (actions, recorded execution, demo). This return is the next commit. |
| Scope | The diff from `commit-30` lies inside `<engine>/`. Only two existing files are **modified**: `glab/core/registry.py` (C01 and `Param.list`) and `README.md`. Everything else is **added**. The assessment, earlier returns and receipts, reviews on main, the manuscript, and the frozen proof are unchanged. |

# C01

- **Red at `commit-30`** (`receipts/c01/red-at-commit-30.log`): 6 failed, 146 passed.
  - Both of System's cases failed.
  - Four of my controls failed: both invalid-key insertion orders, identical digests, and order-independence.
  - The reversed-order controls, whose insertion order is already canonical, passed.
- **Fix:** `validate_params` walks unexpected keys in sorted (canonical) order. This is a one-line, local change. Failure messages and the digest boundary are unchanged.
- **Green:** 152 passed. System's file, run verbatim, passes 2 of 2 (`receipts/c01/review-verbatim.log`).

# The one authorized core addition: `Param.list(item)`

- It accepts only a JSON `list` (not a tuple) and validates every element recursively.
- The failure path is stable and indexed, for example `'top[1][1]'`.
- Declaring it with a non-`Param` item is refused.
- Tests (`tests/core/test_param_list.py`) cover malformed rows, non-lists, floats, bools, NaN, zero denominators, over-nesting, recursive `describe`, and replay of a rejected list attempt, which reproduces.
- No other core semantics changed.

# What Stage 2 built

The full contract is in `TWO-RIM-SCHEMA.md`, and the plan in `STAGE-2-PLAN.md`.

**Source normalization (`glab/two_rim/source.py`).**
- Every point must have exactly two exact coordinates; height must be positive.
- `input_kind` is `cyclic_boundary` or `point_set_hull`.
- **Cyclic input** must already be strictly convex and simple, and it is **never repaired**. The code rejects duplicates, collinear turns, reflex turns, bowties, and doubly wound stars. It normalizes to clockwise order starting at the lexicographic minimum, and records orientation, reversal, and start index.
- **Point-set hull** is an explicit operation using the ported `hull2`. Every removed input point is recorded with its index and a reason: `duplicate`, `boundary_non_vertex`, or `interior`.

**Material (`glab/two_rim/material.py`).**
- It uses the ported `splice_cycles` and has stable IDs: `A{i}`/`B{j}` vertices, `RA`/`RB` rim edges, `E{t}` hinges, `F{t}` faces between `E_t` and `E_{t+1}` (the manuscript's convention), and `C_TOP`/`C_BOTTOM` caps.
- Each face has a ring starting at its entry hinge's lower vertex, with aligned boundary edges.
- A face is a triangle exactly when one rim run vanishes, and a trapezoid otherwise.
- Planes are primitive integers from Proposition 3.1.
- Caps are source faces only.
- `identity` is the content hash of the material fields, excluding the parent and the presentation.
- Units, the coordinate convention, and the number domain are part of identity.
- **Nothing uses floats or angles.** A test searches both packages for `float(`, `math`, `atan`, `sqrt`, and `numpy`.

**Independent checker (`glab/check/two_rim_source.py`).** It imports only `glab.core` and the standard library. Its claims:

| Checker | Claims |
|---|---|
| `two_rim.check.source` | height positive; rims strictly convex and clockwise; normalization accounts for input. For a hull input, that means brute-force extreme points and an independent classification of every removed point. |
| `two_rim.check.material` | the identity hash; facets match a brute-force exact supporting-plane oracle, covering every lateral facet, both caps, and plane coefficients; incidence and rings (the hinge chain, shared vertex pairs, ring convexity with uniform orientation, each rim edge on exactly one face and one cap) |

Every claim uses `exact_computation`, `exact_rational`, and coverage `all`. Evidence on a material depends on `[material, source]`.

Mutations it catches (tests):
- a moved vertex
- a dropped face
- swapped hinge endpoints
- a stale identity
- a diagonal split of a trapezoid
- **merging the two nearly coplanar 10⁻²⁰ triangles**
- a non-convex normalized rim
- a moved normalized vertex
- a zero height
- a missing or misclassified removed hull point

**Registered execution (`glab/two_rim/actions.py`).**
- `two_rim.source.normalize` v1 takes `top`/`bottom` as `Param.list(Param.list(Param.exact()))`, `height` as exact, and `input_kind` as an enum.
- `two_rim.material.build` v1 accepts only `two_rim.source`.
- A domain violation, such as a 3-coordinate point or a reflex ring, is a **failed** attempt with `SourceInputError`. A parameter-type violation, such as a float coordinate, is **rejected**. Both are recorded and replay as reproduced.
- Import-boundary tests enforce three rules: the core imports no domain code; `two_rim` imports only the standard library, `core`, and itself; and the checker imports only the standard library and `core`.

# Evidence detail

**Tests by file:**

| File | Tests |
|---|---|
| `test_source` | 26 |
| `test_material` | 11 |
| `test_checker` | 9 |
| `test_golden` | 13 |
| `test_actions` | 6 |
| `test_boundaries` | 3 |
| core suite | 166 (including C01 and `Param.list`) |

**Random family (`receipts/stage2/random-200.json`, SHA-256 `4dfe7bd5448bccf31da7ab591ffec86a64ac5a908f6e93e764dcb9587f9854ea`, regenerated byte-identically):**
- **Generator:** seed `20260928`. Each rim has 3 to 8 points with coordinates `p/q`, `|p| ≤ 60`, and `q ∈ {1,2,3,5,7}`. Heights are `p/q` with `p` from 1 to 40 and `q ∈ {1,2,3,7,10,1000}`. Input kinds split 100/100.
- **Results:** 200 attempts, 200 valid, **0 rejected**. The face count ranges from 6 to 12, and every case needed a nonzero start-index rotation to align with the originals. That is the documented convention difference: the originals start at `reversed(hull2)`, and we start at the lexicographic minimum.
- **Limit, disclosed:** random rims almost never share a normal direction or contain collinear points. So the random family contained **no trapezoids and no rejections**. Those are covered by the fixtures, by the direct controls in `test_source` and `test_material`, and by a **supplementary family** (seed `20260929`) that is not counted toward the 200. In that family, 50 bottom rims are homotheties of their tops (25 all-trapezoid cases), half with an extra point added. All 50 match the originals and pass the oracle.

**Direct controls** (tests):
- shared edge normals, giving all trapezoids
- a normal on only one rim, the hypotenuse `(1,1)`, giving triangles
- opposite normals `(0,−1)` and `(0,1)`, which are not merged
- repeated and collinear points: rejected in cyclic mode, recorded with reasons in hull mode
- a multi-face rim vertex (3 or more faces)
- a tiny height of `1/10^30`
- the **10⁻²⁰ perturbation**, kept as an exact string in source and material. It gives 5 facets including 2 triangles, even though `float()` of that coordinate equals 3.0.

**Demo (`examples/two_rim_demo.py`, run twice, byte-identical):**
- The run covers F2, F2 reversed and rotated, F3 (the 10⁻²⁰ perturbation), and the pinned hull fixture X, plus one failed and one rejected attempt.
- F2 and its reversed form have **the same material identity** but different states.
- Load is anchored and `matched`. Replay is `reproduced` for 18 of 18 entries, with the full digest reproduced.
- The 24 required claims give `pass` as loaded, with verified `false`. After replay they give `pass`, verified `true`.
- Run digest: `sha256:dfd846ded961098ac28f9b4c08a43bdc2d28b9e32ea977f260f9bfc59771add3`. All output hashes are in `receipts/stage2/demo/MANIFEST.json`.

**Environment:** Windows 11, CPython 3.11.9, pytest 9.1.1 in the local `.venv`. The core, two-rim, and checker revisions are in `receipts/stage2/environment.json`. Replay is environment-bound.

# Disagreements found

- **Port versus the pinned originals:** none. Every fixture and all 250 random or supplementary cases agree on hull vertices, hinge coordinate pairs, normal rays, and facets, allowing only the documented start-index rotation.
- **Independent checker versus generator:** one disagreement, found and fixed. On a triangle whose bottom run vanishes, the checker's wrap-around de-duplication rotated the ring. The generator starts at `L_t` and drops the second copy.
  - Classification: an **ambiguity in our own schema**, surfacing as a checker bug. It is not a port defect and not an issue in the original source.
  - The schema now states the rule explicitly (`TWO-RIM-SCHEMA.md`). The first-run log is `receipts/stage2/task3-checker-first-run.log`.
- **Paper, Lean, or original sources:** no issues found, and nothing was edited.

# What is exact, and what was not attempted

- **Exact** for the represented rational inputs: normalization, hull provenance, hinge pairs, rays, facets, planes, incidence, and identity. No universal claim is made, and the paper's real-input theorem remains a separate object.
- **Not attempted in this stage:** float placements, developments, the cut quotient, trims, seam search, pole or defect sign, collision checks, cap unfolding, a viewer, CGAL, Lean, and the archived eleven-panel Stage 3 lead.

# Limitations and disclosures

1. **The checker sees only its subject.** The material checker verifies the material against its own coordinates, but cannot independently confirm that those coordinates equal the parent source's normalized rims. Here, that is covered by a domain test (`test_material_vertices_equal_parent_source_rims`) and by construction on replay. **Proposed core addition, not implemented:** give checkers read-only copies of their validated dependency states. It needs System's decision, because it changes core semantics.
2. **Material code came before its tests.** `material.py` was written before `test_material.py` and `test_checker.py`, breaking the test-first order. Its first run passed (`receipts/stage2/task3-material-only-first-run.log`). The checker, golden tests, actions, and source followed the order: tests first, with a red log.
3. **Oracle cost.** The oracle is a brute-force cubic enumeration over vertex triples. It is fine for these bounded cases (the full run takes about 3 seconds) but is not meant for large inputs.
4. **Input-kind rename.** The prototype's `cyclic_convex_polygon` is now `cyclic_boundary`. The fixture copies stay byte-identical, and the mapping is applied in the tests and documented in `PROVENANCE-STAGE-2.json`.
5. **Author provenance.** The original helpers name no author, and their Git commit author field is "Human". That is kept separate from intellectual authorship. The port and checker were written by this agent.

# One recommended next step

Review the material representation in `TWO-RIM-SCHEMA.md`, and decide on limitation 1: whether checkers should get read-only dependency states. Do both before any Stage 3 development depends on the representation. **Stage 3 is not started.**
