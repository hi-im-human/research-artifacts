---
title: Geometry Lab engine - Stage 3 return (static development)
status: Stage 3 complete and stopped before Stage 4; numerical diagnostics only
dg-publish: false
---

# Stage 3 return: static development

**From:** Claude Code session (Claude Opus 5.5), outside the project's agent team. I am the implementer of everything below, not an independent reviewer of it.
**Assignment:** `<geometry-lab-project>/SYSTEM-TO-CLAUDE-STAGE-3.md` on `origin/main` (commit-43), relayed by Summer Bee.

## Where it is

- **Repository:** `<private-repo>`
- **Branch:** `<private-branch>` (worktree `<geometry-lab-worktree>`)
- **Base:** `commit-42` (Stage 2 repair return)
- **Commits:**
  - `commit-44`: plan, development schema, pinned NumPy extra (design before code)
  - `commit-45`: tests first, pinned historical copies, red run
  - `commit-46`: implementation, eleven-panel mapping, provenance, receipts, demo, view
  - the commit that adds this file
- **Scope:** `git diff --name-only commit-42 HEAD` lists only paths under `<engine>/`.
- **Unchanged:** the core (`glab/core`), the Stage 2 generator and checker files, every earlier return, every earlier receipt directory, the review cases, the assessment and prototype, the manuscript, and the frozen proof. No core change was needed.

## What was built

| Piece | Module | Kind of result |
|---|---|---|
| Cut topology | `glab/two_rim/cut.py` (`two_rim.cut.open` v1) | exact |
| Static full-affine development | `glab/two_rim/develop.py` (`two_rim.develop.static` v1) | float64 maps |
| Positive trim, same maps | `glab/two_rim/trim.py` (`two_rim.trim.apply` v1) | exact trim domain, parent maps copied unchanged |
| Independent checker | `glab/check/two_rim_development.py` (three contextual checkers, v1) | exact structure claims, numerical geometry claims |
| Enumerated original-seam search | `glab/two_rim/search.py` | per-seam claims and obligations |
| Save, load, replay | core `glab.run/2`, unchanged | reproduced 100/100 entries with the digest |
| Static inspection | `glab/two_rim/view_export.py`, `glab/view/static.py` | SVG plus band and planar OBJ from a saved run |

Contracts:
- [STAGE-3-PLAN.md](STAGE-3-PLAN.md)
- [TWO-RIM-DEVELOPMENT-SCHEMA.md](TWO-RIM-DEVELOPMENT-SCHEMA.md)
- [PROVENANCE-STAGE-3.json](PROVENANCE-STAGE-3.json)
- [ELEVEN-PANEL-MAPPING.md](ELEVEN-PANEL-MAPPING.md)

The checker imports only NumPy, the standard library, and the core; a boundary test enforces this. The generator imports only the standard library, the core, and its sibling modules, and never imports NumPy or the historical bridge.

**Why states embed ancestor copies.** Action callbacks see only their input state, and giving actions a dependency context would be a core change. So each downstream state carries an exact copy of the ancestor data it needs:
- a cut carries its material
- a development carries its cut
- a trim carries its parent's maps

The checker compares every copy with the real ancestor through the read-only `DependencyContext`, and those comparisons are required obligations.

## Tests: red, then green

| Run | Result | Receipt |
|---|---|---|
| Tests-first at `commit-45`, before implementation | 288 passed, 6 collection errors (the new modules did not exist) | `receipts/stage3/red-at-commit-42.log` |
| First run after implementation | 61 passed, 1 failed (a boundary test flagged a docstring mention of the bridge) | `receipts/stage3/first-run-after-implementation.log` |
| Final, whole suite | **351 passed**: 175 core, 113 two_rim, 63 two_rim_dev | `receipts/stage3/final-all-tests.log` |

Test edits made after the tests-first commit (all visible in `git diff commit-45 commit-46 -- tests`):
- `test_view_and_boundaries.py`: the bridge check now looks for real calls and imports (`PhysicalBridge(`, `import midsection`) instead of any mention.
- `test_view_and_boundaries.py`: a new test pins the search's duplicated obligation names to the checker's claim names.
- `test_eleven_panel.py`: NumPy's deprecated 2D `np.cross` was replaced with a scalar cross product. The assertion is unchanged.
- Three Stage 2 tests were re-scoped on purpose, with comments in the files:
  - `tests/two_rim/test_boundaries.py` allows the new sibling modules, and allows NumPy only in `check/two_rim_development.py`.
  - `tests/two_rim/test_material.py`: the no-float test now covers only the exact Stage 2 files.

Review cases rerun at `commit-46`, unchanged from the Stage 2 repair return:

| Directory | Result | Reason |
|---|---|---|
| `review-cases/stage1-review` | 9 passed, 1 failed | R05 reads the v1 key `actions` |
| `review-cases/stage1-repair-review` | 2 passed | |
| `review-cases/stage2-review` | 13 failed | v1 checker lookup, as recorded before |

## Golden comparison with the historical bridge

`receipts/stage3/development-golden.json` compares every seam of every case against the pinned, byte-verified `midsection_bridge.py` (blob `cce8c34f`). The bridge runs only in tests.

| Group | Cases | Seams | Max linear deviation | Max offset deviation |
|---|---|---|---|---|
| 4 fixtures plus eleven-panel | 5 | 37 | 4.4e-16 | 8.5e-14 |
| Stage 2 seeded random (seed 20260928) | 200 | 1622 | 5.6e-16 | 7.1e-14 |
| Stage 2 supplementary shared-normal | 50 | 234 | 3.3e-16 | 5.7e-14 |

This shows the port matches the historical floating diagnostic. It does not show correctness, and it is not a proof.

## Eleven-panel regression

**Mapping.** The mapping was built from exact coordinates, with no label assumptions (`ELEVEN-PANEL-MAPPING.md`; `tests/two_rim_dev/eleven_panel.py`):
- Historical hinge t is current hinge E{(t+3) mod 11}, and the same holds for faces.
- Historical cut k opens hinge k.
- The mapping is checked as a bijection and a rotation.
- The mapping code is test-side, and the checker never sees historical labels (tested).

**Result** at δ = 1/10000 on the trimmed development:

| Historical cut | Current seam | Historical exact class | Current all-pairs | Comparison |
|---|---|---|---|---|
| 0 | E3 | unsafe | fail | agree: overlap F3/F2, area 4.25 |
| 1 | E4 | safe | unknown | not contradicted |
| 2 | E5 | safe | unknown | not contradicted |
| 3 | E6 | safe | unknown | not contradicted |
| 4 | E7 | safe | unknown | not contradicted |
| 5 | E8 | unsafe | fail | agree: F8/F7 7.05, F9/F7 0.92, F10/F7 1.69 |
| 6 | E9 | unsafe | fail | agree: F9/F7 0.92, F9/F8 18.98, **F10/F7 1.69**, F10/F8 9.49 |
| 7 | E10 | unsafe | fail | agree: F10/F7 1.69, F10/F8 9.49, F10/F9 38.49 |
| 8 | E0 | safe | unknown | not contradicted |
| 9 | E1 | safe | unknown | not contradicted |
| 10 | E2 | safe | unknown | not contradicted |

- **No disagreements.** All four historically unsafe cuts fail with a numerical interior overlap.
- **Historical cut 6.** Historical panel positions 1 and 9 (faces F7 and F4) map to current F10 and F7. That is one of the pairs our checker flags.
- **Witness point.** The historical rational point (39037647/1000000, 565877/1000000) lies strictly inside both mapped faces' float images; this is a numerical test.
- **Safe cuts.** Every unglued pair passes, and every unresolved pair is a retained-hinge neighbor pair. Shared glued material never upgrades a pair to pass, so these seams stay `unknown`.
- **Margins.** The opposite-sides margin at each retained hinge is at least about 1e-4, roughly 1000 × τ. This is recorded as information only.

Receipts: `receipts/stage3/demo/eleven-panel-comparison.json`, `search-E11.json`.

**F2 search** (δ = 1/4): all 5 seams give trimmed all-pairs `unknown` and unglued pairs `pass`. The full untrimmed developments are also `unknown`. Receipt: `search-F2.json`.

## Save, replay, and the inspection view

- **Demo:** `examples/two_rim_development_demo.py`. It produced byte-identical output over two runs, and a third run after the final test edit was also identical.
- **Run digest:** `sha256:6120b3e0ca22315996dcfab7e49718302bf4828070eb239e2ed3208dc9c97d92`
- **Load:** `internally_consistent`, anchor `matched`, `authenticated: false`.
- **Replay:** `reproduced`, 100/100 entries, digest reproduced, environment matched.
- **Manifest:** `receipts/stage3/demo/MANIFEST.json` lists 10 files. After commit, all 10 committed blobs hash to the manifest values.
- **Inspection view:** `receipts/stage3/demo/E11-cut6-trimmed.svg`, with `-band.obj` and `-planar.obj`. It shows historical cut 6 (current seam E9) on the trimmed development:
  - the band, with the seam in red
  - the planar candidate, with both seam copies in red and failing faces outlined
  - a zoom of the failing faces, the evidence list, and the non-passing pairs

  It is rendered only from the saved run through `view_export.view_data`. It is static; there is no interactive viewer.

## What kind of result each thing is

**Exact** (method `exact_computation`):
- All five cut claims.
- Development and trim record schemas.
- Every ancestor-copy comparison.
- `two_rim.trim.maps_identical_to_parent` (equal float values).
- `two_rim.trim.domain_is_exact_band` (rational arithmetic).
- `diagnostic.float_representability`, which reports that the eleven-panel source is not exactly representable in float64 (for example, 1693/100).
- The mapping between historical and current IDs.

**Numerical** (method `numerical_diagnostic`, float64 with τ = 1e-9 × scale, which is a heuristic tolerance and not an error bound):
- rigidity, no reflection, nonempty images, retained-hinge and glued-vertex agreement
- the all-pairs disjointness claim and its unglued-pairs diagnostic
- the circuit holonomy sign
- every overlap area above
- the witness-point test

A `pass` or `fail` from the separating-axis test is decided with a margin beyond τ, or by an exact rational test on the float images. That exact test is exact for the float images only, not for the exact source, and the receipt says so (`exactness_scope`).

**Unknown:**
- Every historically safe eleven-panel seam, and every F2 seam, on all-pairs disjointness. The cause is retained-neighbor near-contact within τ.
- The unglued diagnostic on the untrimmed full developments of eleven-panel seams E0 and E1: pairs F0/F10 and F1/F10, and F1/F10 and F1/F0. The trimmed developments pass.

**Not run:**
- interval or enclosure arithmetic
- continuous motion
- proof-guided seam selection
- cap unfolding
- Lean, CGAL, or FOLD
- an interactive viewer

No claim uses `rigorous_enclosure`; a test checks this.

**Historically certified elsewhere, not by this engine:**
- The exact safe/unsafe classes of the eleven cuts.
- The exact cut-6 overlap witness.

These come from the Codex Forge review certificate at `commit-11` (blobs `c5714692`, `2471d2d1`). The verifier is stored as a `.txt` file and never executed.

## Limitations and disclosures

1. **Safe seams stay `unknown`.** Separating a retained-hinge neighbor pair needs more than float64 and a tolerance. Deciding it is Stage 4 work.
2. **State copies.** States embed ancestor copies because actions have no context (see above). The records are larger, and the copies are checked.
3. **Duplicated claim names.** The search duplicates the checker's claim names so that it never imports the checker. A test pins the two lists together.
4. **Demo depends on test support.** The demo and the golden receipt writer import the test-side support modules (`tests.two_rim_dev.eleven_panel` and `bridge_support`) for the mapping and the historical comparison.
5. **Schema wording fixed.** The schema previously said glue classes are sorted by vertex ID. The code, and now the schema, use material vertex order, then chain position.
6. **Replay is environment-bound.** Replay is `reproduced` only with the same revisions and NumPy 2.4.4 (`receipts/stage3/environment.json`).
7. **The source is not float-exact.** The eleven-panel source is not float-representable, so every placement of it is an approximation of the exact source.
8. **One overlap rule was removed in design.** My draft rule that would have passed a pair on its opposite-sides margin was removed before implementation, because it would have passed the required "tiny overlap near glued material gives unknown" control. The plan records this.

## Needs a decision from System

- Whether the ancestor-copy design is acceptable for later stages, or whether actions should get a read-only context. That would be a core change, and it has not been made.
- Whether the demo may keep importing test-side support for the historical comparison, or whether that should move.
- The scope of Stage 4, since the safe-seam `unknown` results are exactly what it would need to settle.

## Not started or not authorized

- Stage 4 and everything the handoff excluded: interval/enclosure work, continuous motion, proof-guided seam selection, cap unfolding, Lean/CGAL/FOLD integration, an interactive viewer.
- No merge, PR, release, deployment, external contact, or additional agents.
- The branch is pushed as a work branch only.
