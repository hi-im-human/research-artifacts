---
title: Geometry Lab engine - Stage 3 repair return (S01-S04)
status: S01-S04 repaired; stopped; Stage 4 held
dg-publish: false
---

# Stage 3 repair return: S01-S04

**From:** Claude Code session (Claude Opus 5.5), outside the project's agent team. I implemented both Stage 3 and this repair, so I am not an independent reviewer of either.

**Assignment:** System's review `<geometry-lab-project>/reviews/stage3-review/REVIEW.md`, at review `commit-48`. I read it from `origin/main` without merging main, together with `test_stage3_regressions.py`, `RESULTS.json` and `ADAPTER-NOTE.md`.

## Where it is

- **Repository:** `<private-repo>`
- **Branch:** `<private-branch>`
- **Reviewed head:** `commit-47`. There were no worker commits after it, and the worktree was clean at the start.
- **Commits:**
  - `commit-49`: repair plan, verbatim review cases, and their reproduction at `commit-47`
  - `commit-50`: tests first, including the adapted review copy, and the red run
  - `commit-51`: S01-S04 implementation, schema and README updates, repair receipts
  - the commit that adds this file
- **Scope:** `git diff --name-only commit-47 HEAD` lists only paths under `<engine>/`.
- **Unchanged since `commit-47`:**
  - the core
  - the Stage 3 generator (`cut.py`, `develop.py`, `trim.py`, `dev_actions.py`)
  - the Stage 2 generator and checker
  - every earlier return and receipt directory, including `receipts/stage3/`
  - the earlier review cases, `ELEVEN-PANEL-MAPPING.md` and `PROVENANCE-STAGE-3.json`

  `receipts/stage3-repair/environment.json` records that the core, both generator revisions, and the Stage 2 checker revision are unchanged.
- **Not made:** no core change and no action-context change.
- **Review file:** copied verbatim to `review-cases/stage3-review/test_stage3_regressions.py`. Its committed blob is `0ec7cd0114fee65314242182269939cf357937cf`, the same as on `origin/main`.

## Reproduction, red, green

| Run | Result | Receipt |
|---|---|---|
| System's file verbatim at `commit-47`, before any change | **3 passed, 8 failed**, the same as the review | `receipts/stage3-repair/red-review-cases-at-commit-47.log` |
| Tests first at `commit-50` (`--continue-on-collection-errors`) | 329 passed, 59 failed, 3 modules not importable | `receipts/stage3-repair/red-tests-first.log` |
| Final whole suite at `commit-51` | **411 passed**: 175 core, 113 two_rim, 123 two_rim_dev | `receipts/stage3-repair/final-all-tests.log` |
| Adapted review copy | **11 passed** | `receipts/stage3-repair/review-stage3-adapted.log` |
| System's file verbatim at `commit-51` | 2 passed, 9 failed. All 9 fail on the checker-version lookup (6 × development v1, 3 × trimmed v1) and on no geometry assertion. | `receipts/stage3-repair/review-stage3-verbatim.log` |
| Earlier review cases | stage1 9/1 (R05), stage1-repair 2/2, stage2 13 fail on the v1 lookup; all unchanged | `receipts/stage3-repair/earlier-review-cases.log` |

**What the red run did and did not exercise.**
- The S01, S03 and S04 test modules could not import yet, because they import new names. Their assertions were **not** exercised in red.
- Most of the other red failures come only from the v2 checker lookup, which did not exist yet.
- The S02 cases, the adapted S01 and S02 cases, and the view tests did run and fail for substantive reasons.
- The same caveat applies to my Stage 3 red run (288 passed, 6 collection errors): it exercised no numerical assertion in the modules that could not import.

**Test edits after the tests-first commit** (`git diff commit-50 commit-51 -- tests`):
- `test_repair_s02_schema.py`: the NaN `sum_q` case moved into its own test. The core refuses to record a NaN at all (it is not JSON), so there is no development state to check; the new test asserts that refusal.
- `test_repair_s01_aggregates.py`: added pins for `DEVELOPMENT_EXACT_OBLIGATIONS` against the checker's list, and for the search's checker versions against the registry.

Existing Stage 3 tests were changed from checker v1 to v2 in the tests-first commit. The v1 prism holonomy assertion (`unknown`) became a v2 assertion: `pass`, with `lifted_total_turn_sign: unknown`.

## Adapter for System's cases

The adapter is `tests/two_rim_dev/make_review_stage3_adapted.py`. It generates `test_review_stage3_adapted.py` by counted literal substitutions, and regenerating it gives an identical file. The changes:

1. Checker version 1 → 2 for the development and trimmed checkers (8 call sites). The cut checker stays at v1.
2. As `ADAPTER-NOTE.md` directs, `test_S01_trim_summary_keeps_failed_parent_copy_obligation` registers the real Stage 2 v2 checkers. That case's source and material prerequisites then pass, and the development's failed cut copy is what blocks the source-linked pass.
3. S03 reads the renamed field `lifted_total_turn_sign`.

No assertion is removed or weakened. The adapted S03 assertion still accepts `None`, so my own S03 tests assert `negative` strictly.

## S01: source-linked totals (`glab/two_rim/search.py`)

**Two kinds of total per seam:**
- **Local:** `full_obligations`, `trimmed_obligations`
- **Source-linked:** `source_linked_full_obligations`, `source_linked_trimmed_obligations`

The report also carries `prerequisites` and `aggregate_definitions`; the latter gives each total's scope and claim list. The definitions are in `TWO-RIM-DEVELOPMENT-SCHEMA.md`, "Enumerated search totals".

**How the prerequisites are checked:**
- The search runs `two_rim.check.source` v2 on the material's actual parent source, and `two_rim.check.material` v2 on the material, once per search, through the Run.
- It does not infer anything from ancestry hashes or action success.
- An unregistered checker leaves a rejected attempt in the history and no evidence, so the core summary gives `not_run`.
- A material with no source parent gives `not_run`.

**The trimmed totals** now include the development's exact `record_schema` and `cut_copy_matches_parent`. They never include the full development's numerical verdicts.

**The local trimmed total changed meaning.** It now also includes the development's exact claims. This closes the dropped parent-copy failure in the local total as well.

**Tests:**

| Case | Result |
|---|---|
| Positive complete total with the real Stage 2 bundle | pass |
| Missing checkers | source-linked `not_run`; local unaffected |
| Height-3 source with a height-4 material | source-linked `fail`; local `pass`; the intrinsic material claims still pass, so they are not relabeled false |
| Failed development cut copy | local and source-linked trimmed totals both `fail` |
| E11 E9 at δ = 49/100 | full development fails; trimmed domain is `unknown` with unglued pairs passing, so the full failure is not inherited |
| Material without a source parent | `not_run` |
| Duplicated claim names and checker versions | pinned |

**The view** (`geometry-lab.view/3`) takes optional `statuses`. The SVG shows "local chain status" and "source-linked status" separately, or says they were not supplied. On the eleven-panel specimen, local and source-linked totals agree for all 11 seams, because the source correspondence passes.

## S02: schema meaning (`check_development`, `check_trimmed`)

Small explicit validators, `_dev_schema` and `_trim_schema`, with no framework.

**Development:**
- `map_convention` must equal the one supported string
- maps are finite and not bool
- `cut` is an object
- `generator` has exactly `name`, `port_of`, `turns_q` (one finite number per face) and `sum_q` (finite). These are shape checks only; the values are never evidence.

**Trim:**
- `height_parameter` must equal `original normalized height t = z/h`
- every trim point is an object with exactly `hinge` (a string), `t` (a canonical exact string), and `xyz` (exactly three canonical exact strings)
- bools, ints, floats, padded strings and non-lowest-terms spellings fail

An unsupported record gives `record_schema: fail`, and every dependent claim is `unknown`. Valid records are neither repaired nor reinterpreted.

**Tests:**
- 8 development mutations, including the subtracted-offset convention, and 13 trim mutations:
  - all four of System's cases
  - wrong point arity (2 and 4 coordinates)
  - a point that is not an object
  - an extra key
  - float `t` and an int `hinge`
  - non-canonical coordinate and `t` spellings
  - a leading space
  - a bool, a float and an int coordinate
- the NaN refusal
- a control: a canonically spelled but wrong value is a valid record that fails `domain_is_exact_band`
- a positive control on E11, whose trim points include negative fractional coordinates: both schemas pass

## S03: principal rotation and lifted total turn

The new receipt fields are listed in the schema, "Circuit holonomy receipt (v2)". In summary:

- **`principal_rotation`** comes from the seam copies, with its own sign.
- **`lifted_total_turn`** is the **checker's own reconstruction**: the sum over chain faces of the principal angle from each face's entry-hinge image to its exit-hinge image.
  - It is decided only when every increment stays 1e-9 rad away from ±π.
  - Its sign is `unknown` within 1e-9 rad of zero.
- **Comparisons.** The lift and the principal rotation are compared modulo 2π. The generator's `sum_q` is recorded, attributed to the generator, and compared; it is never used as evidence.
- **Removed fields:** `defect_sign` and `abs_values_agree`.

**Validation of the reconstruction:** it matched the generator's `sum_q` within 8e-15 over all 1893 golden seams. This is a probe, not a committed receipt; the tests cover E9, a positive case, and the synthetic cases.

**Results:**

| Case | Principal rotation | Lifted total turn |
|---|---|---|
| E11 E9 (full and trimmed) | +0.0756, positive | −6.2076, negative |
| Seeded random case 32 | negative | > π, positive |
| Translated prism | | sign `unknown`, outcome `pass` |

- **E9 outcome:** `pass`. It agrees with the generator.
- **E11 branch margin:** the smallest per-face margin is 0.038 rad. That is decided, but it shows the branch check matters on flat bands.
- **Synthetic tests:** lifts of +6.0 and −5.0 that cross the branch; an increment at the branch, which is undecided; a generator value off by 2π, which fails; and a principal rotation inconsistent with the lift, which fails.

No sign is chosen to match a fixture, and no proof selector or interval code was added.

## S04: the tolerance policy is in `Claim.tolerances`

**The policy.** `NUMERICAL_TOLERANCE_POLICY` (`two_rim.development.numerical/1`) is a single instance-independent policy, marked "heuristic tolerance, not a rigorous error bound". It separates:

| Part | Units | Value |
|---|---|---|
| Length tolerance | length | τ = 1e-9 × scale |
| Rigidity threshold | dimensionless | 1e-8 |
| Area threshold | area | τ × scale |
| Angle threshold | radian | 1e-9 |

It also includes the scale rule.

**Which claims carry it.** Every numerical claim and numerical diagnostic declares the policy. Exact claims keep `null`. Effective values stay in the receipts. In the demo run: 224 numerical records carry the policy, and 210 exact records carry none.

**Tests:**
- `Run.validate` and `Run.summarize` with the matching policy give `current`/`pass`; a mismatched policy gives `policy_mismatch` and a non-pass result
- exact claims validate against `None`
- the search's optional `expected_numerical_tolerances`
- save, load (`validate_evidence` on the loaded store), and replay

## Eleven-panel comparison, demo, replay

- **Demo:** `examples/two_rim_development_demo.py` writes to `receipts/stage3-repair/demo/`. It needs the full checkout, which the README now says.
- **Determinism:** a second run was byte-identical.
- **Run digest:** `sha256:9692a047eb1080ff284a35e3f928b0f9773a74f200d21c7b5ed957a3eeac47f0`
- **Load and replay:** anchor `matched`; replay `reproduced` with **104/104** entries and the digest. The four entries beyond Stage 3's 100 are the prerequisite source and material checks.
- **Manifest:** 10 files; after commit, all committed blobs match.
- **Eleven-panel result, unchanged:** current E3, E8, E9 and E10 fail; the other seven are `unknown`; no disagreement.
- **Golden receipt:** regenerated as `receipts/stage3-repair/development-golden.json`. It is byte-identical to `receipts/stage3/development-golden.json`, as expected, since the generator is unchanged.
- **Inspection SVG:** `receipts/stage3-repair/demo/E11-cut6-trimmed.svg` now shows both statuses. I rendered it with headless Edge and looked at it.

## Remaining limits

- Safe seams remain `unknown`. That is Stage 4 territory, unchanged by this repair.
- System's verbatim file cannot pass as written, because v1 of the development checkers is deliberately not re-registered. The adapted copy runs in the suite.
- `receipts/stage3/` holds v1-checker artifacts. Against a v2 registry, their evidence validates as `checker_mismatch`.
- By default the search does not enforce a tolerance policy. A caller opts in with `expected_numerical_tolerances`.
- The holonomy lift is a float64 reconstruction with a heuristic branch margin. It is not an enclosure.
- The search duplicates Stage 2 and Stage 3 claim names so that it never imports a checker. Tests pin both sets.
- **Environment.** Everything above ran on Windows with Python 3.11.9 and NumPy 2.4.4. System's NumPy 2.3.5 environment was not reproduced here.

## Stage 4 proposal (documentation only, not implemented)

The goal is to enclose the **ideal** construction from the exact rational material, never to wrap already-rounded float coordinates.

1. **Decide retained-neighbor pairs by exact identities, not by numbers.**
   - In the ideal development, two faces that share a retained hinge are placed by orientation-preserving isometries that agree on the whole hinge.
   - Each face's off-hinge vertices lie on one side of the hinge line. That side is the sign of an exact rational expression, the cross product of the hinge direction and a vertex offset, dotted with the face's plane normal, computed in 3D from the material.
   - Opposite sides, with both faces convex, gives disjoint interiors.
   - The engine would record this as `exact_computation` about the ideal construction, with obligations stating the isometry and agreement properties the formulas guarantee.
   - This is what currently leaves every safe seam `unknown`.
2. **Enclose everything else rigorously from exact inputs.**
   - Build each chart and transition from exact rational 3D data. Represent rotations by (cos, sin) pairs, obtained from normalized dot and cross products with interval square roots, not from `atan2`.
   - Compose the enclosures along the chain, so every ideal vertex image lies in a certified box.
   - Classify pairs as follows:

     | Outcome | When |
     |---|---|
     | `pass` | a separating axis is certified on the enclosures |
     | `fail` | a witness point is certified strictly inside both ideal faces, as the historical certificate did for cut 6 |
     | `unknown` | neither |
3. **Glued-vertex pairs** that are not adjacent would use enclosed angle sums around the glued vertex. Exact tangency stays `unknown`.
4. **Evidence.** Claims would use `rigorous_enclosure` with an explicit enclosure policy in `Claim.tolerances`. The backend (for example, interval or ball arithmetic) would be pinned and version-recorded like NumPy.
5. **Regression.** The eleven-panel specimen would be the target: the historical exact classes for all 11 cuts should be reproduced, and not only the four failures.

## Not done or not authorized

- Stage 4 implementation, action-context extension, continuous motion, proof-guided seam selection, cap unfolding, Lean/CGAL/FOLD, interactive viewer.
- No merge, PR, release, deployment, external contact, purchases, scheduler changes, or additional agents.
- The branch is pushed as a work branch only.
