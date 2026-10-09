---
title: Geometry Lab Stage 4B repair plan - portable re-checker I01 and I02
author: Claude Code session (Claude Opus 5.5), outside the project's agent team
date: 2026-09-29
status: plan, committed before any change; stop after STAGE-4B-REPAIR-RETURN.md
dg-publish: false
---

# Stage 4B repair plan (I01, I02)

## Inputs

- **Handback:** `reviews/stage4b-commit-79/` on `origin/main`, `commit-80`, read with `git show`: `REVIEW.md`, `RESULTS.json`, `RECONSTRUCTION-NOTE.md`, and `test_stage4b_review.py` (blob `f24d3a11`).
- **Worker head:** `commit-79`, equal to its remote, clean worktree.
- **Baseline reproduced first:** System's review file, run unchanged from a scratch copy with `GLAB_ENGINE` set to this engine in the review environment: **7 passed, 5 failed**, the five being I01 and the four I02 cases (`receipts/stage4b-repair/red-system-review-at-commit-79.log`). No adapter was needed.

## Scope

Only the test-side portable re-checker `tests/two_rim_ideal_recheck/recheck_ideal_mpmath.py` and its tests, plus the documentation System allowed:
- a minimal current-status update in `engine/README.md` (Stage 4B implemented on the work branch, under bounded repair and review; not accepted or released);
- two clarifications in `TWO-RIM-IDEAL-SCHEMA.md`: the separating axis is nonzero; the contract pin is a literal hash in the code plus a consistency test, not automatic runtime invalidation.

`IDEAL-DEVELOPMENT-CONTRACT.md` is **not** edited, so its pinned hash, the policy, the checker revision and the provenance record stay as they are.

Unchanged: the arithmetic, the ideal definition, the rounding, the main checker and aggregate, all of `probes/stage4a/`, the original Stage 4B return and receipts. Anything beyond these bounds would stop the work for a decision.

## I01: an honest all-unknown bundle must be checkable

- `_shape` will reject an empty map of precision levels **only when some row claims an interval decision** (an axis or witness). With no such row, no enclosure is asserted and none is required.
- A decided row must still name an existing level (`bits_level`), and the level checks are unchanged.
- `check_seam` computes its own second enclosure only when at least one level is recorded. With none, zero coordinates are checked.
- Theorem S rows are still confirmed, unknown rows counted, and the recomputed verdict is `unknown`, never `pass`.
- Budget, schedule and rounding are not touched.

## I02: every supplied side record and the partition are accounted for

In `_declared`, before any dictionary or set is built:
- **Side rows:**
  - each must be an object with only the recognized side fields (`unrecognized_field`);
  - its pair must be two distinct chain faces (`side_pair_ids`) at consecutive chain positions (`side_pair_order`);
  - each retained pair appears exactly once (`side_duplicate`, `side_coverage`);
  - under the supported export (claim 5 declared `pass`), each row's outcome must be `pass` (`side_outcome`).
- **Theorem S partition:**
  - `decided_pairs` and `undecided_pairs` must be lists of pairs without duplicates (`partition_duplicate`);
  - they must be disjoint (`partition_overlap`) and together cover the retained pairs (`partition_coverage`);
  - they must agree with the side outcomes (`partition_disagrees`).
- **Every side record,** not only the decided ones, then enters the shape checks and the exact Theorem S confirmation under the existing field rules.

## Tests (before the change)

- **System's file,** run unchanged, is the acceptance target: 12 cases.
- **New `tests/two_rim_ideal_recheck/test_repair_i01_i02.py`,** with a single fault per test and its expected code:
  - I01: the flat E11 derivative (height `1/10^200`, default policy) verifies with 45 unknown rows, 10 confirmed Theorem S rows, zero coordinates and verdict `unknown`;
  - I01: that bundle with one row forged into an axis certificate is rejected (`bits_level`);
  - I01: a genuine E9 bundle still verifies with verdict `fail`, distinct from `unknown`;
  - I02: each new code above, including System's four mutations with their specific reasons.
- **Reruns after the repair:**
  - the 47 portable cases unchanged;
  - the maintained suite (inherited and new);
  - prototype controls, targets and A01/A02, and the prototype review environment;
  - the fresh E11 and prism receipts, the independent re-check, and save/replay.
- **Receipts** go under `receipts/stage4b-repair/`. Each run is recorded separately; no counts are combined into totals that were not executed.

## Not in this repair

A second exact-rational confirmation path (not authorized); any change to the maintained checker, aggregate, arithmetic or contract text; merge, PR, release, deployment, publishing, external contact, new stages or agents.
