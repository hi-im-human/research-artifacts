---
title: Geometry Lab Stage 4B repair return - portable re-checker I01 and I02
status: I01 and I02 repaired in the test-side re-checker; stopped for review; Stage 4B final acceptance held by System
dg-publish: false
---

# Stage 4B repair return (I01, I02)

**From:** Claude Code session (Claude Opus 5.5), outside the project's agent team. I wrote the re-checker adaptation and this repair, so I am the implementer, not an independent reviewer.

**Assignment:** System's review `reviews/stage4b-commit-79/`, handback `commit-80`, read from `origin/main` with `git show`: `REVIEW.md`, `RESULTS.json`, `RECONSTRUCTION-NOTE.md`, `test_stage4b_review.py` (blob `f24d3a11`). Main was not merged. The Stage 4A repairs were not repeated.

## Where it is

- **Branch:** `<private-branch>` in `<private-repo>`.
- **Reviewed head:** `commit-79`; the worktree was clean.
- **Commits:**
  - `commit-81`: the plan and the reproduced review baseline;
  - `commit-82`: the new tests first, with their red run;
  - the repair commit: the re-checker, README, schema, provenance pin and receipts;
  - the commit that adds this file.
- **Changed-file scope** since `commit-79`:
  - **Modified:**
    - `tests/two_rim_ideal_recheck/recheck_ideal_mpmath.py` (the repair);
    - `PROVENANCE-STAGE-4B.json` (that file's pin; the previous hash is kept under `repairs`);
    - `README.md` (status line plus a short Stage 4B section);
    - `TWO-RIM-IDEAL-SCHEMA.md` (the two allowed clarifications and a note on the repaired behaviour).
  - **Added:** `STAGE-4B-REPAIR-PLAN.md`, this file, `tests/two_rim_ideal_recheck/test_repair_i01_i02.py`, and `receipts/stage4b-repair/`.
  - **Unchanged,** checked by diff: every file under `glab/` (arithmetic, definition, rounding, checker, aggregate), `IDEAL-DEVELOPMENT-CONTRACT.md` (so the policy pin and checker revision are unchanged), all of `probes/stage4a/`, and the original `STAGE-4B-RETURN.md` and `receipts/stage4b/`.

## Baseline (reproduced before any change)

System's `test_stage4b_review.py`, run unchanged from a scratch copy with `GLAB_ENGINE` set to this engine: **7 passed, 5 failed**, the five being I01 and the four I02 cases. No adapter was needed (`red-system-review-at-commit-79.log`).

## Repairs (test-side re-checker only)

**I01: an honest all-unknown record is checkable.**
- `_shape` rejects an empty set of precision levels only when some row claims an interval decision (an axis or witness).
- A decided row must still name a recorded level (`bits_level`); level validation is otherwise unchanged.
- `check_seam` computes its own second enclosure only when at least one level is recorded.
- On System's flat E11 derivative (height `1/10^200`, default policy), the report is **verified** with:
  - 45 unknown rows and 10 confirmed Theorem S rows;
  - zero coordinates checked;
  - recomputed verdict **`unknown`**, never `pass`.
- The budget, schedule and rounding are untouched. A failure to confirm an asserted enclosure keeps its meaning.

**I02: every supplied side record and the partition are validated.** This happens in `_declared`, on the original list, before any dictionary or set is built.
- Side rows:
  - `side_pair_ids`: two distinct chain faces;
  - `side_pair_order`: a retained pair at consecutive chain positions;
  - `unrecognized_field`: only side fields;
  - `side_duplicate`, `side_coverage`: each retained pair exactly once;
  - `side_outcome`: `pass` under the supported export.
- Theorem S partition:
  - `partition_shape`, `partition_duplicate`;
  - `partition_overlap`: decided and undecided are disjoint;
  - `partition_coverage`: together they cover the retained pairs;
  - `partition_disagrees`: they agree with the side outcomes.
- Every side record then goes through the existing field checks and the exact Theorem S confirmation. System's four mutations are now rejected with specific reasons:
  - both duplicates: `side_duplicate`;
  - the F99 row: `side_pair_ids`;
  - the contradictory partition: `partition_overlap`.

## Execution record (each run separate; no counts combined)

Environments: the maintained `.venv` (Python 3.11.9, NumPy 2.4.4, pytest 9.1.1) and the throwaway review and mpmath-only environments. Both were re-verified against `RECORD` before use: all hashed files match (`environment-record-audit.json`).

| Run | Result | Receipt |
|---|---|---|
| System's review file, at `commit-79` | 7 passed, 5 failed | `red-system-review-at-commit-79.log` |
| New repair tests, before the repair | 12 failed, 5 passed (the passes are the controls and two faults the old code already caught) | `red-repair-tests.log` |
| System's review file, after | **12 passed** | `green-system-review.log` |
| The original 47 portable cases, unchanged | 47 passed | `green-original-47.log` |
| Whole portable directory (47 + 17 new) | 64 passed | `green-portable-recheck.log` |
| Prototype review environment | 63 passed | `green-prototype-review-env.log` |
| Inherited engine suite | 411 passed | `green-inherited-suite.log` |
| New maintained tests | 212 passed, 2 skipped (the two re-check modules: mpmath absent) | `green-new-maintained.log` |
| Whole `tests/` | 623 passed, 2 skipped | `green-all-tests.log` |
| Prototype controls, targets, A01/A02 | 99, 7, 36 passed | `green-prototype-*.log` |
| Fresh E11 and prism receipts | byte-identical to `receipts/stage4b/results` except `timing.json` (the maintained lane is unchanged) | `results/`, `results-vs-stage4b.log` |
| Independent re-check of the fresh E11 bundle (mpmath-only environment, `-I -B`) | exit 0; verified 11/11; 1232/1232 coordinates; 484 Euclidean and 11 witness bounds | `recheck/` |
| Saved E11 run: load and replay | reproduced, 48 of 48 entries, digest reproduced | `replay-e11-run.log` |

**Test changes:** none to System's file, the original 47 cases or any earlier test. The new tests were not edited after their red run.

## Your decisions, as applied

1. **Placement** accepted; the explicit import-boundary tests remain.
2. **Definition identifier** accepted; unchanged.
3. **Common policy** accepted; unchanged.
4. **`pair_coverage_complete` and `not_determined`** kept.
5. **Non-dyadic limitation** accepted as documented; no exact-rational path was added.
6. **README:** a minimal status update saying Stage 4B is implemented on the work branch and under bounded repair and review, not accepted or released.

The two clarifications went into `TWO-RIM-IDEAL-SCHEMA.md`, which is not pinned:
- the separating axis is always nonzero;
- the contract pin is a literal hash in code kept consistent by a test, not automatic runtime invalidation.

The pinned `IDEAL-DEVELOPMENT-CONTRACT.md` was not edited, so no pin or revision changed.

## Remaining limits

- **Same author:** the re-check is independent arithmetic and construction, not peer review.
- **What the re-check does not do:** confirm exact non-dyadic zero-width boxes (accepted limitation), or re-prove Run provenance or Stage 2 source correspondence.
- **Scope of the I02 checks:** they apply to the currently supported export, in which the side claim is declared `pass`. A record declaring premises other than `pass` is still rejected (`declared_claims`) rather than interpreted.
- **Written lemmas:** reviewed written derivations, not machine-checked, not Lean, not human peer review.
- **Finite results:** no universal theorem, untrimmed safety or motion claim.

## Not done and not authorized

- Merge, PR, release, deployment, a new stage, publishing, website or research-publishing 0.4 work, external contact, purchases, scheduler changes, additional agents.
- Core change, new dependency, motion, untrimmed glued vertices, caps, proof selector, Lean, CGAL or FOLD, viewer expansion, relative rounding or performance redesign.
- The branch is pushed as a work branch only.
