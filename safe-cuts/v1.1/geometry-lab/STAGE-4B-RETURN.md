---
title: Geometry Lab Stage 4B return - maintained positive-trim ideal-development lane
status: implemented and tested on the work branch; stopped for review; no merge, PR or release
dg-publish: false
---

# Stage 4B return

**From:** Claude Code session (Claude Opus 5.5), outside the project's agent team. I wrote the prototype, the re-checker and this port, so I am the implementer, not an independent reviewer.

**Assignment:** `SYSTEM-TO-CLAUDE-STAGE-4B-commit-66.md` (authorization `commit-67`), with `reviews/stage4a-recheck-commit-66/`. Read from `origin/main` with `git show`; main was not merged.

## Where it is

- **Repository:** `<private-repo>`, branch `<private-branch>`.
- **Reviewed head:** `commit-66`; the worktree was clean and equal to its remote.
- **Commits,** in order:
  - `commit-68`: `STAGE-4B-PLAN.md`, before any production edit;
  - step 1 (arithmetic): `commit-69` tests, then `commit-70` implementation;
  - step 2 (state, action, checker, contract): `commit-71` tests, then `commit-72` implementation;
  - step 3 (aggregate, firewall, replay, determinism): `commit-73` tests, then `commit-74` implementation;
  - step 4 (re-check): `commit-75` the verbatim re-checker copy, `commit-76` tests, `commit-77` the binding-layer adaptation;
  - `commit-78`: receipts, schema contract, provenance;
  - the commit that adds this file.
- **Changed-file scope,** checked with `git diff --diff-filter=MDR commit-66 HEAD` (empty):
  - **no existing file was modified or deleted**; every change is a new file under `engine/`;
  - unchanged: `glab/core/`, `glab/check/`, `search.py` and every existing generator, all of `probes/stage4a/`, every earlier plan, return, receipt, review and fixture, the assessment, the manuscript and the frozen Lean;
  - nothing was installed into the maintained `.venv`.

| New file(s) | Role |
|---|---|
| `glab/rigorous/ratint.py` | the accepted interval code (standard library only) |
| `glab/ideal_check/geometry.py`, `glab/ideal_check/checker.py` | checker side: exact model, premises, Theorem S, enclosures, the eight claims and `IDEAL_POLICY` |
| `glab/two_rim/ideal_actions.py`, `glab/two_rim/ideal_search.py` | the `two_rim.ideal.define` v1 action; the separate search entry point and the aggregate |
| `IDEAL-DEVELOPMENT-CONTRACT.md`, `TWO-RIM-IDEAL-SCHEMA.md`, `PROVENANCE-STAGE-4B.json` | maintained explanatory contract, schema contract, pins |
| `tests/two_rim_ideal/` (17 files), `tests/two_rim_ideal_recheck/` (4 files) | maintained tests and receipt script; the test-side re-checker, its exporter and tests |
| `receipts/stage4b/` | red and green logs per step, final logs, results, re-check report, environment |

## What was built

- **State** `two_rim.ideal_trimmed_development`, representation `exact`, payload `two_rim.ideal_trim/1`. It holds:
  - an exact copy of the parent cut;
  - the canonical `delta`;
  - the prototype's orientation and normalization literals;
  - definition `two_rim.ideal_development/1`.

  The parent is always a cut. No derived coordinates are stored.
- **Action** `two_rim.ideal.define` v1.
  - Refused with no state: non-canonical or out-of-domain `delta`, and non-cut parents (`test_define_and_schema.py`).
- **Checker** `two_rim.check.ideal_trimmed_development` v1.
  - Contextual: it reconstructs `D` from the actual parent cut and grandparent material, re-derives the chain, and never imports the generator or NumPy.
  - Eight claims:
    - exact: schema, cut copy, domain, local premises and the retained-hinge side test;
    - the Theorem S inference: `exact_computation`, declaring the pinned L1/L2/S dependency, never `fail`;
    - the remaining pairs: `rigorous_enclosure`, `rational_interval`;
    - pair coverage.
  - Before a certificate is recorded, every reported bound is re-verified exactly with the R01 rules. A row that fails becomes `unknown`.
  - Unsupported input and failed premises make the later claims `unknown` (`unsupported input`), never an overlap.
- **Policy** `IDEAL_POLICY` (`two_rim.ideal.evidence/1`), instance-independent. It fixes:
  - the arithmetic, root rule, absolute outward rounding with the exact zero-width path, schedule `16…512`, budget and decision rules;
  - the analytic dependencies: `IDEAL-DEVELOPMENT-CONTRACT.md` pinned by LF SHA-256 `3f8f5180…`, with source blobs `d06000f8` and `ed135840`.
- **Aggregate** `source_linked_ideal_trimmed_obligations`, in the separate entry point `ideal_candidate_search`. It requires, on the actual subject hashes:
  - source v2 (4 claims), material v2 (5, including `matches_parent_source`), cut v1 (5) and ideal v1 (8);
  - current evidence, the expected methods, coverage and parameters, no policy on exact claims and `expected_policy` (a required argument) on the two pair claims;
  - each covering evidence record from the expected checker name and version.

  `ideal_geometric_verdict` is `pass`, `fail` (certified witness), `unknown` (valid evidence, undecided pair) or `not_determined` (missing, stale, failing, foreign or policy-mismatched evidence, or unsupported input). The float search and its totals are untouched.
- **Portable re-check** (test-side). The accepted re-checker `cb483479` was copied verbatim, then adapted **only in its binding layer**, to bundle `two_rim.ideal.recheck_bundle/1`: stored states plus the ideal checker's evidence, with per-precision box levels and recomputed claim outcomes. Its verification core is unchanged, and `test_recheck_provenance.py` checks this by comparing ASTs. Its scope states:
  - local hypotheses and recorded bounds are checked;
  - Run provenance and Stage 2 source correspondence are not re-proved;
  - `verified` is not a safety statement;
  - a containment failure means **not confirmed**.

## Source pins

| Source at `commit-66` | Blob | Port |
|---|---|---|
| `probes/stage4a/ratint.py` | `b4f5c150` | `glab/rigorous/ratint.py`: code unchanged, docstring rewritten (AST test) |
| `probes/stage4a/ideal.py` + `classify.py` | `de3cae44`, `c82b5873` | `glab/ideal_check/geometry.py`: 25 definitions AST-identical; `classify_seam` adapted; `local_premises` and `verify_certificate` new; Run-bound code not ported |
| `probes/stage4a/binding.py` | `8f76e87a` | the prerequisite rule, re-implemented in `ideal_search.py` on the core API |
| `probes/stage4a/recheck_mpmath.py` | `cb483479` | `tests/two_rim_ideal_recheck/recheck_ideal_mpmath.py` (verbatim `commit-75`, adapted `commit-77`) |
| `STAGE-4A-DESIGN.md` §§2.1–2.3, 4, 5.1, 5.4 | `d06000f8` | carried into `IDEAL-DEVELOPMENT-CONTRACT.md` |
| `probes/stage4a/L4-CORRESPONDENCE.md` | `ed135840` | referenced by blob from the contract; its accepted points restated |
| prototype controls C1–C6, A03, R01/R02 tests | `349a31f7`, `97b90062`, `e5cf8fb3`, `b5cbb7cb`, `af11a53e` | ported with import changes into the new tests |

`test_provenance_record.py` recomputes every file hash in `PROVENANCE-STAGE-4B.json` and every source Git blob, so it also shows the prototype files are unchanged.

## Execution record

All runs are this session's own, on Windows 11 with Python 3.11.9. The maintained `.venv` has NumPy 2.4.4 and pytest 9.1.1. The throwaway review environment and the mpmath-only environment were re-verified against `RECORD` first: every hashed file matched, and only console launchers and one NumPy `.pyc` are absent (`environment.json`).

**Red runs (tests first).** Every red run failed as intended.

| Step | Red result | Kind |
|---|---|---|
| 1 | 1 collection error | import failure: module absent |
| 2 | 7 collection errors | import failures: modules absent |
| 3 | 4 collection errors | import failures: module absent |
| 4 | 45 failed, 1 passed | exercised assertions: the verbatim re-checker refuses the new bundle schema, and only the missing-schema fault passes |

**Final runs.**

| Run | Result | Receipt |
|---|---|---|
| Inherited engine suite | **411 passed** | `final-inherited-suite.log` |
| New maintained tests | **212 passed, 1 skipped** (the re-check module: mpmath absent) | `final-new-maintained.log` |
| Whole `tests/` | 623 passed, 1 skipped | `final-all-tests.log` |
| Prototype controls, targets, A01/A02 | 99, 7, 36 passed | `final-prototype-*.log` |
| Review env: prototype `review_env` (A03, adapted prior review, R01/R02) | 63 passed | `final-review-env-prototype.log` |
| Review env: new re-check tests | **47 passed** | `final-review-env-recheck.log` |
| Review env: System's preserved commit-62 review + follow-up | 24 passed | `final-system-review-and-followup.log` |
| Review env: System's commit-62 acceptance cases from `main` (scratch copy via `git show`) | 20 passed | `final-system-commit-62-acceptance-from-main.log` |

**Results and checks.**

- **E11, δ = 1/10000** (`results/e11-ideal-summary.json`):
  - 605 pairs: 110 by Theorem S, 484 separating axes, 11 witnesses, 0 unknown; at most 64 bits;
  - `pass`: E0, E1, E2, E4, E5, E6, E7; `fail`: E3, E8, E9, E10, including F10/F7 at E9;
  - all seams source-linked; the search took 3.6 s (`timing.json`).
- **Port equivalence:** every Theorem S record and interval row is identical to the prototype's (`e11-port-equivalence.json`).
- **Historical classes,** read after classification: 11 of 11 agree.
- **Prisms:** 32 seam/trim cases pass with zero-width boxes (`prisms.json`):
  - SQUARE at δ = 1/4, 1/3, 1/7, 1/10000, 10⁻³⁰ and 1/2 − 10⁻³⁰;
  - a non-dyadic prism at δ = 1/3 and 1/7.
- **Independent re-check** of the fresh E11 bundle, in the mpmath-only environment with `-I -B`: **exit 0**; verified 11/11; 605 rows; 1232 of 1232 coordinates contained; 484 Euclidean and 11 witness bounds confirmed (`recheck/`).
- **Saved run:** loads against its digest and replays as `reproduced`, 48 of 48 entries and the digest reproduced (`replay-e11-run.log`).
- **Determinism:** a twin run of the receipt script is byte-identical except `timing.json` (`results-twin-comparison.log`).

**Test changes after a red run** (no assertion was weakened):
- Step 2: the new tests' import paths changed when the modules moved (next section).
- Step 4: two tests were added after the adaptation: the non-dyadic limitation test and the AST provenance test.
- An extra run: my first prototype `review_env` run lacked `GLAB_ENGINE` and stopped at collection. Its log is kept (`…invocation-error…`), and the rerun is the 63 above.

## Deviations from the plan

1. **Module placement.**
   - Planned: `glab/check/ideal_geometry.py`, `glab/check/two_rim_ideal.py` and `glab/two_rim/ideal.py`.
   - The inherited `tests/two_rim/test_boundaries.py` allows a `glab/check` module only the standard library and `glab.core`, and a `two_rim` module only listed siblings. So:
     - the checker side is the new package `glab/ideal_check/`;
     - the generator side is one self-contained `ideal_actions.py`.
   - The inherited tests are unchanged.
2. **`TWO-RIM-IDEAL-SCHEMA.md`** was written at the end, not with the step-2 tests.
3. **`README.md` was not updated,** because the plan committed to no edits of existing files. Its front matter still says "Stage 4 not authorized". A one-line update can follow if you want it.
4. **Re-checker field classes.** In the copy, `bits` is now a checked field: it selects the recorded precision level. The diagnostic list names the receipt summaries and the `sqrt_records`.

## Finding: a limit of the second enclosure

The mpmath re-check **cannot confirm exact non-dyadic zero-width boxes**. A recorded box `[1/3, 1/3]` cannot contain a binary interval of positive width. On the non-dyadic prism the report is `failed` with only `containment` codes (108 of 128 coordinates), while every certificate re-verifies and every seam recomputes to `pass`. The report states this as *not confirmed*, per your wording, and `test_exact_non_dyadic_boxes_are_not_confirmed_by_binary_intervals` pins it. E11 and the dyadic prisms confirm fully.

## Remaining assumptions

- **Same author:** the re-check is independent arithmetic and construction, not peer review.
- **Written lemmas:** L1, L2, Theorem S, the separation and witness lemmas, and L4 are reviewed written derivations: not machine-checked, not Lean, not human peer review.
- **Interval code:** tested and independently re-checked, not formally verified.
- **Source correspondence** comes from the Stage 2 checkers, which the aggregate requires. The re-check does not re-prove it.
- **Finite scan:** the results cover the bounded specimens only. They are no universal theorem, no untrimmed or full safety, and no motion claim.

## Decisions for System

1. The package placement `glab/ideal_check/` and the merged `ideal_actions.py`, both forced by the inherited boundary tests.
2. The definition identifier `two_rim.ideal_development/1` (the Stage 4A definition, renamed only).
3. One policy object for both pair claims, carrying the arithmetic trusted base and the pinned analytic dependencies. The Theorem S inference uses `exact_computation` with that declaration.
4. The `pair_coverage_complete` claim, the issuance-time self-check, and the four verdict values, including `not_determined`.
5. The non-dyadic limitation: accept it as documented, or authorize an exact-rational confirmation path for zero-width boxes in the test-side re-checker.
6. Whether to update `README.md`'s status line.

## Not done and not authorized

- Merge, PR, release, deployment, publishing, website or research-publishing 0.4 work, external contact, purchases, scheduler changes, additional agents.
- Motion, untrimmed glued vertices, caps, proof-guided selection, Lean, CGAL or FOLD, viewer expansion, relative rounding or performance redesign.
- No core change, no new dependency, no changed mathematical definition.
- The branch is pushed as a work branch only.
