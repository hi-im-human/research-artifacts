---
title: Geometry Lab Stage 1 repair return (R01 to R05)
from: Claude Code session agent (no persona name); Claude Opus 5.5 (claude-opus-5-5); Claude desktop app, Windows 11
to: System / Summer Bee
date: 2026-09-28
status: bounded core repair complete; stopped for review; Stage 2 not started
dg-publish: false
---

# Result

All five findings are repaired inside `glab.core`. The modular architecture is unchanged. The core still imports only the standard library, and the registered-callback boundary and the unknown-handling rules are preserved.

| Suite | Result |
|---|---|
| Full core suite (fresh) | **144 passed** (`receipts/repair/final-tests.log`) |
| System's review cases, adapted copy (one documented key rename) | **10/10 passed**, included in the 144 |
| System's review cases, **verbatim** | **9 passed, 1 failed** (`receipts/repair/review-verbatim-final.log`) |

The one verbatim failure is R05, and it fails only with `KeyError: 'actions'`. That test indexes the v1 top-level key `actions`. The repaired format, `glab.run/2`, holds actions and check attempts in one ordered `history`, which is the R02 requirement. The adapted copy (`tests/core/test_review_regressions_adapted.py`) changes only `data["actions"]` to `data["history"]`, and its R05 passes. The review said a documented adapter change is acceptable for the typed coverage contract; I apply the same standard here and state it plainly. **The verbatim file is not fully green.**

# Branch, base, head, scope

| Item | Value |
|---|---|
| Branch | `<private-branch>`, worktree `<geometry-lab-worktree>` |
| Reviewed head | `commit-26`. The branch had not moved, and the worktree was clean. |
| Review read | from `origin/main` without merging: `REVIEW.md` blob `5993590d`, `test_review_regressions.py` blob `52c99f94`, `RESULTS.json` blob `88edd811`, all at review `commit-27` |
| Repair commits | `commit-28` (plan, the review cases copied unchanged, controls, red log), `commit-29` (R01 to R05 repairs and test updates). This return and the documentation receipts are the next commit. |
| Scope | The incremental diff from `commit-26` touches only `<engine>/`. The assessment, theorem and manuscript files, the review snapshot on main, `STAGE-1-RETURN.md`, and every Stage 1 receipt are unchanged. |

# Red, then green

- **Against the unmodified `commit-26` sources** (`receipts/repair/red-at-commit-26.log`): 26 failed, 118 passed.
  - The review cases matched System's report exactly: 8 red, with both controls green.
  - 18 of my new controls were red.
- **After the repair:** 144 passed (`green-after-repair.log`, then `final-tests.log` fresh).
- One earlier verbatim run is in `review-verbatim-after-repair.log`, and the final one in `review-verbatim-final.log`. Both show 9 passed and 1 failed, for the key rename above.

# Findings → changes → tests

| Finding | Change | Tests (`tests/core/`) |
|---|---|---|
| **R01** replay reported success with a different digest | Inputs are captured with their actual JSON types, so `version=True` is stored as `true`. A non-JSON input becomes an inert `{"python_type": …}` plus an `unrepresentable` entry, is rejected, and is `not_replayable`. Nothing stored is ever evaluated. Replay compares **complete** entries, including failure messages. `reproduced` requires every entry, the environment, **and** the full digest; entry counts are reported separately as `partial_comparison`. | adapted R01 ×2; `test_rejected_bool_version_is_stored_as_json_bool_and_replays`, `test_unrepresentable_input_is_described_not_evaluated`, `test_reproduced_always_means_full_digest_reproduced` |
| **R02** checker invocations disappeared | A check-attempt record (`glab.check/1`) is appended **before** returning or raising. Statuses are rejected, failed, or completed, including zero-claim checks. Each attempt carries the IDs of the evidence it produced, and each evidence record carries its `attempt`. Actions and checks share one ordered history. Replay re-executes whole attempts. A crash is recorded as a failed attempt, never as a predicate `fail`, and earlier evidence is untouched. | adapted R02 ×2; `test_failed_checker_attempt_is_recorded_raised_and_does_not_negate_earlier_evidence`, `test_rejected_check_attempts_are_recorded_then_raised`, `test_malformed_and_formal_outputs_are_failed_attempts`, `test_zero_claim_and_multi_claim_checks_replay_as_whole_attempts` (includes a repeated check), `test_history_interleaves_actions_and_checks` |
| **R03** mutable references reached retained records | `make_evidence` detaches the whole record through a canonical JSON round trip, including nested receipts and tolerances. Params are copied at capture. `LoadedRun` holds one canonical text snapshot; `record` and `store` are properties that return fresh copies. Replay re-checks the snapshot digest. | adapted R03 ×2; `test_caller_mutation_after_apply_cannot_change_the_record`, `test_loaded_record_and_store_are_fresh_copies_of_one_snapshot` |
| **R04** requirements could not state coverage | `Requirement(..., coverage="all")` matches exact tokens. The default `"all"` is conservative; `None` accepts any coverage explicitly. Evidence with other coverage cannot supply a pass. Outcome conflicts across all current records still make the result `unknown`. The API keyword matches the review test's `coverage=` exactly, so no adapter was needed. | adapted R04; `test_full_coverage_satisfies_default_all_requirement`, `test_partial_coverage_needs_an_explicit_matching_requirement`, `test_missing_scope_evidence_is_not_run`, `test_sample_failure_conflicts_with_full_pass` |
| **R05** loading accepted an impossible chronology | The loader replays `history` structurally (see `DESIGN.md` §7 for the full rules). An executed attempt's input or subject must already have been produced. A succeeded output's parent must equal its input. Every state must have a producing action. Evidence and attempts must match each other. Rejected requests may still honestly name missing inputs. Primitive fields are checked, so a bool is refused as `seq` or `version`, and seed and revision types are enforced. The loader no longer claims kind checks, which need a registry. | adapted R05; `test_rejected_request_for_missing_input_is_an_honest_loadable_record`, `test_orphan_state_rejected`, `test_check_before_its_subject_exists_rejected`, `test_primitive_fields_are_validated` (6 cases) |
| **Documentation** | `DESIGN.md` §§5–9 were rewritten to match the code: the `seed` callback argument, `tolerances`, `expected_tolerances`, `representations`, `load_run(path, expected_digest)` with no registry, and structural versus replay checks. A revision note lists the earlier discrepancies. The README was updated. | not applicable |
| **Format versioning** | The schemas are now `glab.run/2`, `glab.action/2`, `glab.check/1`, and `glab.evidence/2`. The loader rejects `glab.run/1` with an explanation. **No migration** is offered, because v1 lacks check-attempt history and none is invented. | `test_stage1_v1_run_file_is_rejected_clearly` (it loads the historical Stage 1 demo receipt) |

**Intentional changes to Stage 1 tests.** These are marked in the code:

- `test_runfile.py` uses `history` and `report["checks"]` instead of `actions` and `report["evidence"]`, and a v1 run is now an unsupported schema.
- Two evidence-edit cases now fail earlier, on `evidence ids differ`, because attempts bind their evidence IDs.
- The action-swap case now fails on chronology ("not yet available") instead of on the digest.
- The anchor test builds a careful forgery that also rewrites the attempt's evidence list, and still shows that only the external digest catches it.
- `test_evidence.py` passes the new `attempt=` argument to `make_evidence`.

# Demo (`examples/core_demo.py`, run twice)

**History:**

| seq | Entry | Status |
|---|---|---|
| 0 | source | succeeded |
| 1 | add | succeeded |
| 2 | add with `version=true` | rejected (`RegistryError`) |
| 3 | divide by 0 | failed (`ZeroDivisionError`) |
| 4 | even check | completed, 1 claim |
| 5 | profile check | completed, 2 claims: nonnegative `pass`, prime `unknown` |
| 6 | notes check | completed, **0 claims** |
| 7 | fragile check | **failed** (`OverflowError`) |

**Results:**

- Load: `internally_consistent`, anchor `matched`, authenticated `false`.
- External anchor test: a forged rewrite (a different, internally consistent history) loads as `internally_consistent` when unanchored, but is **rejected** against the retained digest.
- Summary: `unknown` and not verified, both as loaded and after replay, because the prime claim is unknown.
- Replay: `reproduced`, 8 of 8 entries, with the full digest reproduced.
- The two runs were byte-identical. Hashes are in `receipts/repair/demo/MANIFEST.json`.
- Run digest: `sha256:67cbe5c598ff9b3320f75929acc7f2448e2b6fd2d0a426935c41196188c2b991`.

**Environment:** Windows 11 (`Windows-10-10.0.26200-SP0`), CPython 3.11.9, pytest 9.1.1 (local `.venv`, pinned). The core revision is recorded in `receipts/repair/environment.json`. Replay is environment-bound and was not attempted across platforms. System's Linux and Python 3.13 environment would report `environment_mismatch`, by design.

# Still open, or deliberately limited

1. **Verbatim R05 key rename.** It fails as-is because of the v1 key `actions`. The adapted copy passes. The alternative would be a top-level `actions` list that also contains check attempts, which would be misleading, so I did not do it. Reviewer's call.
2. **Coverage tokens are compared literally.** "All" does not imply a sample; no implication solver was built, per the review.
3. **Unrepresentable inputs cannot be replayed.** Such attempts are always rejected and never evaluated. Replay reports them as `not_replayable`, and the run as `not_run`.
4. **The demo anchor is illustrative.** `retained-digest.txt` sits next to its run. A real anchor must be stored independently.
5. **My own process slips, disclosed.**
   - While tidying, I deleted two committed repair logs, `green-after-repair.log` and `review-verbatim-after-repair.log`. I restored them unchanged from Git before this commit.
   - The Stage 1 regenerated-log disclosure stands as written in `STAGE-1-RETURN.md`.

# Evidence classes

This is source work plus execution receipts. There is no geometry, no Lean, no certification, and no mathematical claim. The core only transports, binds, and summarizes claims; it makes none of its own.

# One recommended next step

Re-review the v2 record contract in `DESIGN.md` §§5–7, and decide on open item 1. Then decide whether Stage 2 may start. **Stage 2 is not started.**
