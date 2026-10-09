---
title: Geometry Lab Stage 1 return
from: Claude Code session agent (no persona name); Claude Opus 5.5 (claude-opus-5-5); Claude desktop app, Windows 11
to: System / Summer Bee
date: 2026-09-28
status: Stage 0 reconciliation and Stage 1 core complete; stopped before Stage 2
dg-publish: false
---

# Result

The Stage 1 core is built and tested, and it contains no geometry. `glab.core` imports only the standard library. It covers:

- exact input
- canonical records and content hashes
- the versioned registry, with every attempt recorded
- per-claim evidence and conservative summaries
- whole-run integrity with an optional external anchor
- deterministic replay

The full suite has **110 passed**, run from `engine/` with the local `.venv` (Python 3.11.9, pytest 9.1.1). Design reconciliation is in `DESIGN.md`. It is faithful to the approved architecture with amendments A to E, so no further permission was needed.

# Branch, base, head, scope

| Item | Value |
|---|---|
| Branch | `<private-branch>`, worktree `<geometry-lab-worktree>` |
| Base for Stage 1 | the reviewed head `commit-19`. The worktree was clean and the branch had not moved. |
| Handoff read | `git show origin/main:…/SYSTEM-TO-CLAUDE-STAGE-1.md`, `commit-20`, blob `eeb38420`, from `origin/main` at `commit-21`. Main was **not** merged. |
| Commits | `commit-22` (Stage 0 design plus Task 1), `commit-23` (Task 2), `commit-24` (Task 3), `commit-25` (Task 4, demo, README). This return note is the next commit. |
| Scope check | `git diff --name-only commit-19 HEAD` lists only `<engine>/**`, and `assessment/` has no diff. |

No Lean source, manuscript, proof record, review, fixture, root configuration, or sibling project changed. No other agents were dispatched.

# Obligations → tests (final log `receipts/stage1-final.log`)

| Obligation (handoff) | Tests |
|---|---|
| **Exact input.** Integers and exact strings normalize the same way. Floats, bools, nonfinite values, and zero denominators are rejected. | `test_records.py`: `test_equal_exact_spellings_normalize`, `test_fraction_and_decimal_agree`, `test_nonexact_inputs_rejected` (15 cases) |
| **Records.** Canonical JSON, hashes, strict loading (duplicate keys, NaN), state validation, no float in an exact state, approximate never relabeled exact, defensive copies | `test_records.py` (47 in total) |
| **Registry.** Unknown names and versions, bool or string versions, extra, missing, or mistyped parameters, and incompatible input kinds are all rejected, and each **rejection is retained** | `test_registry.py::test_rejections_are_recorded_not_lost` (10 cases), `test_incompatible_input_kind_and_bad_inputs_rejected` |
| **Failed attempts persist**; parents stay unchanged; returned records are copies | `test_failed_construction_is_retained_with_no_output`, `test_callback_cannot_mutate_retained_parent`, `test_returned_records_are_copies` |
| **Integer demo actions live outside the core** | `tests/core/toy.py`, `examples/core_demo.py` |
| **Missing or unknown required evidence** can't produce a pass; unknown propagates; fail dominates | `test_evidence.py::test_missing_required_evidence_cannot_pass`, `test_required_unknown_propagates_and_fail_dominates` |
| **Duplicates and conflicts** are never silently overwritten; repeated checks are retained | `test_repeated_checks_are_retained_and_conflicts_never_overwrite` |
| **Reuse invalidation** after ancestor tampering, a checker revision change, or a tolerance-policy change | `test_changed_ancestor_invalidates_reuse`, `test_checker_revision_change_invalidates_reuse`, `test_tolerance_policy_change_invalidates_reuse` |
| **Ambiguity at a hypothetical glued contact** stays unknown (amendment A) | `test_ambiguous_contact_at_hypothetical_glued_hinge_stays_unknown`, `test_near_integer_float_is_unknown_not_pass` |
| **A rounded representation is kept distinct from its exact source** (amendment C) | `test_rounded_representation_is_not_evidence_about_its_exact_source`, `test_numerical_pass_does_not_satisfy_an_exact_requirement` |
| **Imported results** are not verified by their label | `test_imported_results_are_not_verified_by_label`, `test_runfile.py::test_loaded_evidence_is_not_verified_until_replayed` |
| **`formal_proof`** has no route to a pass | `test_formal_proof_has_no_route_to_pass` |
| **Speculative states** are preserved alongside their failing evidence (amendment D) | `test_speculative_state_is_preserved_with_failing_evidence` |
| **Round trip and replay**, including repeated checks and failed or rejected attempts | `test_runfile.py::test_round_trip_and_replay_reproduce`, `test_save_is_deterministic` |
| **Tampering detected:** state, ancestor, action parameter, action order (with and without renumbering), evidence outcome, checker revision, identities, environment, extra keys, schema | `test_edits_break_internal_integrity` (10 cases), `test_action_order_swap_with_renumbered_seq_still_fails` |
| **Missing referenced record, and cyclic or dangling state graphs** (detected even after the digest is recomputed); duplicate keys and nonfinite values | `test_missing_referenced_state_is_rejected_even_with_recomputed_digest`, `test_cyclic_or_dangling_state_graph_rejected`, `test_malformed_json_rejected` |
| **A wholly rewritten run** fails comparison with an external old digest; an evidence-only edit with a recomputed digest needs that anchor to be caught | `test_wholly_rewritten_run_fails_against_external_old_digest`, `test_evidence_only_edit_with_recomputed_digest_needs_the_anchor` |
| **Loading executes nothing** | `test_loading_does_not_execute` |
| **Replay mismatch, `not_run`, and environment mismatch** never count as a pass | `test_changed_implementation_same_revision_is_a_mismatch`, `test_changed_revision_is_not_run_not_a_pass`, `test_missing_action_makes_dependents_not_run`, `test_environment_mismatch_is_not_reproduced` |
| **The core imports only the standard library**, with no geometry, NumPy, viewer, or dynamic-import code | `test_import_boundaries.py` (2 tests) |

# Test history (all logs preserved in `receipts/`)

- **Initial collection failures.** `task1-initial.log`, `task2-initial.log`, `task3-initial.log`, and `task4-initial.log` each fail at collection, because the tests were written before the modules they import existed.
- **Task 3 intermediate failure.**
  - Log: `task3-intermediate.log`, 5 failed and 76 passed.
  - Cause: a bug in the **test-local** toy checker, which called `float("1/1000")`. The core was not at fault.
  - Fix: I corrected the toy.
  - Record note: I accidentally overwrote that log with a passing run. I then regenerated the failure from the committed buggy `toy.py`, so the saved log is a faithful re-execution of the failure, not the original bytes.
- **Finals.** `task1-final.log` (47), `task2-final.log` (18), `task3-final.log` (16), and `task4-final.log` (29) are the per-task files. `stage1-final.log` is the whole suite: 110 passed.

# Demo (`examples/core_demo.py`)

The demo does the following:

1. Loads the integer state 1200.
2. Adds 2.
3. Retains a failed divide-by-zero attempt.
4. Checks the state: `even` gives `pass`, and `prime_small` gives `unknown` because 1202 is above the checker's range.
5. Saves the run and reloads it against the retained digest.
6. Replays it.

Results:

- Integrity: `internally_consistent`. Anchor: `matched`. Authenticated: `false`.
- Replay: `reproduced`, and the run digest was reproduced.
- The summary stays `unknown` and unverified, both as loaded and after replay, because one requirement is unknown. This is the intended conservative behavior.
- Two runs of the demo produced byte-identical outputs.
- Output hashes are in `receipts/demo/MANIFEST.json`, and they match the committed blobs.
- Run digest: `sha256:5b2fc3c21c782e3091520f4381dbea9d4f54f5b28fe439f51efdfe4e62625b81`.

# Limits and deviations to review

- **The demo's anchor is only illustrative.** `receipts/demo/retained-digest.txt` is committed next to the run it anchors. A real anchor must be stored somewhere independent of the run.
- **Replay is tied to the environment.** The recorded environment includes the platform string and the core revision. Replay on another machine reports `environment_mismatch` by design; it was not attempted.
- **Checker exceptions are not recorded.** A checker that raises during `Run.check` propagates the exception, and no evidence entry is appended. Action attempts, by contrast, are always recorded. During replay, a raising checker is reported as `mismatch`. If a maintained checker needs "attempted but crashed" as data, that is a small Stage 2+ design item.
- **Execution method.** The handoff suggested a `superpowers:executing-plans` skill, which is not available in this environment. I followed the same test-first sequence by hand, with one commit per task.
- **Receipt line endings.** Receipts are kept byte-exact via `engine/.gitattributes` (`receipts/** -text`). Root Git settings were untouched. The pytest logs are Windows console output with CRLF endings. The hashed demo outputs use LF.

# Evidence classes

- **Source inspection:** the handoff, my prior assessment, and DESIGN-BRIEF.
- **Execution:** the receipts above.
- **Exact checking and formal verification:** none apply to geometry in this stage. The core only transports and summarizes claims; it makes none of its own.
- **No certification, proof, or geometry claim is made.**

# One recommended next step

Review `DESIGN.md` §§4–7: the record schemas, validation statuses, and replay outcomes. Stage 2 source geometry would be the first thing to depend on them, so they are cheapest to amend now. Stage 2 is not started and awaits separate authorization.
