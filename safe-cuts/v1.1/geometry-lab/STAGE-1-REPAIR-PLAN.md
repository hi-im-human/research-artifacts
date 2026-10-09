---
title: Geometry Lab Stage 1 repair plan (R01 to R05)
author: Claude Code session agent, Claude Opus 5.5
date: 2026-09-28
status: bounded repair contract; same modular architecture; Stage 2 still on hold
dg-publish: false
---

# Inputs

| Item | Pin |
|---|---|
| System review, `<geometry-lab-project>/reviews/stage1-review/REVIEW.md` | `commit-27`, blob `5993590d9fcc96e9b4c113927a035ad2320bcde1` |
| `test_review_regressions.py` from the same review | blob `52c99f943934cf03becf4cbc8302f6c24b7badaf` |
| `RESULTS.json` from the same review | blob `88edd8119cbd6db8b2894a6f920423eab11e2116` |
| Reviewed worker head | `commit-26` (branch not advanced; worktree clean) |

The architecture is unchanged: standard-library `glab.core` modules, the immutable state store, the registered-callback boundary, conservative handling of `unknown`, and the three-way split between internal integrity, an external digest match, and authentication. Every change below clarifies one of the five findings.

# Contract

**R01. Full replay comparison.**
- Action inputs that JSON can represent are stored with their actual types, so a bool version stays `true`.
- A value JSON cannot represent is stored as a non-executable description `{"python_type": name}`, and its field is listed in `unrepresentable`. On replay that attempt is `not_replayable`, and the whole run is not reproduced. Nothing stored is ever evaluated.
- Replay compares complete canonical entries, including failure messages, not just status and exception type.
- `outcome = "reproduced"` requires every entry to match, the environment to match, **and** the full run digest to be reproduced. Per-entry results remain available as an explicitly partial comparison.

**R02. Recorded checker attempts.**
- `Run.check` appends a check-attempt record **before** it returns or raises. The record carries: its sequence number, checker name, version and revision, parameters, subject, dependencies, status (`completed`, `rejected`, or `failed`), the IDs of the evidence it produced, and failure details.
- The attempt is recorded in every case: a validation rejection, a callback exception, malformed output, an unsupported `formal_proof` output, and a completed check with zero claims. Rejected and failed attempts are then raised to the caller.
- Actions and checks share one ordered `history`. Each evidence record names its producing attempt.
- Replay re-executes whole attempts, not claim-count groups.
- A crash produces no predicate outcome, and earlier evidence is never altered.

**R03. Detachment at every capture and read boundary.**
- Evidence content, including nested receipts and tolerances, is detached through a canonical JSON round trip when it is created. Parameters and payloads are copied when captured.
- `LoadedRun` keeps only validated canonical text. Its `record` and `store` properties return fresh copies built from that one snapshot. Replay re-checks the snapshot digest before using it.

**R04. Coverage in requirements.**
- `Requirement(..., coverage="all")`: the default is `"all"`, the conservative choice. `coverage=None` explicitly accepts any recorded coverage.
- Tokens are matched exactly, with no inference from wording.
- Evidence with a different coverage token cannot supply a pass. Conflicting outcomes across all current records still make the result `unknown`.

**R05. Causality at load.**
- Replaying `history` structurally, without executing anything:
  - a succeeded action's input must already have been produced, and its output's parent must equal that input;
  - a failed attempt's input must already be available;
  - every stored state must be the output of some succeeded action.
- A completed or failed check's subject must already be available, and its evidence IDs must match the evidence records that point back to it.
- Rejected attempts may name missing or invalid inputs, because that is recorded as the reason they were rejected.
- Primitive fields are checked: integers must not be bools, versions must be positive integers for anything that executed, and revisions and seeds must have the right types.
- The loader performs no kind checks, since it has no registry. Those checks happen at replay.

# Format versioning

The schemas become `glab.run/2`, `glab.action/2`, `glab.check/1`, and `glab.evidence/2`. The loader rejects `glab.run/1` with a clear error. No import path is offered, because a v1 file lacks check-attempt history and inventing that history is not allowed. The Stage 1 demo receipt remains a historical v1 artifact.

# Order of work

1. Copy the review cases unchanged, and add nearby controls.
2. Run all of them against the unmodified `commit-26` sources and preserve the red log.
3. Repair capture and immutability, and make replay compare full records.
4. Add recorded checker attempts, coverage matching, and chronology validation.
5. Reconcile `DESIGN.md` and `README.md` with the code.
6. Run everything fresh; run the demo twice with the required contents; write receipts; write `STAGE-1-REPAIR-RETURN.md`; push; stop.
