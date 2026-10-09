---
title: Geometry Lab Stage 2 plan (exact source geometry port)
author: Claude Code session agent, Claude Opus 5.5
date: 2026-09-28
status: in-scope reconciliation of SYSTEM-TO-CLAUDE-STAGE-2.md; Stage 3 not authorized
dg-publish: false
---

# Inputs read

| Item | Pin |
|---|---|
| `SYSTEM-TO-CLAUDE-STAGE-2.md` | `commit-31`, blob `7c6b33ccd3267140a205bc909daf2906b83b0c36`, read from `origin/main` without merging |
| C01 review `reviews/stage1-repair-review/REVIEW.md` | blob `e03fba5c`; `RESULTS.json` blob `e8437123`; `test_rejection_order.py` blob `7c088430` |
| Reviewed worker head | `commit-30`. The branch had not moved and the worktree was clean. C01 was fixed in `commit-32`. |
| Manuscript | DRAFT-02 §§2–4 and Proposition 3.1, at the Observatory baseline `commit-17`. The Observatory is unchanged through `commit-18`. |
| Ported sources | `normal_fan_inputs.py` (blob `5445ec10`) and `cyclic_normal_splice.py` (blob `314b1938`), from `<research-record>/<historical-folder>/verification/packet/code/` |

# Scope

The pipeline for this stage:

> two rational rims + positive rational height → recorded normalization (the source state) → original maximal facets, hinges, and incidence (the material state) → independent exact source checks → saved and replayed run

**Not in this stage:** float placements, seam search, the cut quotient, trims, pole or defect sign, collision checks, cap unfolding, a viewer, CGAL, or Lean.

The executable input scope is **rational data** (`fractions.Fraction`). The paper's theorem concerns real inputs and is a separate object. Exact execution on particular inputs is not a new universal proof.

# Layout (all under `engine/`)

| Path | Role |
|---|---|
| `glab/core/registry.py` | Adds `Param.list(item)`, the one authorized core addition: it checks for a list and validates each item recursively. |
| `glab/two_rim/source.py` | Input parsing and normalization. Includes the ported `hull2`. |
| `glab/two_rim/material.py` | Original maximal facets, hinges, rim edges, and caps. Includes the ported `splice_cycles`. |
| `glab/two_rim/actions.py` | Registered wrappers `two_rim.source.normalize` v1 and `two_rim.material.build` v1 |
| `glab/check/two_rim_source.py` | Independent exact checker. It imports only `glab.core` and the standard library, never `glab.two_rim`. |
| `tests/two_rim/` | Domain, controls, golden, recorded-execution, and boundary tests |
| `tests/two_rim/pinned/` | Byte-verified copies of the two originals, loaded by file path through `importlib` for the golden tests only. No `sys.path` changes, and nothing is written into historical directories. |
| `TWO-RIM-SCHEMA.md` | Domain schema and API note |
| `PROVENANCE-STAGE-2.json` | Provenance for the port and the fixtures |
| `examples/two_rim_demo.py` | Headless JSON demo |
| `receipts/stage2/` | Receipts for this stage |

# Tasks (test-first; one commit per task)

1. **C01, and `Param.list`.** C01 is done (`commit-32`). Tests for `Param.list` cover:
   - malformed rows and non-list values
   - nested invalid values
   - floats and bools in exact coordinates
   - replay of a rejected attempt
2. **Exact normalization (`source.py`).** Tests cover:
   - both input kinds
   - invalid shapes, where a point must have exactly two coordinates
   - positive height
   - nonempty rim interiors
   - cyclic and reversed normalization
   - explicit hull provenance: every removed point, with its reason
   - repeated and collinear points under both input modes
3. **Original material (`material.py`).** It has stable IDs and ordered boundary incidence, distinguishes caps, and includes triangles. Checks:
   - agreement with the pinned helpers, up to the documented start-index convention
   - the independent oracle
   - targeted controls: shared, one-rim, and opposite normals; multi-face rim vertices; triangles and trapezoids; tiny height; the 10^-20 perturbation
4. **Recorded execution.** Registered actions and checkers; save, load, and replay; parents unchanged; the same material identity across presentations; the demo.
5. **Verification.**
   - the inherited core suite
   - the domain suite
   - the four assessment fixtures
   - **200 seeded random valid rational rim pairs**, with recorded inputs and seed, and rejection counts for invalid samples
   - golden comparisons and oracle coverage, with any subset recorded explicitly
   - hashes, the incremental diff, a push, and `STAGE-2-RETURN.md`

Then stop.

# Known design constraint, to be handed back rather than widened

Checker callbacks receive only their subject state. So the material checker can verify the material against its own coordinates, using the oracle, incidence, and identity. It **cannot** independently verify that those coordinates equal the parent source's normalized rims.

- **Here:** that correspondence is tested in the domain suite, and it follows by construction on replay.
- **Proposed core addition, not implemented:** give checkers read-only copies of the validated dependency states. That would change core semantics beyond C01 and `Param.list`, so it goes back to System.
