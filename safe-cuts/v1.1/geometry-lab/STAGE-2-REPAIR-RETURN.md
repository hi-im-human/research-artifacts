---
title: Geometry Lab Stage 2 repair return (D01 to D03)
from: Claude Code session agent (no persona name); Claude Opus 5.5 (claude-opus-5-5); Claude desktop app, Windows 11
to: System / Summer Bee
date: 2026-09-29
status: bounded repairs complete; source construction unchanged; stopped before Stage 3
dg-publish: false
---

# Result

D01 to D03 are repaired. **The generator is unchanged**: `source.py`, `material.py`, and `actions.py` have the same revision as at `commit-37` (`sha256:86cc1e9a…`).

| Suite | Result |
|---|---|
| Full suite (`receipts/stage2-repair/final-all-tests.log`) | **288 passed**: 175 core and 113 two-rim |
| System's review cases, adapted copy | **13 of 13 passed**, including both controls, all 11 former red expectations, and D01, D02, and D03 |
| Golden and oracle campaign, rerun with v2 claims (4 fixtures, 200 seeded random cases, 50 supplementary) | **All pass all 9 claims**, correspondence included |
| Two-rim demo | byte-identical across two runs |

The adapted copy's only change is checker version `1 → 2`, in three calls.

# Branch, base, head, scope

| Item | Value |
|---|---|
| Review read | from `origin/main` without merging: `commit-38`; `REVIEW.md` blob `5461cb2f`, `test_source_boundary.py` `9e4535e2`, `RESULTS.json` `312c1ba1` |
| Base | reviewed head `commit-37`. The branch had not moved, and the worktree was clean. |
| Commits | `commit-39` (plan, review cases verbatim and adapted, red run), `commit-40` (D01 core context), `commit-41` (D01–D03 checker, docs, demo, tests, receipts). This return is the next commit. |

**Scope.** Everything is inside `<engine>/`.
- **Modified:** `glab/core/registry.py` and `glab/core/runfile.py` (the authorized context only), `glab/check/two_rim_source.py`, `DESIGN.md`, `TWO-RIM-SCHEMA.md`, `README.md`, `examples/two_rim_demo.py`, and four tests or test helpers that call the checkers.
- **Added:** new tests, `review-cases/stage2-review/`, `STAGE-2-REPAIR-PLAN.md`, `receipts/stage2-repair/`, and this return.
- **Unchanged:** every earlier return, plan, receipt (`receipts/`, `receipts/repair/`, `receipts/c01/`, `receipts/stage2/`), source copy, and the assessment. The manuscript and proof were not touched.

# Red, then green

- **Against the unmodified `commit-37` sources:**
  - System's file, verbatim: **11 failed, 2 passed** (`review-verbatim-red-at-commit-37.log`), exactly as reported.
  - The whole suite plus new tests: 45 failed, 234 passed, and 1 collection error (`red-at-commit-37.log`). The collection error is because `DependencyContext` did not exist yet.
- **After the repair:** 288 passed.
- **System's Stage 2 review file, run verbatim after the repair:** **13 failed**. All 13 fail with `RegistryError: unknown version 1 of checker 'two_rim.check.source'` (`review-verbatim-stage2-review.log`). The claim sets changed, so the checkers are honestly registered as v2 only, and the adapted copy passes 13 of 13.
- **The older verbatim files are unchanged:** Stage 1 is still 9 passed and 1 failed (the accepted `actions` key rename), and C01 is 2 of 2.

# D01. Opt-in read-only dependency context and source correspondence

**Core change** (`commit-40`, the one authorized addition):
- `CheckerSpec` gains `uses_context: bool = False`, validated as a real `bool`.
- A declared contextual checker is called as `fn(subject, params, context)`. Two-argument checkers are unchanged, and nothing is guessed from signatures.
- `DependencyContext(store, subject)`:
  - validates the chain, then snapshots the canonical texts of **exactly** the subject's ancestor closure
  - holds no store, registry, or generator
  - `get(h)` returns fresh copies inside the closure and raises `ContextError` outside it; `parent()` and `dependencies` are also provided
- The closure is the same `dependencies` already recorded on the check attempt and on each evidence record. Integrity checks, reuse validation, and replay therefore bind it, and **the history format is unchanged**.
- A `ContextError`, like any checker exception, is a **failed attempt**, never a predicate outcome.
- Tests (`tests/core/test_dependency_context.py`, 9):
  - the bool contract
  - closure-only reads
  - no store or registry reachable from the context
  - a root subject having no parent
  - a mutation through the context not reaching the store
  - an unrelated read becoming a failed attempt with no evidence
  - two-argument checkers unchanged
  - staleness after an ancestor change
  - save, load, and replay reproduced
  - the constructor validating the chain

**New claim `two_rim.material.matches_parent_source`.** It is part of the material checker, v2 and contextual. It compares the material with its actual immediate `two_rim.source` parent, without calling any generator:
- normalized coordinates, in canonical order, with the `A{i}`/`B{j}` association and counts
- `z` heights and `height`
- the cap planes
- units, convention, and number domain

A missing parent, a wrong-kind parent, an invalid parent schema, or a mismatch gives `fail`. A direct call without a context gives `unknown`.

Tests (`tests/two_rim/test_repairs_d01_d03.py`):
- correct correspondence
- wrong height and shifted `xy`, where **only** the correspondence claim fails and the intrinsic claims stay true, as the review expected
- reordered presentations with equal normalized data, which pass
- a material with no parent, and a material whose parent is the wrong kind
- a direct call without a context giving `unknown`
- staleness after a source edit
- save, load, and replay
- v1 no longer registered

The demo includes a faulty registered builder: a height-4 material under the height-2 F2 source. It passes record schema, identity, oracle, and incidence, and **fails `matches_parent_source`**. Its summary is `fail`.

# D02. Validation before any lossy conversion

**New claim `two_rim.material.record_schema`.** It checks the documented ID namespaces **on the lists, before any set or dict is built**:
- `A0…A{m−1}` then `B0…B{k−1}`, with `m` and `k` at least 3
- exactly `RA0…` then `RB0…`, with consecutive ends
- `E0…E{n−1}`, one per face
- `F0…F{n−1}`
- caps exactly `[C_TOP, C_BOTTOM]`

It also checks uniqueness, counts, field shapes, and referential integrity.

**`incidence_and_rings` also checks each cap ring.** The ring must be its rim in the documented canonical **clockwise source order**, with `boundary_edges[k] = R?{k}` joining consecutive ring vertices, and the rim path must be strictly convex. That is the existing convention; no new cap orientation was introduced, and nothing is unfolded.

**Caught (tests):**
- a duplicate face ID
- an appended duplicate hinge
- an appended duplicate rim edge
- a duplicate vertex
- a duplicate cap
- an undeclared hinge reference
- a crossed top-cap ring
- misaligned cap edges
- a reversed bottom-cap ring

Valid controls pass. The triangles-and-trapezoids and trapezoid-only fixtures pass with both caps, and legitimately shared vertices, referenced by several faces, are not mistaken for duplicate declarations. A valid content hash never substitutes for structure.

# D03. Shapes and versions checked before interpretation

**New claim `two_rim.source.record_schema`.** It checks:
- the supported schema version and exact key sets
- `unitless`, the documented convention text, and `exact_rational`
- input points with exactly two exact values, kept as given (spellings are preserved)
- normalized points with exactly two canonical exact strings
- decision-record shapes and types

**Strict points.** `_pt` now rejects any point without exactly two coordinates, instead of reading the first two.

**Unknown versions.** When a record's schema claim fails, all its other claims are `unknown` ("not interpreted"). An unknown version is never read as the old one.

**Tests:**
- an extra input coordinate, and a missing one
- a bool coordinate
- an extra normalized coordinate
- a non-canonical normalized spelling
- the `/99` schema
- wrong units
- a missing decision field
- the unknown material schema
- the valid-spelling control: input `["0.0", 0]`, `[" 4 ", "0/1"]`, height `"2.0"` all pass

**Cost note corrected:** the oracle is **O(V⁴)** arithmetic operations, before rational bit-complexity.

# Other test changes (documented in each file)

- `test_checker.py`: a direct call has no context, so correspondence is asserted to be `unknown`. Three mutations (dropped face, diagonal split, merged near-coplanar triangles) are now caught first by `record_schema`. Their original intent is kept by also asserting that the oracle alone rejects them.
- `test_actions.py`, `test_golden.py`, `golden_support.py`, and `write_golden_receipt.py`: use v2 and the full claim sets. The golden and oracle helper now checks each material with its real source context.

# Receipts and hashes (`receipts/stage2-repair/`)

| Receipt | Content |
|---|---|
| `random-200-v2.json` | SHA-256 `e015d2e41af12419434f74941ad4fd9c41abb3efbd608fe6ef45862055852993`. Seed `20260928`: 200 valid and 0 rejected. Fixtures all OK, random 200 of 200 OK, supplementary (seed `20260929`) 50 of 50 OK with 25 all-trapezoid. Oracle coverage is full. |
| `demo/` | run digest `sha256:4472e5b6c2de1bc1be184338a3c3fa0c2eb0eb7fdd8a10b1be73074c4df63952`; manifest in `demo/MANIFEST.json`. Replay reproduced 20 of 20 with the full digest. The 36 requirements for the four legitimate bodies (4 × 9) give `pass`, not verified, as loaded, and `pass`, verified, after replay. The faulty builder's summary is `fail`. |
| `environment.json` | Windows 11, CPython 3.11.9, pytest 9.1.1; core revision `sha256:950d9a74…`; checker v2 revision `sha256:3ed63baa…`; generator revision unchanged at `sha256:86cc1e9a…` |
| Logs | red, green, per-review-file verbatim runs, and the final full suite |

# Discrepancies and remaining limits

1. **System's Stage 2 file, run verbatim, is 0 of 13, all on the version lookup.** This follows from honest versioning. The adapted copy is green. Reviewer's call if another shape is preferred.
2. **Correspondence covers only the immediate parent.** It compares the material with its immediate `two_rim.source`. The context exposes the whole closure, but no longer chains exist in this domain yet.
3. **The convention text is compared as an exact string.** The checker holds an independent copy of the documented v1 convention. Any future wording change must be a versioned schema change.
4. **The recorded attempt does not say which hashes a contextual checker actually read.** Only the closure it was offered is bound. The review said the full closure is sufficient for this stage.
5. **Historical receipts are v1.** Replaying the Stage 2 demo run under the current registry reports its v1 checks as `not_run`, because v1 is not registered. Those receipts are kept unchanged as history.
6. **Environment-bound.** All executions were on Windows 11 and Python 3.11.9. Nothing was run on System's Linux or Python 3.13 environment. There was no Lean run, and no formal or universal claim is made.

# One recommended next step

Review the v2 checker contract (`TWO-RIM-SCHEMA.md`, Checkers section) and the `DependencyContext` API (`DESIGN.md` §5). Accept or amend the versioning choice in item 1 before any Stage 3 development depends on these claims. **Stage 3 is not started.**
