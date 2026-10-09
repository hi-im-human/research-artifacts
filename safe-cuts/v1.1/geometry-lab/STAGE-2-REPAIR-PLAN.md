---
title: Geometry Lab Stage 2 repair plan (D01 to D03)
author: Claude Code session agent, Claude Opus 5.5
date: 2026-09-29
status: bounded repair contract; source construction unchanged; Stage 3 held
dg-publish: false
---

# Inputs

| Item | Pin |
|---|---|
| System review `reviews/stage2-review/REVIEW.md` | `commit-38`, blob `5461cb2f`. `test_source_boundary.py` blob `9e4535e2`; `RESULTS.json` blob `312c1ba1`. All read from `origin/main` without merging. |
| Reviewed head | `commit-37`. The branch had not moved, and the worktree was clean. |

The construction is retained: `glab/two_rim/source.py`, `material.py`, and `actions.py` are **not changed**, so the generator revision and the source and material states stay the same.

# D01. Opt-in read-only dependency context (the one authorized core change)

- **Registration.** `CheckerSpec` gains a declared field `uses_context: bool = False`. It is validated as a real `bool`. Ordinary checkers keep the two-argument `fn(subject, params)`. A checker declared with `uses_context=True` is called as `fn(subject, params, context)`. No signature is guessed at runtime.
- **The context.** `glab.core.runfile.DependencyContext(store, subject_hash)` validates the subject's chain and **snapshots the canonical texts of exactly that closure**. It holds no reference to the store, registry, or generator.
  - `get(h)` returns a fresh copy for a hash in the closure. Any other hash raises `ContextError`.
  - `parent()` returns the immediate parent, or `None`.
  - `dependencies` returns the closure.
- **Binding.** The context exposes the same closure already recorded as the attempt's `dependencies` and each evidence record's `dependencies`. Integrity checks, reuse validation, and replay therefore already bind it. The history format is unchanged, so no new run-schema version is needed.
- **Failures.** A context read error, or any checker exception, is an execution failure of the attempt, never a geometric counterexample.
- **New predicate.** `two_rim.material.matches_parent_source` compares the material with its actual immediate `two_rim.source` parent, independently and without calling the generator:
  - normalized top and bottom coordinates in canonical vertex order, with the `A{i}`/`B{j}` association and counts
  - `z` heights and `height`
  - cap planes
  - units, coordinate convention, and number domain
  - A missing, wrong-kind, schema-invalid, or mismatched parent gives `fail`. A call made without a context gives `unknown`, since correspondence cannot be evaluated.

# D02 and D03. Record validation before interpretation

- **New `two_rim.source.record_schema` and `two_rim.material.record_schema` predicates.** They check:
  - a supported schema version and the exact key sets
  - units, convention, and number domain
  - planar points with exactly two exact coordinates
  - canonical exact strings in the normalized and material fields, while input spellings are kept as given
  - decision-record shapes
  - ID namespaces and **uniqueness checked on the lists before any set or dict is built**: `A0…`, `B0…`, `RA`/`RB` with their ends, `E0…`, `F0…`, and caps `[C_TOP, C_BOTTOM]`
  - counts and referential integrity
- **If a record's schema predicate fails,** every other claim for that record is `unknown` ("not interpreted"). An unknown schema is never interpreted as the old one.
- **Incidence gains cap-ring checks.** A cap's boundary must be its rim in the documented canonical **clockwise source order** (`A0…A{m−1}` and `B0…`), with `boundary_edges[k] = R?{k}` joining consecutive ring vertices. That is the existing convention, not a new cap orientation.
- **Strict point parsing.** The planar point reader rejects lengths other than 2, instead of reading only the first two elements.
- **Cost note.** The oracle's cost description is corrected to O(V⁴) arithmetic operations.

# Versioning

The claim sets change, so the checkers are registered as **`two_rim.check.source` v2** and **`two_rim.check.material` v2**. v1 is no longer registered. Earlier Stage 2 runs and receipts stay unchanged as history, and replaying their v1 checks is reported as `not_run`.

System's review file is kept verbatim under `review-cases/stage2-review/`. An adapted copy in `tests/` makes one documented mechanical change: checker version `1` becomes `2`.

# Order

1. Add the review cases (verbatim and adapted), the D01 context tests, and the D02 and D03 controls. Run them red against `commit-37`.
2. Add the core context and its tests.
3. Make the checker repairs.
4. Reconcile the docs: DESIGN §5, TWO-RIM-SCHEMA, README.
5. Run the full suite, the review cases, the golden and oracle campaign, and the demo with the complete requirements: source validity, material validity, and correspondence.
6. Write receipts and `STAGE-2-REPAIR-RETURN.md`; push; stop.
