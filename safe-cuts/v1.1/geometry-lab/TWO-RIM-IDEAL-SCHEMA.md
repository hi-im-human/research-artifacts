---
title: Two-rim ideal-development schema (Stage 4B)
author: Claude Code session (Claude Opus 5.5), outside the project's agent team
date: 2026-09-29
status: Stage 4B contract for the positive-trim ideal lane; separate from the float development lane
dg-publish: false
---

# Two-rim ideal-development lane

The lane names the ideal trimmed development `D` (mathematics: `IDEAL-DEVELOPMENT-CONTRACT.md`) as a Run state, checks it with an independent contextual checker, and aggregates it with the Stage 2 and cut evidence. It never reads, changes or relabels a float `two_rim.development` or `two_rim.trimmed_development` state.

## State

| Kind | Representation | Parent | Payload schema |
|---|---|---|---|
| `two_rim.ideal_trimmed_development` | `exact` (exact inputs and definition; the image coordinates of `D` are not claimed rational) | a `two_rim.cut`, never a float state | `two_rim.ideal_trim/1` |

```json
{"schema": "two_rim.ideal_trim/1",
 "definition": "two_rim.ideal_development/1",
 "delta": "1/10000",
 "orientation": "outward: each face map preserves orientation with respect to that face's outward normal",
 "normalization": "N0: first chain face's entry-hinge low trim point at (0, 0); that hinge along +x",
 "cut": {"<exact copy of the parent two_rim.cut/1 payload>": "..."}}
```

- `delta` is a canonical exact string (`"n/d"` in lowest terms, or `"n"`) with `0 < delta < 1/2`.
- `definition` `two_rim.ideal_development/1` is the Stage 4A definition `stage4a.ideal_development/1`, unchanged.
- The orientation and normalization strings are the only supported values.
- No derived data (chain, trim points, maps, boxes) is stored. The checker reconstructs everything from the actual ancestors.

## Action `two_rim.ideal.define` v1

- **Accepts:** `two_rim.cut`. **Parameter:** `delta` (`Param.exact`). **Module:** `glab/two_rim/ideal_actions.py` (standard library and `glab.core` only). **Revision:** `source_revision` of that module.
- **Refuses, with no state created:**
  - a non-canonical spelling (`"2/8"`, `" 1/4"`, `"0.25"`, `"1e-4"`), a value outside `0 < delta < 1/2`, or an integer (execution failure);
  - a float, boolean or `null` (rejected by parameter validation);
  - a parent that is not a cut (rejected by the core's `accepts`).
- Does no geometry.

## Checker `two_rim.check.ideal_trimmed_development` v1

- **Module:** `glab/ideal_check/checker.py`, with geometry in `glab/ideal_check/geometry.py` and arithmetic in `glab/rigorous/ratint.py`. The package lives outside `glab/check` because the inherited boundary tests keep every `glab/check` module to the standard library and `glab.core`; this checker also needs the shared arithmetic. It never imports the generator package `two_rim` and never uses NumPy.
- **Declaration:** contextual (`uses_context=True`), accepts `two_rim.ideal_trimmed_development`, no parameters.
- **Revision:** `source_revision` over `ideal_check/checker.py`, `ideal_check/geometry.py` and `rigorous/ratint.py`.
- **Reconstruction:** from the actual parent cut and grandparent material (`DependencyContext`). The chain is re-derived from the material's hinge order and the cut's seam.

| # | Claim | Method | Numeric domain | Coverage | Tolerances | Outcome |
|---|---|---|---|---|---|---|
| 1 | `two_rim.ideal.record_schema` | `exact_computation` | `exact_rational` | `all` | none | exact key set; supported schema, definition, orientation, normalization; canonical `delta`; object `cut` |
| 2 | `two_rim.ideal.cut_copy_matches_parent` | `exact_computation` | `exact_rational` | `all` | none | carried cut = parent cut, and that cut's material = its parent material |
| 3 | `two_rim.ideal.delta_in_supported_domain` | `exact_computation` | `exact_rational` | `all` | none | `0 < delta < 1/2` |
| 4 | `two_rim.ideal.local_premises` | `exact_computation` | `exact_rational` | `all` | none | coded exact premises (below) |
| 5 | `two_rim.ideal.retained_hinge_sides_opposite` | `exact_computation` | `exact_rational` | `retained_hinge_pairs` | none | S1–S4 and the side values `σ` on every retained hinge; `fail` is an exact statement about the side test, never an overlap |
| 6 | `two_rim.ideal.retained_neighbours_interiors_disjoint` | `exact_computation` | `exact_rational` | `retained_hinge_pairs` | `IDEAL_POLICY` | Theorem S applied to claims 4 and 5; names the pinned analytic dependency; `pass` or `unknown`, never `fail` |
| 7 | `two_rim.ideal.remaining_pairs_interiors_disjoint` | `rigorous_enclosure` | `rational_interval` | `pairs_not_decided_by_theorem_s` | `IDEAL_POLICY` | every other pair: `fail` if a certified interior witness, `pass` if every pair has a certified separating axis (always a nonzero rational axis), else `unknown` |
| 8 | `two_rim.ideal.pair_coverage_complete` | `exact_computation` | `exact_rational` | `all` | none | claims 6 and 7 partition the unordered chain pairs |

**Local premises (claim 4)**, each failure with a code:
- `number_domain`: the material's `number_domain` is `exact_rational`;
- `noncanonical_number`: coordinates are canonical exact strings;
- `identity_ambiguous`, `reference_missing`: unique IDs, existing references;
- `incidence`, `chain`: every hinge is the entry of one face and the exit of one face; the chain continues from the seam and equals the cut's `face_order`; each ring holds its hinge endpoints;
- `hinge_degenerate`, `normal_zero`, `plane_shape`;
- `ring_not_on_plane`: every ring vertex and hinge endpoint exactly on the stated plane;
- `orientation_not_outward`: every material vertex satisfies `n·v ≤ d`;
- `trimmed_ring_not_convex_ccw`: every trimmed ring strictly convex and counterclockwise about `n`.

**Order of interpretation.**
- If claim 1 fails, nothing is interpreted: claims 2–8 are `unknown`.
- If the ancestors are not an exact cut and material, claim 2 fails and claims 4–8 are `unknown`.
- If claim 3 fails, claims 4–8 are `unknown` (`unsupported input`); if claim 4 fails, claims 5–8 are `unknown`.
- Unsupported input is never an overlap.

**Self-check.** Before a certificate is recorded, the checker re-verifies it exactly on the boxes it used: nonzero axis, supported order, `axis_gap` recomputed, `euclidean_gap_lower_bound` `b ≥ 0` with `b²(d·d) ≤ axis_gap²`; for a witness, exact convexity and orientation and `0 < cross_lower_bound ≤` the recomputed smallest bound. A row that fails becomes `unknown` (`certificate_self_check_failed`), with the rejected certificate as a diagnostic.

**Claim 7 receipt.**
- `rows`: per pair `pair`, `positions`, `method`, `outcome`, `certificate`, `bits` (the deciding precision) and `attempts`.
- `enclosures`: the boxes and square-root records at every precision used by a decision, so each certificate is re-checkable against the boxes it used.
- `checked_fields` and `diagnostic_fields`: the diagnostics are `attempts`, `reason`, a `shared_hinge` record on a retained pair routed to intervals, and `self_check_rejected`.
- Summaries: `counts`, `attempted_precisions`, `enclosure_errors`, `max_bits_needed`, `self_check`.

## Policy `IDEAL_POLICY` (`two_rim.ideal.evidence/1`)

Instance-independent; declared in `Claim.tolerances` by claims 6 and 7 (the exact claims declare none):
- arithmetic: exact rational interval endpoints; the reciprocal of an interval containing 0 is refused (`zero_denominator`);
- root rule: verified `isqrt` bounds, `lo² ≤ a ≤ hi²` re-checked exactly;
- rounding: absolute outward rounding to `2^-P` of intervals that have width; zero-width values kept exact;
- precision schedule `16, 32, 64, 128, 256, 512`, stopping at the first decision; `budget_exhausted` or `error:<kind>` give `unknown`;
- decision rules, reported-bound rules and the trusted base;
- `analytic_dependencies`: `IDEAL-DEVELOPMENT-CONTRACT.md` pinned by LF SHA-256, with source blobs `bb32b132` (design, export copy) and `e60cb7f1` (L4, export copy); reviewed written derivations, not machine-checked, not Lean results, not human peer review.
  The pin is a literal hash in the checker's code, kept consistent with the file by a test (`test_the_explanatory_contract_is_pinned_by_the_policy`). It is not automatic runtime invalidation: editing the Markdown alone does not change the code's policy; a text revision must update the hash pin, the checker revision and `PROVENANCE-STAGE-4B.json` together, keep the old text in Git and record the revision.

A different schedule is a different policy: evidence under it is a `policy_mismatch` against `IDEAL_POLICY`.

## Aggregate and verdict (`glab/two_rim/ideal_search.py`)

`ideal_candidate_search(run, material, delta, *, expected_policy, seams=None)` is a separate entry point. `enumerated_candidate_search` and its float totals are unchanged and are not called. Per seam it opens the cut, defines the ideal state, runs the cut and ideal checkers (source and material once), and evaluates `ideal_obligations(run, ideal, *, expected_policy)`; `loaded_ideal_obligations(loaded, registry, ideal, *, expected_policy)` evaluates a loaded run file against a given registry.

**`source_linked_ideal_trimmed_obligations`** (conservative: fail > unknown > not_run > pass) requires, on the actual subject hashes along ideal → cut → material → source:
- `two_rim.check.source` v2: 4 claims; `two_rim.check.material` v2: 5 claims including `matches_parent_source`; `two_rim.check.cut` v1: 5 claims; the ideal checker v1: 8 claims;
- current evidence, parameters `{}`, the expected method and coverage;
- no policy on exact claims, and exactly `expected_policy` on claims 6 and 7;
- every covering evidence record from the expected checker name and version.

**`ideal_geometric_verdict`:**

| Verdict | Meaning |
|---|---|
| `pass` | every pair of `D` certified disjoint, with complete current source-linked evidence under the expected policy |
| `fail` | a certified interior witness, with every non-pair obligation current and passing |
| `unknown` | valid current evidence that leaves a pair undecided; never a safety pass |
| `not_determined` | required evidence missing, stale, failing, foreign or under another policy, or the input unsupported; never an overlap and never a pass |

## Portable re-check (test-side)

`tests/two_rim_ideal_recheck/`: the accepted Stage 4A re-checker (blob `cb483479`: A03, R01, R02), copied verbatim and then adapted only in its binding layer to the bundle schema `two_rim.ideal.recheck_bundle/1` (stored states along ideal → cut → material → source, plus the ideal checker's evidence). It needs mpmath and runs only in the throwaway review environment. Its report separates certificate verification from the recomputed verdict on `D`. A containment failure means **not confirmed**, not proof that the recorded enclosure is invalid: exact non-dyadic zero-width boxes, for example, cannot contain a binary interval of positive width.

Since the Stage 4B repair (I01, I02): a record whose interval rows are all `unknown` asserts no enclosure and is checkable without precision levels (its verdict is `unknown`, never `pass`), while a decided row must still name a recorded level; and every supplied side record and the Theorem S partition (`decided_pairs`, `undecided_pairs`) are validated as supplied (shape, retained-pair membership, uniqueness, coverage, disjointness and agreement with the side outcomes) before any row is confirmed.
