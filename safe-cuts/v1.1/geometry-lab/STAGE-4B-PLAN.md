---
title: Geometry Lab Stage 4B plan - maintained positive-trim ideal-development lane
author: Claude Code session (Claude Opus 5.5), outside the project's agent team
date: 2026-09-29
status: plan, committed before any production edit; implementation follows it; stop after STAGE-4B-RETURN.md
dg-publish: false
---

# Stage 4B plan

## 0. Controlling inputs and starting point

- **Handoff:** `<geometry-lab-project>/SYSTEM-TO-CLAUDE-STAGE-4B-commit-66.md` on `origin/main`, authorization `commit-67` (read with `git show`, main not merged). It supersedes the older commit-62 handoff and the attachment-delivered hold.
- **Read with it:** `reviews/stage4a-recheck-commit-66/REVIEW.md`, `RESULTS.json` and `ADAPTER-NOTE.md`. The older `SYSTEM-TO-CLAUDE-STAGE-4B.md` and main's `reviews/stage4a-repair-commit-62/` were read as history only; their test cases are reused as adversarial cases (§8).
- **Worker branch:** `<private-branch>`, head `commit-66`, equal to its remote, clean worktree. No later worker commits.
- **Scope:** a bounded port of the accepted positive-trim construction into the maintained engine. Not a new geometry framework. **Stop and return for decision** if the port needs a core change, a new dependency or a changed mathematical definition.

## 1. Source pins (what is ported, from which blob)

| Source (branch head `commit-66`) | Git blob | Ported to | How |
|---|---|---|---|
| `probes/stage4a/ratint.py` | `b4f5c150a1ef528d76de02d53c0e228c6b27c183` | `glab/rigorous/ratint.py` | code unchanged; module docstring rewritten; a test compares the module ASTs without docstrings |
| `probes/stage4a/ideal.py` | `de3cae446f2e9a21ac206d34c5e8d333c26dca39` | `glab/check/ideal_geometry.py` | exact model, face checks, Theorem S, enclosure recursion; `Subject`, `load_subject` and Run access are **not** ported (the checker reads ancestors through its context) |
| `probes/stage4a/classify.py` | `c82b587308f5f342703797c0e637097b9f5f5dd2` | `glab/check/ideal_geometry.py` | axis and witness proposals, certification, schedule loop |
| `probes/stage4a/binding.py` | `8f76e87a4d5659a41a34b22957c57ef67b9b2af0` | `glab/two_rim/ideal_search.py` | the prerequisite rule (complete claim sets on actual subjects, current evidence, expected checker identity) |
| `probes/stage4a/recheck_mpmath.py` (accepted: A03, R01, R02) | `cb483479bae2bf18896547b9fd42c53c7e61ebc2` | `tests/two_rim_ideal_recheck/recheck_ideal_mpmath.py` | committed verbatim first, then its binding layer adapted to maintained records (§8), so the adaptation is one reviewable diff |
| `STAGE-4A-DESIGN.md` §2.2, §2.3, §4, §5.4 (L1, L2, `D`, Theorem S, certificates) | `d06000f8818d8699c69e8ca01241951272aedbca` | `IDEAL-DEVELOPMENT-CONTRACT.md` | text carried with its pin |
| `probes/stage4a/L4-CORRESPONDENCE.md` (accepted) | `ed135840e9e2c7c2e26e42b0201142271c5de871` | referenced by blob from `IDEAL-DEVELOPMENT-CONTRACT.md` | kept where it is, unchanged |

Unchanged prototype functions are verified mechanically: a test compares the AST of each ported function with the prototype function of the same name, and lists the functions that were deliberately adapted. `PROVENANCE-STAGE-4B.json` records every pin above and the LF-normalized SHA-256 of every new file that affects arithmetic or claim semantics.

## 2. Module layout (all new; no existing file is edited)

| File | Role | Imports allowed |
|---|---|---|
| `glab/rigorous/__init__.py`, `glab/rigorous/ratint.py` | outward rational intervals, verified `isqrt` root bounds | standard library only |
| `glab/two_rim/ideal.py` | generator side: builds the `two_rim.ideal_trim/1` payload; no numeric work | `glab.core.numbers` |
| `glab/two_rim/ideal_actions.py` | registers `two_rim.ideal.define` v1 | core registry |
| `glab/check/ideal_geometry.py` | checker side: exact model, local premises, Theorem S, enclosures, certificates | `glab.rigorous`, `glab.core.numbers`; **never** `glab.two_rim`, never NumPy |
| `glab/check/two_rim_ideal.py` | contextual checker `two_rim.check.ideal_trimmed_development` v1, its claims and policy | as above plus core registry/runfile |
| `glab/two_rim/ideal_search.py` | separate entry point `ideal_candidate_search` and the aggregate `source_linked_ideal_trimmed_obligations` | core only (claim names are literals, kept in step by tests, as in `search.py`) |
| `IDEAL-DEVELOPMENT-CONTRACT.md` | maintained explanatory contract (§7) | |
| `TWO-RIM-IDEAL-SCHEMA.md` | state, action, claims, policy and aggregate contract | |
| `PROVENANCE-STAGE-4B.json` | source pins and file hashes | |
| `tests/two_rim_ideal/` | maintained tests (maintained `.venv`) | |
| `tests/two_rim_ideal_recheck/` | test-side re-checker copy and its tests; need mpmath, so they run in the throwaway review environment and skip elsewhere | |
| `receipts/stage4b/` | red and green logs, scan results, re-check reports, environment | |

Registration is additive: `register_ideal_actions(registry)` and `register_ideal_checkers(registry)`. Nothing registers itself; the existing `register_*` functions, `search.py`, the float checkers and `glab/core/` are not touched.

## 3. State and action

**State** `two_rim.ideal_trimmed_development`, representation `exact`, payload schema `two_rim.ideal_trim/1`:

```json
{"schema": "two_rim.ideal_trim/1",
 "definition": "two_rim.ideal_development/1",
 "delta": "1/10000",
 "orientation": "outward: each face map preserves orientation with respect to that face's outward normal",
 "normalization": "N0: first chain face's entry-hinge low trim point at (0, 0); that hinge along +x",
 "cut": {"<exact copy of the parent two_rim.cut/1 payload>": "..."}}
```

- `exact` means an exact input and definition. It does not say the real image coordinates are rational.
- The **parent is the cut**, never a float state. The payload holds no derived coordinates.
- The orientation and normalization strings are the prototype's literals, unchanged.
- **Naming decision:** `two_rim.ideal_development/1` names the maintained contract's copy of the Stage 4A definition `stage4a.ideal_development/1`. The mathematics is unchanged. This is a flagged decision, not a new definition.

**Action** `two_rim.ideal.define` v1: accepts `two_rim.cut`, parameter `delta` (`Param.exact`). It refuses, with no state created:
- a non-canonical spelling (`"2/8"`, `" 1/4"`, `"0.25"`)
- a value outside `0 < delta < 1/2`
- a cut payload with an unsupported schema

Floats, booleans and `null` are already rejected by `Param.exact`. The action copies the cut payload and does no geometry.

## 4. Checker: `two_rim.check.ideal_trimmed_development` v1

- **Declaration:** contextual (`uses_context=True`), accepts `two_rim.ideal_trimmed_development`, no parameters.
- **Reconstruction:** from the **actual** ancestors: parent `two_rim.cut`, grandparent `two_rim.material`. The chain is re-derived from the material's hinge order and the actual cut's seam; the cut's recorded `face_order` must equal it.
- **Never trusted:** no model object, cached flag or earlier evidence.

| # | Claim | Method / domain | Coverage | Declares | Outcome rule |
|---|---|---|---|---|---|
| 1 | `two_rim.ideal.record_schema` | `exact_computation` / `exact_rational` | `all` | none | pass iff the exact key set, schema, definition, orientation and normalization literals, a canonical exact `delta` string, and an object `cut` |
| 2 | `two_rim.ideal.cut_copy_matches_parent` | exact | `all` | none | pass iff the payload's cut equals the parent cut, and the parent cut's material equals the grandparent material |
| 3 | `two_rim.ideal.delta_in_supported_domain` | exact | `all` | none | pass iff `0 < delta < 1/2` |
| 4 | `two_rim.ideal.local_premises` | exact | `all` | none | the exact premises the construction and certificates use (list below). Receipt: per-face checks and coded problems |
| 5 | `two_rim.ideal.retained_hinge_sides_opposite` | exact | `retained_hinge_pairs` | none | per consecutive pair, S1–S4 and the exact side values `σ`; pass iff every retained pair has opposite closed sides with strict values. `fail` here is an exact statement about the side test, never an overlap |
| 6 | `two_rim.ideal.retained_neighbours_interiors_disjoint` | exact / `exact_rational` | `retained_hinge_pairs` | `IDEAL_POLICY` | the **Theorem S inference**, applied to claims 4 and 5. Pass iff both hold for every retained pair; otherwise unknown. **Never** `fail`. Receipt names the pinned L1/L2/S dependency |
| 7 | `two_rim.ideal.remaining_pairs_interiors_disjoint` | `rigorous_enclosure` / `rational_interval` | `pairs_not_decided_by_theorem_s` | `IDEAL_POLICY` | every other pair on the schedule: fail if any certified interior witness; pass if every pair has a certified separating axis; otherwise unknown |
| 8 | `two_rim.ideal.pair_coverage_complete` | exact | `all` | none | pass iff claims 6 and 7 partition the unordered chain pairs, each pair decided in exactly one place |

**Local premises (claim 4).** Codes follow the re-checker's R02 codes:
- `number_domain` `exact_rational` and canonical exact coordinates
- unique IDs and existing references
- chain and incidence: every hinge is the entry of one face and the exit of one face, and each ring holds its hinge endpoints
- nondegenerate hinges and nonzero normals
- every ring vertex and hinge endpoint exactly on the stated plane
- outward orientation: every material vertex satisfies `n·v ≤ d`
- trimmed rings strictly convex and counterclockwise about `n`

**Unsupported input is not an overlap.**
- If claim 1 fails, nothing else is interpreted: every later claim is `unknown`.
- If the ancestors are not a cut and a material (possible only in a tampered loaded run), claim 2 fails and the geometric claims are `unknown`.
- If claim 3 or claim 4 fails, claims 5–8 are `unknown`, with the reason `unsupported input`.

**Self-check of every reported bound.** Before a certificate is recorded, the checker re-verifies it exactly on the recorded boxes:
- the axis gap is recomputed;
- the Euclidean bound `b` must satisfy `b ≥ 0` and `b²(d·d) ≤ g²`;
- the witness bound `b` must satisfy `0 < b ≤ m`, with `m` recomputed by an independent code path.

A row that fails this becomes `unknown` (`certificate_self_check_failed`), never pass or fail.

**Claim 7 receipt.**
- Per pair: positions, method, outcome, the certificate, the deciding precision, and every attempt `{bits, outcome}`.
- The boxes and square-root records **at every precision used by a decision**, so each certificate is re-checkable against the boxes it used.
- The counts, and the lists of checked fields and diagnostic fields.

**Revision.** `source_revision` over `check/two_rim_ideal.py`, `check/ideal_geometry.py` and `rigorous/ratint.py`: every file that affects the arithmetic or the claim semantics.

## 5. Policy (instance-independent)

`IDEAL_POLICY`, declared in `Claim.tolerances` by claims 6 and 7:

- **Policy id:** `two_rim.ideal.evidence/1`
- **Subject:** `D` of the `two_rim.ideal_trim/1` state only
- **Arithmetic:** exact `Fraction` endpoints; `+ − ×` exact; the reciprocal refused on intervals containing zero
- **Root rule:** `isqrt` with exact re-check of `lo² ≤ a ≤ hi²`
- **Rounding:** absolute outward rounding to `2^-P` for intervals that have width; zero-width values kept exact
- **Schedule:** `16, 32, 64, 128, 256, 512`, stopping at the first decision
- **Budget and exhaustion:** after the last precision, `unknown` with `budget_exhausted`; errors give `unknown` with `error:<kind>`
- **Decision rules:** pass on a certified separating axis; fail on a certified interior witness; otherwise unknown
- **Trusted base:** CPython `int`, `fractions.Fraction`, `math.isqrt`, `glab.rigorous.ratint`
- **Analytic dependencies:**
  - the lemmas L1, L2, Theorem S and the §5.4 separation and witness lemmas
  - `IDEAL-DEVELOPMENT-CONTRACT.md`, pinned by its LF SHA-256, with its source blobs `d06000f8` and `ed135840`
  - status: reviewed written derivations, not machine-checked, not Lean, not human peer review

The exact premise claims declare no policy, as the existing exact claims do. `formal_proof` is not used anywhere.

## 6. Aggregate and verdict (separate entry point)

`ideal_candidate_search(run, material_hash, delta, *, expected_policy)`:
- **Per original hinge:** `two_rim.cut.open` v1, then `two_rim.ideal.define` v1.
- **Checkers run:** source v2 and material v2 once; cut v1 and the ideal checker v1 per seam.
- **Evaluation:** `ideal_obligations(...)` then evaluates each seam from evidence only.
- **Float search:** `enumerated_candidate_search` and its float totals are not changed or called.

**`source_linked_ideal_trimmed_obligations`**, conservative (fail > unknown > not_run > pass), over:
- `two_rim.check.source` v2: all four source claims on the material's parent
- `two_rim.check.material` v2: all five material claims, including `matches_parent_source`
- `two_rim.check.cut` v1: all five cut claims
- `two_rim.check.ideal_trimmed_development` v1: all eight ideal claims

Each requirement fixes:
- the subject hash, method and coverage token;
- `expected_tolerances` of `None` for exact claims and `expected_policy` for claims 6 and 7;
- the producing checker's name and version: every covering evidence ID is resolved and checked, as A02 did.

Only current evidence counts, so a stale revision, changed policy, missing claim or wrong checker gives no pass.

**Geometric verdict on `D`**, reported separately as `ideal_geometric_verdict`:
- `not_determined`: any prerequisite or any claim other than 6 and 7 is not a current `pass` with the expected identity and policy. This covers absent, stale or failing prerequisites and unsupported input. **No source-linked geometric verdict is made.**
- `fail`: claim 7 is `fail`, meaning a certified interior witness, with all non-pair obligations passing.
- `pass`: claims 6 and 7 both `pass`.
- `unknown`: otherwise. Never a safety pass.

`expected_policy` is a required argument: the aggregate is always held to a stated policy.

## 7. Maintained explanatory contract (`IDEAL-DEVELOPMENT-CONTRACT.md`)

- **Carried text:** the definition of `D`, L1, L2, Theorem S and the §5.4 certificate lemmas, with the design blob pin.
- **L4 by blob** `ed135840e9e2c7c2e26e42b0201142271c5de871`, with its accepted points restated:
  - the common trim-dependent translation `τ_δ(y) = y − (δ‖G_k‖, 0)`
  - chain position `j` distinct from cyclic face index `k+j`
  - a pass at `δ₀` carries to more-trimmed `δ₀ ≤ δ < 1/2` only, by restriction
- **Described as** reviewed written dependencies: not Lean results, not machine-checked, not human peer review.
- **Limit:** no universal theorem, full or untrimmed safety, or continuous-motion claim follows from the finite scan.

## 8. Portable re-check (test-side)

1. **Verbatim copy.** Copy the accepted re-checker (`cb483479`) to `tests/two_rim_ideal_recheck/recheck_ideal_mpmath.py` and commit it byte-identical.
2. **Bundle.** A test-side exporter writes `two_rim.ideal.recheck_bundle/1`:
   - the source, material, cut and ideal state records;
   - per seam, the ideal state hash and the ideal checker's evidence records.
3. **Adapt only the binding layer.**
   - State hashes, kinds and the parent chain ideal → cut → material → source are checked.
   - So are the ideal payload's constants, domain and cut copy, the cut's seam and material copy, and the material identity.
   - Evidence records must name the ideal subject, its dependency chain and checker `two_rim.check.ideal_trimmed_development` v1, with each ideal claim exactly once.
   - The claim receipts are turned into the rows and per-precision boxes that the unchanged verification core checks: R02 local geometry first, then shape and coverage, containment, Theorem S, axes, witnesses, and the R01 bounds.
   - The declared claim outcomes must equal the recomputed ones.
4. **Report scope.** Local geometric hypotheses and recorded bounds are checked. The structural binding of the evidence records is checked, but Run provenance and Stage 2 source correspondence are not re-proved. A containment failure means **not confirmed**, not by itself proof that the recorded enclosure is invalid. `verified` is not a safety statement.
5. **Tests.**
   - Fresh maintained bundles, all 11 E11 seams and the square prism, must verify.
   - The existing adversarial cases are ported to the new format: A03 single faults, R01 bound inflations and malformed bounds, R02 rehashed bad geometry, System's B01 and acceptance cases, the honest-unknown case, and the CLI exit codes.
   - The verbatim copy's red run on the new bundle is kept.
6. **Environment.** The throwaway review environment only (mpmath 1.3.0, RECORD re-verified before use). Nothing is installed in the maintained `.venv`.

## 9. Obligation-to-test mapping (handoff §4)

| Handoff obligation | Tests (all new) |
|---|---|
| exact square/prism, non-dyadic values, positive near-boundary trims | `test_prism_exact.py`: SQUARE at δ = 1/4, 1/3, 1/10000, 10⁻³⁰, 1/2 − 10⁻³⁰; a prism with non-dyadic coordinates and height; every box zero-width; all seams pass |
| E11: 605 pairs, 7 pass / 4 fail, F10/F7 at E9 | `test_e11_ideal.py`: counts 110 / 484 / 11; verdicts E0–E2, E4–E7 pass, E3, E8, E9, E10 fail; the F10/F7 witness; rows identical to the prototype's certificates (port equivalence); comparison with the mapped historical classes after classification |
| low precision, zero denominators, budget exhaustion, honest unknowns | `test_classification_controls.py` (C1–C5 ported: four-way signs, `zero_denominator`, sqrt bounds, `unknown` at 2 and 4 bits then decided, `budget_exhausted`); claim-level unknowns through the claim assembly and a test registry |
| source/cut/model substitutions, stale or missing prerequisites, wrong checker identity, nested mutation | `test_aggregate_prerequisites.py`, `test_state_mutations.py`: another seam's or material's cut copy, a mutated nested coordinate, missing source or material checks, a stale checker revision, a fake checker emitting the right claim names, a policy mismatch |
| schema/domain/coordinate conventions before interpretation | `test_define_and_schema.py`: refused deltas; wrong schema, definition, orientation, normalization; extra keys; float parents rejected; later claims `unknown` |
| pair/box coverage, nonzero axes, method/outcome, quantitative bounds, invalid plane/hinge data | `test_checker_claims.py` (claims 4–8 and self-checks) and the re-check tests (bundle level) |
| save/load/replay with policy and revision checks, mismatches rejected | `test_replay_policy.py`: `reproduced`; another checker revision gives `not_run`; another policy gives `policy_mismatch` and no pass |
| unchanged float mutation controls; no transfer ideal → float | the inherited suite unchanged; `test_firewall.py`: float totals and the seven float `unknown`s unchanged; no ideal evidence on float hashes; the action and checker refuse float states |
| separate re-check of fresh bundles and existing adversarial cases | `tests/two_rim_ideal_recheck/` (review environment) |
| repeated serialized results, timing separate | `test_receipt_determinism.py`; the receipt script run twice, byte-identical except `timing.json` |

## 10. Order of work (tests before each step)

Each step commits its tests and the red log first, then the implementation and the green log.
- **Red logs** separate collection or import failures from exercised assertions.
- **Test changes** after a red run are disclosed in the return.

1. **Arithmetic:** `test_ratint.py`, then `glab/rigorous/ratint.py`.
2. **Lane:**
   - tests: define/schema, prism, E11, controls, claims, mutations, provenance;
   - with them: `IDEAL-DEVELOPMENT-CONTRACT.md` and `TWO-RIM-IDEAL-SCHEMA.md`, since the policy pins the contract;
   - then `ideal.py`, `ideal_actions.py`, `ideal_geometry.py` and `two_rim_ideal.py`.
3. **Aggregate and firewall:** aggregate, firewall, replay and determinism tests, then `ideal_search.py`.
4. **Re-check:**
   - the verbatim copy and its tests, with the red run on the new bundle;
   - then the binding-layer adaptation.
5. **Receipts:**
   - inherited suite (411) and new maintained tests;
   - prototype controls (99), targets (7), A01/A02 (36);
   - review-environment suites (63 prior plus the new re-check tests);
   - receipt script twice, re-check of the fresh bundle, environment and RECORD audit.
6. **Return:** `STAGE-4B-RETURN.md`, then stop.

## 11. Decisions flagged for System

1. The definition identifier `two_rim.ideal_development/1` for the unchanged Stage 4A definition (§3).
2. One policy object for both the Theorem S inference claim and the enclosure claim. It carries both the arithmetic trusted base and the pinned analytic dependencies (§5).
3. The separate `pair_coverage_complete` claim, and the `not_determined` verdict for unsupported input and absent or failing prerequisites (§4, §6).
4. `retained_hinge_sides_opposite` may be `fail` as an exact statement. The inference claim never fails (§4).
5. The re-check exporter is test-side. The re-checker copy is adapted only in its binding layer (§8).
6. The checker self-checks every reported bound at issuance, in addition to the re-checker's R01 comparisons (§4).

## 12. Not in this stage

- Core changes, new dependencies, a changed definition; relative rounding or performance redesign.
- Motion, untrimmed glued vertices, caps, proof-guided selection; Lean, CGAL or FOLD; viewer expansion.
- Publishing, website or research-publishing 0.4 work.
- Merge, PR, release, deployment, external contact, purchases, scheduler changes, new agents.
- Kept unchanged: `probes/stage4a/`, all previous returns, plans, receipts, reviews and fixtures, the assessment, manuscript and frozen Lean.
