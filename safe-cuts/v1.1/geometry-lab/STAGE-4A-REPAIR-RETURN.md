---
title: Geometry Lab Stage 4A repair return (A01-A03 and the written L4 correspondence)
status: A01-A03 repaired; L4 bridge written for review; stopped; Stage 4B held
dg-publish: false
---

# Stage 4A repair return: A01–A03 and the written L4 correspondence

**From:** Claude Code session (Claude Opus 5.5), outside the project's agent team. I wrote the probe, these repairs and the L4 note, so I am their implementer, not an independent reviewer.

**Assignment:** System's review `<geometry-lab-project>/reviews/stage4a-review/`: `REVIEW.md`, `RESULTS.json`, `test_stage4a_review.py`, `ADAPTER-NOTE.md`. Authorization `commit-58`. All read from `origin/main` without merging.

## Where it is

- **Repository:** `<private-repo>`
- **Branch:** `<private-branch>`
- **Reviewed head:** `commit-57`. There were no later worker commits, and the worktree was clean.
- **Commits:**
  - `commit-59`: repair plan (`STAGE-4A-REPAIR-PLAN.md`), System's review file **verbatim**, and the reproduction at `commit-57`
  - `commit-60`: tests first (A01, A02, A03, and the adapted review copy), with red runs
  - `commit-61`: the A01–A03 implementation, `L4-CORRESPONDENCE.md`, and repair receipts
  - the commit that adds this file
- **Write scope,** checked: only `STAGE-4A-REPAIR-PLAN.md`, this file, and `engine/probes/stage4a/` changed since `commit-57`.
- **Unchanged:** the original Stage 4A design and return, every earlier receipt (the original `receipts/controls`, `results` and `recheck`, and the logs), `glab/`, `tests/`, the manuscript, proofs, reviews and the assessment.
- **Not done:** no registry, core or action-context change; nothing installed into the maintained `.venv`.
- **Review file:** copied to `probes/stage4a/review-cases/stage4a-review/test_stage4a_review.py`. Its blob `9b141bce2f6c9a937455bb5349cc1bf26d3a0d66` equals `origin/main`'s.

## Environments

- **Maintained `.venv`, used read-only:** Python 3.11.9, numpy 2.4.4, pytest 9.1.1. It runs the controls, targets, A01/A02 tests and the inherited suite.
- **Throwaway review environment** (`receipts/repair/review-environment.json`). System's review file imports the mpmath re-checker, which the maintained `.venv` lacks, so this runs the review cases and the A03 tests.
  - It lives in the scratchpad, outside the repository, and was built without network access.
  - It holds the maintained `.venv`'s pinned numpy, pytest and their dependencies, plus mpmath 1.3.0 from the Python 3.11 user site.
  - Every present file verified against its `RECORD` hash with **no mismatches**. The only absent entries are five console-script `.exe` launchers and one numpy `.pyc`, all deliberately not copied.
  - It runs with `-B` and `PYTEST_DISABLE_PLUGIN_AUTOLOAD=1`.
- **Throwaway re-check environment** (the same one as in Stage 4A; `receipts/repair/recheck/environment.json`): mpmath 1.3.0 only, 92 files verified against `RECORD`, no bytecode, run with `-I -B`.

## Execution record

| Run | Result | Receipt (`probes/stage4a/receipts/repair/`) |
|---|---|---|
| System's review file verbatim, at `commit-57`, before any change | **4 passed, 11 failed**, the same as the review | `red-review-at-commit-57.log` |
| Tests first, maintained environment | 2 **collection errors**: the A01 and A02 modules import names that did not exist yet, so **no A01/A02 assertion ran** | `red-repair-tests-maintained-env.log` |
| Tests first, review environment | 36 failed, 4 passed. Classified by each failure's exception: 22 are `KeyError`s on report fields that did not exist yet (not substantive), 12 are genuine assertion failures, 1 is a `ValueError` and 1 an `AttributeError`. The 4 passes are the adapted controls. | `red-review-env-tests.log` |
| A01/A02 repair tests | **36 passed** | `repair-tests-a01-a02.log` |
| A03 contract tests and the adapted review copy (review environment) | **41 passed** (26 + 15) | `review-env-tests.log` |
| System's review file verbatim, after repair | **14 passed, 1 failed** (see "Adapter") | `review-verbatim-after-repair.log` |
| Stage 4A controls C1–C7, after repair | 99 passed | `controls-after-repair.log` |
| Targets (T1–T3, prism, scan, historical reference), after repair | 7 passed | `targets-after-repair.log` |
| Inherited worker suite | **411 passed**; the float64 mutation controls are unchanged | `inherited-suite.log` |
| Probe run with the bound v2 bundle | 11 seams, byte-identical across two runs apart from `timing.json`; committed blobs match `MANIFEST.json` (7 of 7) | `results/`, `run-probe-stdout.log` |
| Hardened independent re-check of all 11 seams | **exit code 0, `verified`**. 11/11 seams verified; 605/605 pair rows; 968/968 coordinates contained; 110/110 Theorem S rows; 484/484 axes; 11/11 witnesses; 0 unknown rows; 0 failures. | `recheck/recheck.json`, `recheck/recheck-stdout.log` |

**Verdicts on `D` are unchanged by the repairs.** At δ = 1/10000, E0, E1, E2 and E4–E7 `pass`; E3, E8, E9 and E10 `fail`. All eleven are **source-linked**, computed from actual Run evidence. Every pair is decided by 64 bits.

**Test edits after the tests-first commit** (`git diff commit-60 commit-61 -- probes/stage4a/tests`):
1. **The A01 inward-plane control.** It negated a face plane *after* the builder had computed the material identity. That makes the record internally inconsistent, and the correct result is a **binding** refusal, which the test did not anticipate. The control now recomputes the identity, so it isolates the face precondition (outward normal). A **new** test covers the stale-identity case, which gives a `subject_binding` refusal.
2. **A new A03 test** shows that a bundle in the old layout is rejected with exactly one reason, `bundle_schema`.
3. **A new `tests/review_env/conftest.py`.** It skips that directory explicitly when mpmath is absent, instead of failing at import.

## A01: the domain and the preconditions

- **Domain.** `require_supported_delta` makes `load_subject` refuse δ before any `D` exists, raising `UnsupportedSubject`, a `ValueError`. It refuses δ outside `0 < δ < 1/2`, non-canonical spellings (`"2/4"`, `" 1/4"`, `"0.25"`), floats, bools and `None`.
- **Checks at issuance.** `ideal_certificate` calls `binding.bind`, which re-checks δ and then the preconditions (`ideal.preconditions`):
  - the chain is the face cycle opened at the seam
  - for every face: nonzero normal; ring on its plane; **outward normal** (every material vertex satisfies `n·v ≤ d`); nondegenerate hinges lying in the plane; trimmed ring strictly convex and counterclockwise
- **Refusals.** A failure gives a **structured refusal**: `status: "refused"`, `seam_verdict: "refused"`, `refusal.kind: "unsupported_subject"` with the problems listed, and no classification. A refusal is never an overlap `fail`.
- **Tests:**
  - the five δ cases, plus two more out-of-domain and six non-canonical values
  - δ altered after construction, bypassing the frozen object, with a consistent ID: refused at issuance
  - an inward face plane, and a scrambled chain: refused
  - a faulty-builder Run with no mutation: issued `pass`
  - valid near-boundary controls, all issued: δ = 10⁻³⁰ and δ = 1/2 − 10⁻³⁰ on the square (`pass`, exact), and δ = 1/2 − 10⁻³⁰ on E11 E9 (an honest verdict)
  - low-level `classify_seam` still works at δ = 1/2, but produces no certificate fields

## A02: calculation and evidence bound to the subject at use time

**Immutable objects.**
- `Subject` and `ExactModel` are frozen dataclasses.
- Nested maps are `FrozenDict` (a `dict` subclass that refuses mutation, so JSON still works), and sequences are tuples.
- Assigning a field raises `FrozenInstanceError`. Nested mutation raises `TypeError`.

**`bind(subject)` at issuance.** It trusts nothing the caller carries. It:
1. recomputes `id = content_hash(spec)`;
2. checks the fixed definitions;
3. reads the three named states and verifies their **content hashes**, kinds, parent links, material identity (recomputed), cut seam and material copy;
4. **rebuilds** the model from those states and compares it with the carried model. A mismatch gives `subject_model_mismatch`.

**Prerequisites** (`binding.prerequisite_status`):
- the complete expected claim sets on the actual subject hashes (source v2 × 4 claims, material v2 × 5, cut v1 × 5);
- summarized by the core with `methods=("exact_computation",)`, coverage `all`, `expected_tolerances=None`, giving fresh validation: current chain, representation and registered checker revision;
- every covering evidence ID resolved to its record in the Run, with its checker **name and version** checked;
- `Prepared.prerequisites` is now an informational cache only, and the carried `source_linked` flag is ignored.

**Tests:**
- frozen fields
- nested mutation of faces, vertices, rings, spec and chain
- a bypassed model swap, and a bypassed nested mutation: `subject_model_mismatch`
- spec and ID disagreeing: `subject_binding`
- a consistent spec, ID and model swap: it certifies **E4 under E4's ID**, never E9's
- a forged `source_linked` flag, and forged or dropped cache rows: ignored, so not source-linked
- **stale** evidence (the source state tampered after its checks): refused at binding, not linked
- **unrelated** evidence (E1's cut evidence filed under E0): E0's cut claims are `not_run`
- a **rogue checker** emitting the material claim names: rejected by checker identity
- valid controls

## A03: the re-checker's input contract

**Bundle `stage4a.recheck_bundle/2`,** built by `run_probe.recheck_bundle` only from **issued** certificates. It contains:
- the source, material and cut **state records**, keyed by hash
- per seam: `subject` (spec and ID), `boxes`, `rows`, and the declared `verdict_on_D`

**What `recheck_mpmath.py` does,** still standard library plus mpmath, importing neither glab nor the probe:

1. **Binding:**
   - the spec's keys and fixed definitions
   - the ID recomputed from canonical JSON
   - each state record hashes to its key, with the right kind and parent links
   - the material identity recomputes, and the cut's seam and material copy match
   - δ is canonical in (0, 1/2)
   - the chain is re-derived from the material and the seam
2. **Shape and coverage, before any geometry:**
   - boxes for exactly the chain faces, each 4 × 2 canonical `[lo, hi]` with `lo ≤ hi`
   - every unordered pair appears exactly once, in chain order, with valid IDs and no extra rows
   - method, outcome and certificate shape are consistent; axes must be nonzero, and order tokens supported
   - `unknown` rows carry no certificate and are **counted, not rejected**
3. **Geometry:** unchanged arithmetic.
4. **Verdict:** the verdict on `D` is recomputed and compared with the declared one.

**Report:** per-seam `verified`, `rejected` or `failed`, with **reason codes**. **Exit code 0 only when everything is verified.** A bundle without the v2 schema, or an empty one, is rejected.

**Tests (26):**
- System's four cases, via the adapted fixture
- 18 single faults, each asserting its own reason code:
  - `axis_zero`, `axis_order`, `noncanonical_number`, `interval_bounds`
  - `box_shape` (a truncated face; a coordinate with 3 entries), `box_coverage` (a missing face; an extra face)
  - `pair_coverage`, `pair_duplicate`, `pair_ids`, `pair_order`
  - `method_outcome`, `shared_hinge_pair`, `verdict`
  - `subject_id`, `state_hash`, `bundle_schema`
- a forged parent link with consistent hashes: `parent_link`
- δ changed with a consistent ID: fails geometry (`containment`), not silently
- an honest unknown row, with the declared verdict `unknown`: **verified**, 1 unknown row counted
- the same unknown row with the verdict left as `pass`: `verdict`
- exit codes: 0 for a genuine bundle, non-zero for a bad one
- the re-checker's constants match the probe's
- an old-layout bundle gives `bundle_schema` only

## Adapter for System's review cases

`tests/review_env/test_review_stage4a_adapted.py` is generated by `make_review_stage4a_adapted.py` using one counted substitution: `make_bundle()` returns the probe's **bound v2 bundle**. Every test body and assertion is unchanged, and each A03 mutation is applied to that genuinely valid bundle. **15/15 pass.**

**The verbatim file after the repair gives 14 passed and 1 failed:**
- The **failure** is `test_control_genuine_recheck_bundle_passes`. Its fixture is the old unbound layout, which the contract now rejects as `bundle_schema`. This is by design, and it is the case `ADAPTER-NOTE.md` anticipates.
- The four verbatim **A03 cases pass only incidentally.** Their unbound bundle is rejected for the missing binding before any other check, and a dedicated test shows the rejection reason is exactly `{bundle_schema}`. As the adapter note directs, **I do not count them as coverage.** The coverage comes from the adapted copy and the single-fault tests.
- The verbatim A01, A02 and control cases pass on the real interface.

## The L4 correspondence (`probes/stage4a/L4-CORRESPONDENCE.md`)

This is a written argument, pinned to manuscript blob `8b9f7e1a` and design blob `d06000f8`:

1. **Charts preserve orientation.** The charts `ψ_i` (4.1) preserve orientation with respect to the outward normals. The reason: in the clockwise source order the outward edge normal is `ν_i` turned by `+π/2`, so `ν_i × ẑ = −u_i`, and `ξ_i` has positive vertical component. Together these give `ν_i × ξ_i = −n̂_i`.
2. **Whole-line agreement.** `T_i∘ψ_{i+1} = ψ_i` on the **entire** hinge line. The derivation shows the midpoint images agree (translation), and that `R(q_{i+1})` sends `(cos φ⁺, −sin φ⁺)` to `(cos φ⁻, −sin φ⁻)` (direction), using (3.1), (3.6), (4.1) and (4.2).
3. **The manuscript's maps.** The maps `𝒰_{k,j}` preserve orientation and agree on every retained hinge. Nothing is claimed at the seam.
4. **Normalization and induction.** A first-face normalization `ρ` and an induction using L2 give `Ψ = ρ∘𝒰_k`.
5. **The trim-dependent translation** (System's point). `N0` anchors the δ-dependent low trim point, so `D^δ = τ_δ∘ρ∘𝒰_k` with `τ_δ(y) = y − (δ‖G_k‖, 0)`. Therefore `D^{δ₂} = D^{δ₁} − ((δ₂−δ₁)‖G_k‖, 0)`: **one fixed map family followed by a global translation that depends only on δ**, never on the face.
6. **Trimmed faces.** `T_i(δ) = F_i^δ`, by a short independent argument that agrees with the manuscript's §3.2 statement.
7. **Consequence.** A `pass` or `fail` verdict on `D` at `(k, δ)` is the same verdict for the manuscript's trimmed family `𝒰_{k,·}|F^δ` at that `(k, δ)`. A certified `fail` shows that `k`, with its fixed maps, cannot satisfy the trimmed half of (2.4). That is consistent with Theorem 2.1, which asserts only that some `k` exists.

**Status:** the note is **not machine-checked, not formally verified, and not reviewed by a mathematician**. Its dependency table lists what it takes from the manuscript as given (Proposition 3.1 and the definitions) and what it derives.

## Remaining assumptions and limits

| Id | Status |
|---|---|
| O1: L1, L2, Theorem S, separation and witness lemmas | written derivations (design §2.2, §4, §5.4); not machine-checked |
| O2: `D` corresponds to the manuscript's `𝒰_k` | now a **written bridge** (`L4-CORRESPONDENCE.md`), with the translation made explicit; awaiting review; not formal |
| O3: the interval implementation | controls, the hardened independent re-check, and 26 contract tests; not formally verified. The re-checker has the same author: independent arithmetic and construction, not independent peer review. |
| O4: material is the manuscript's facet cycle (Stage 2 evidence) | now validated at issuance from actual Run evidence, with checker identity |
| O5: face preconditions | checked exactly at issuance; certificates refuse otherwise |
| O6: relation to the manuscript's safety statement | L4 note §8 (conditional); not a universal proof |

**Scope limits:**
- The re-checker does not re-validate Stage 2 evidence, which is a Run-level check done at issuance. It verifies geometry bound to the named states.
- The untrimmed glued-vertex case remains out of scope.

## Not done and not authorized

- Stage 4B or any maintained integration; registry, core or action-context changes; production `rigorous_enclosure` or `formal_proof` claims.
- Motion, a proof selector, caps, Lean, CGAL or FOLD, a viewer, publishing.
- Merge, PR, release, deployment, external contact, purchases, scheduler changes, new agents.
- Nothing was installed into the maintained environment.
- The branch is pushed as a work branch only.
