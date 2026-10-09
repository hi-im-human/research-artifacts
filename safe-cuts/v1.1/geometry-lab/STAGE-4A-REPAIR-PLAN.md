---
title: Geometry Lab Stage 4A repair plan (A01-A03, written L4 correspondence)
status: plan written before the repairs; Stage 4B held
dg-publish: false
---

# Stage 4A repair plan: A01–A03 and the written L4 correspondence

## Inputs

- **System's review:** `<geometry-lab-project>/reviews/stage4a-review/REVIEW.md`, with `RESULTS.json`, `test_stage4a_review.py` (blob to be recorded when copied) and `ADAPTER-NOTE.md`. Authorization `commit-58`. All read from `origin/main` without merging.
- **Reviewed head:** `commit-57`. There were no later worker commits, and the worktree was clean.
- **Manuscript**, read-only, for L4: `<research-record>/<historical-folder>/manuscript/DRAFT-02.md`, blob `8b9f7e1a4633c372053ba43e65208847d0ebb93d`, identical on the branch and on `origin/main`. Sections read: 2.2–2.3 (Theorem 2.1, (2.3), (2.4)), 3.1–3.3 ((3.1)–(3.6)), 4 ((4.1)–(4.4)) and 9.

**Write scope:**
- `engine/probes/stage4a/`: repairs, new controls, the verbatim and adapted review cases, and receipts under `receipts/repair/`
- `engine/probes/stage4a/L4-CORRESPONDENCE.md`
- this plan, and `engine/STAGE-4A-REPAIR-RETURN.md`

The original Stage 4A design and return, all earlier receipts, `glab/`, the manuscript, the proofs and the reviews stay unchanged. Corrections to the design are recorded here and in the note, not by rewriting history.

## 0. Reproduction first

`test_stage4a_review.py` imports the mpmath re-checker, and the maintained `.venv` has no mpmath. So I will build a **throwaway review environment** outside the repository, with no network access:
- Python 3.11.9
- the maintained environment's pinned numpy 2.4.4, pytest 9.1.1 and their dependencies, copied from `.venv`
- mpmath 1.3.0, copied from the user site
- every copied distribution checked against its `RECORD` hashes, with bytecode removed, run with `-B`

The maintained `.venv` is not modified. I expect System's result at `commit-57`: 4 passed, 11 failed. Receipt: `receipts/repair/red-review-at-commit-57.log`.

## A01: domain and preconditions, enforced at issuance

- `load_subject` refuses δ outside `0 < δ < 1/2` (and any non-canonical δ) with `UnsupportedSubject`, a `ValueError`, before any `D` exists.
- `ideal_certificate` **re-checks everything at issuance** and returns a **structured refusal**, never `pass` or `fail`, when any precondition fails:

| Id | Precondition |
|---|---|
| P1 | δ canonical and in the domain |
| P2 | the spec's state hashes resolve in the Run, with the correct kinds and parent links (cut → material → source); the cut's material copy equals its parent; the material `identity` recomputes |
| P3 | chain: the cut's `face_order` is a permutation of the faces, the first entry is the seam, and consecutive faces share exit and entry |
| P4 | every face: nonzero normal; ring exactly on its plane; **normal outward** (every material vertex satisfies `n·v ≤ d`); both hinges nondegenerate and in the plane; trimmed ring strictly convex and counterclockwise about the normal |

- A refusal is not an overlap verdict. The low-level functions (`model_from_payloads`, `classify_seam`, `decide_boxes`) stay available for synthetic experiments. Their output is never a certificate.
- **Tests:**
  - System's five δ cases
  - faulty-builder Runs: an inward face plane, and a cut with a scrambled `face_order`
  - a subject whose spec δ is altered after construction, bypassing the frozen object
  - valid near-boundary controls: δ = 10⁻³⁰ and δ = 1/2 − 10⁻³⁰ on the square (exact, issued `pass`), and δ = 1/2 − 10⁻³⁰ on E11 (issued with an honest verdict)

## A02: bind the calculation and the evidence to the subject at use time

**Immutable objects.**
- `ExactModel` becomes a frozen dataclass whose nested maps are `FrozenDict`, a `dict` subclass that refuses mutation, so it still serializes to JSON, and whose sequences are tuples.
- `Subject` becomes a frozen dataclass that carries its `Run`.

**Rebuild at issuance.** `ideal_certificate` never trusts the carried `model` or the `source_linked` flag. It:
1. recomputes `id = content_hash(spec)`;
2. checks the spec constants: kind, definition, orientation, normalization;
3. reads the named states from the Run and **rebuilds** the model from them;
4. compares the rebuilt model with the carried one. Any mismatch in seam, δ, coordinates, rings, chain, normalization or orientation gives a structured refusal, `subject_model_mismatch`.

**Prerequisites from the Run's evidence, not from `Prepared.prerequisites`**, which becomes an informational cache only:
- the full expected claim sets from the maintained constants:

  | Subject | Checker | Claims |
  |---|---|---|
  | source hash | `two_rim.check.source` v2 | `SOURCE_CLAIMS` |
  | material hash | `two_rim.check.material` v2 | `MATERIAL_CLAIMS` |
  | cut hash | `two_rim.check.cut` v1 | `CUT_CLAIMS` |
- each summarized with the core `Run.summarize`: `methods=("exact_computation",)`, coverage `all`, `expected_tolerances=None`. This gives fresh `validate_evidence`, meaning current chain, representation and registered checker revision.
- each covering evidence ID resolved to its actual record, with the checker name and version checked.
- `source_linked` is computed here. `prerequisites_complete` uses the same code, so every path agrees.

**Tests:**
- System's two cases
- assigning to a frozen field; a nested mutation (`TypeError`); a bypassed model swap (refusal)
- a spec and ID that disagree (refusal)
- stale evidence: the material state tampered after its checks
- unrelated evidence: the cut checker run only on a different cut
- a rogue checker emitting material claim names
- valid controls

## A03: the re-checker's input contract

**Bundle schema `stage4a.recheck_bundle/2`:**
- the three **state records** (source, material, cut) keyed by hash
- per seam: `subject` (spec and ID), `boxes`, `rows` and a declared `seam_verdict`

**What the re-checker does,** still standard library plus mpmath, importing neither glab nor the probe:

- **Binding**, with its own copies of the constants and canonical JSON:
  - the spec has exactly the expected keys and values
  - `id = sha256(canonical(spec))`
  - each state record hashes to its key, with the right kinds and parent links
  - the material `identity` recomputes, and the cut's seam and material copy match
  - δ is canonical and in the domain
  - the chain is re-derived from the material hinge order and the seam
- **Shape and coverage, before any geometry:**
  - boxes for exactly the chain faces, each exactly 4 × 2 canonical `[lo, hi]` with `lo ≤ hi`
  - rows covering every unordered pair of chain faces exactly once, in chain order, with valid IDs and no extras
  - method, outcome and certificate shape consistent:

    | Row type | Required |
    |---|---|
    | shared hinge | outcome `pass`, a consecutive pair, `σ` for both rings |
    | separating axis | outcome `pass`, a nonzero rational axis, `order ∈ {P_below_Q, Q_below_P}`, canonical gap |
    | interior witness | outcome `fail`, a rational point, a positive bound |
    | unknown | outcome `unknown`, no certificate; counted, not rejected |
- **Geometry:** the existing containment, Theorem S, axis and witness checks.
- **Verdict:** recomputed from the confirmed rows and compared with the declared `seam_verdict`.

**Report.** Each seam is `verified`, `rejected` (binding or shape; geometry skipped) or `failed` (geometry). Failures carry reason codes. Totals keep the old keys and add `verified`, `rejected_seams`, `failed_seams` and `unknown_rows`. The **exit code is 0 only when every seam is verified.** A bundle without the v2 schema or binding is rejected.

**Tests,** run in the throwaway review environment:
- System's four cases (adapted fixture)
- one test per single fault:
  - zero axis, bad order token, non-canonical number, reversed bounds
  - one truncated face, a coordinate with 3 entries, a missing face, an extra face
  - a missing row, a duplicate row, a wrong ID, a reversed pair, an extra row
  - a witness labelled `pass`; a shared-hinge row on a non-consecutive pair
  - a wrong declared verdict
  - an altered spec field; an altered state record; a wrong parent link; δ changed with a consistent ID
  - an honest `unknown` row (accepted and counted), and an `unknown` that should turn the verdict to `unknown`
  - exit codes

## Adapter for System's review cases

- `review-cases/stage4a-review/test_stage4a_review.py` stays **verbatim**, with its blob checked.
- `tests/repair/test_review_stage4a_adapted.py` is generated by a script using counted literal substitutions. The only change: `make_bundle` builds the new **v2 bound bundle** with the probe's exporter, because the old unbound bundle is deliberately rejected under A03.
- Every assertion is kept. Coverage of each reviewed property is shown on a genuinely valid fixture. A rejection for a missing binding is not counted as coverage of anything else.

## L4 correspondence note (`probes/stage4a/L4-CORRESPONDENCE.md`)

A written argument for review, pinned to manuscript blob `8b9f7e1a`:
1. the charts `ψ_i` (4.1) preserve orientation with respect to outward normals, because the faces are in clockwise order (3.1) and `ξ_i` has positive `z`-component;
2. `T_i∘ψ_{i+1} = ψ_i` on the **entire** hinge line, rotation and translation, derived from (3.1), (3.6), (4.1) and (4.2);
3. the manuscript's `U_{k,j}` are orientation-preserving isometries that agree on every retained hinge;
4. a first-face normalization `ρ`, and then induction using L2, give `Ψ = ρ∘U`;
5. **δ-dependent `N0`:** `D^δ = τ_δ∘ρ∘U` with `τ_δ(y) = y − (δ|G_k|, 0)`, so `D^{δ₂} = D^{δ₁} − ((δ₂−δ₁)|G_k|, 0)`. This is the translation between normalizations. It connects `D` to the fixed-map-across-trims statement of Theorem 2.1 and Section 9, and it adds no motion and no new safety claim;
6. `T_t(δ) = F_t^δ` (2.3) and §3.2.

The note is **not** a formal verification. Its dependencies are listed.

## Verification and return

- Controls C1–C7; the inherited suite; the verbatim and adapted review cases; the new repair tests; the E11 and prism targets; the hardened re-check with its single-fault controls.
- Failed attempts are preserved. Input rejection, undecided arithmetic and geometric overlap are kept distinct.
- Return `engine/STAGE-4A-REPAIR-RETURN.md`, then stop. Stage 4B stays held.
