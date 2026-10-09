---
title: Geometry Lab Stage 4A re-check repair plan (R01, R02, and two L4 clarifications)
status: plan written before the repairs; Stage 4B held
dg-publish: false
---

# Stage 4A re-check repair plan: R01, R02 and the L4 clarifications

## Inputs and delivery

**Delivery.** System's review of `commit-62` was delivered **as an attachment**, relayed by Summer Bee: `C:\Users\<user>\Downloads\geometry_lab_stage4a_repair_review_commit-62`. System's current tools expose GitHub reads but no writes, so it is not on `origin/main`.

**Verification before use:**
- All 83 packet files match the packet's `PACKET-MANIFEST.json` (sha256 and size).
- The 50 files of its selected engine reconstruction are byte-identical (Git blob) to this branch at `commit-62`.
- The packet's `review/test_stage4a_verbatim.py` equals the `origin/main` review file (blob `9b141bce`).
- The L4 note blob System cites (`5976b026`) is this branch's.

**Preserved first** (`commit-63`): `review/` and `receipts/`, side by side, with `START-HERE.txt`, `README.md` and `PACKET-MANIFEST.json`, under `<geometry-lab-project>/reviews/stage4a-repair-commit-62/`.
- All 32 copied files were verified against the manifest.
- A one-line `.gitattributes` (`* -text`) keeps checkouts byte-exact.
- Not copied, per START-HERE: `engine/` (the reconstruction) and `continuity/` (System-only).

**Reproduced before any change** (`probes/stage4a/receipts/recheck-repair/`):
- `test_stage4a_review.py` (System's own v2 adapter) and `test_followup.py`, run with `GLAB_ENGINE` at this engine: **21 passed, 3 failed**. The failures are `test_R01_inflated_witness_margin_is_not_verified`, `test_R01_inflated_distance_bound_is_not_verified` and `test_R02_bound_but_nonplanar_subject_is_not_verified`. Of the 21 passes, 15 are prior cases and 6 are follow-up controls, as the review expected.
- The verbatim historical review: 14 passed, 1 failed, as expected.

## Scope

**Authorized:**
- R01 and R02 inside `engine/probes/stage4a/`, with tests and new receipts
- the two L4 exposition clarifications
- this plan, and `engine/STAGE-4A-RECHECK-REPAIR-RETURN.md`

**Unchanged:**
- the arithmetic algorithm and rounding, the subject definition, core, registry and maintained `glab/`
- every original receipt and return, and the preserved review
- no general redesign of the verifier

## R01: verify the quantitative bounds that remain in a certificate

In `recheck_mpmath.py`, during geometry and after the existing checks succeed:

- **Witness.** Require `0 < recorded cross_lower_bound ≤ m`. Here `m` is the smallest cross-product lower bound the re-checker computes itself, exactly, on the recorded boxes. A **smaller** valid bound stays acceptable. Failure code: `witness_bound`.
- **Axis.** `g` is the verified nonnegative projected gap for axis `d`, and `b` is the recorded `euclidean_gap_lower_bound`, which must be canonical and nonnegative. Require **`b²·(d·d) ≤ g²`**, checked in exact rational arithmetic with no square root. Failure code: `euclidean_gap_bound`. Shape failures use `noncanonical_number` or `euclidean_gap_bound_shape`.
- **Every remaining certificate or row field is classified,** never passed over:
  - *verified*: the pair, method, outcome, axis, order, `axis_gap`, both bounds above, the witness point, the side values `σ`, `shared_hinge.hinge`, `shared_hinge.sides` and `positions`
  - *unverified diagnostics*: `bits`, `attempts`, free-text `reason` and `problems`

  The report lists the diagnostics explicitly. Nothing is stripped from incoming certificates.

## R02: check the local geometry assumptions the re-checker's own construction uses

Before any geometric confirmation, from the bound material and cut payloads only, and **independently**: no glab or probe geometry code is reused. Failure codes in parentheses:

- **Unambiguous identities.** Vertex, face and hinge IDs are unique, and every referenced ID exists (`identity_ambiguous`, `reference_missing`).
- **Chain and incidence.** Each face's ring contains the endpoints of its entry and exit hinges. Consecutive chain faces share exit and entry, and the chain closes at the seam (`incidence`).
- **Nondegeneracy.** Hinges have `L ≠ U` (`hinge_degenerate`), and normals are nonzero (`normal_zero`).
- **On the plane.** Every ring vertex and both hinges' endpoints satisfy `n·v = d` exactly (`ring_not_on_plane`).
- **Outward orientation.** Every material vertex satisfies `n·v ≤ d` (`orientation_not_outward`).
- **Clipped rings.** Every trimmed ring is strictly convex and counterclockwise about `n` (`trimmed_ring_not_convex_ccw`).

**The report states the scope, machine-readably:**
- these are local preconditions of the re-checker's own calculation;
- Stage 2 source/material correspondence and Run evidence are **not** re-verified here. They are established at in-Run issuance.
- `verified: true` means the bundle's certificates and declared verdict were confirmed. **It is not a safety statement.** The per-seam recomputed `verdict_on_D` carries that; `unknown` is never a safety pass.

## Tests (single fault, genuine bound bundles, expected reason code)

**R01:**
- an inflated witness bound (rejected)
- the witness bound at exactly the recomputed value (verified), and just above it (rejected)
- a halved witness bound (verified)
- an inflated Euclidean bound (rejected), a bound just above the exact limit (rejected)
- a zero bound (verified), and the probe's own bound (verified)
- a negative bound and a non-canonical bound (rejected with shape codes)
- a missing Euclidean bound (rejected; the contract requires it)

**R02**, each state set rehashed self-consistently so that only geometry is at fault:
- a plane offset changed (System's case), giving `ring_not_on_plane`
- an inward normal
- a zero normal
- a degenerate hinge
- a duplicated vertex ID
- a face referring to a missing hinge
- a face ring lacking a hinge endpoint
- one hinge's `lower`/`upper` swapped (the clipped rings become bow-ties), giving `trimmed_ring_not_convex_ccw` with the planes still valid

**Also:** the scope and meaning fields are present in the report.

Run in the throwaway review environment. System's `test_followup.py` and `test_stage4a_review.py` run unchanged from the preserved review folder.

## L4 clarifications (in `probes/stage4a/L4-CORRESPONDENCE.md`, with a revision note)

1. **Notation.** Use the chain position `j` consistently: face `F_{k+j}` at position `j`, with maps `Ψ_{k+j}`, `Φ^δ_{k+j}` and `𝒰_{k,j}`. Never mix a global face index into the slot of `𝒰_{k,·}`.
2. **The precise trim limitation.** For the same fixed maps, a pass at `δ₀` also covers every more-trimmed subdomain `δ₀ ≤ δ < 1/2`, because `F^δ ⊆ F^{δ₀}` and interiors are monotone. It does not establish less-trimmed material, all positive trims, or the untrimmed limit.

## Verification and return

- **In the maintained environment:** inherited tests, probe controls and targets, and the A01/A02 repair tests.
- **In the review environment:** the A03, R01 and R02 tests; the adapted and verbatim prior reviews; System's review and follow-up files.
- **Bound runs:** the bound scan and re-check (new receipts), System's `reproduce_scan.py` into a fresh directory, and System's `probe_remaining_boundaries.py` on a **scratch copy**, so that the preserved receipts are never overwritten.
- My own executions are recorded separately from the imported receipts.
- Return `engine/STAGE-4A-RECHECK-REPAIR-RETURN.md`, then stop.
