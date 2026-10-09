---
title: Geometry Lab Stage 4A re-check repair return (R01, R02, two L4 clarifications)
status: R01/R02 repaired in the standalone re-checker; L4 note clarified; stopped; Stage 4B held
dg-publish: false
---

# Stage 4A re-check repair return: R01, R02 and the L4 clarifications

**From:** Claude Code session (Claude Opus 5.5), outside the project's agent team. I wrote the probe, the re-checker and these repairs, so I am their implementer, not an independent reviewer.

**Assignment:** System's review of `commit-62`. It was delivered **as an attachment relayed by Summer Bee**, because System's GitHub tools exposed reads only, and it is not on `origin/main`. Scope: R01 and R02 inside `engine/probes/stage4a/`, the two L4 exposition clarifications, a plan and this return. Stage 4B is held.

## Where it is

- **Repository:** `<private-repo>`
- **Branch:** `<private-branch>`
- **Reviewed head:** `commit-62`. There were no later worker commits, and the worktree was clean.
- **Commits:**
  - `commit-63`: **System's review preserved first**, under `<geometry-lab-project>/reviews/stage4a-repair-commit-62/`
  - `commit-64`: plan, R01/R02 tests first, and the reproduction at `commit-62`
  - `commit-65`: the R01/R02 re-checker repair, the L4 clarifications, and receipts
  - the commit that adds this file
- **Write scope,** checked: only the preserved review folder, `STAGE-4A-RECHECK-REPAIR-PLAN.md`, this file, and `engine/probes/stage4a/` changed.
- **Unchanged:** the arithmetic and rounding (`ratint.py`, `ideal.py`), the classifier, the issuer (`binding.py`, `firewall.py`), `glab/`, `tests/`, every earlier return and receipt, and the verbatim copy of System's earlier review cases (`probes/stage4a/review-cases/`). There was no core, registry or action-context change, and nothing was installed into the maintained `.venv`.

## The attachment and its preservation

**Checks before use:**
- All 83 packet files match the packet's own `PACKET-MANIFEST.json` (sha256 and size), with none unlisted or missing.
- The packet's selected engine reconstruction (50 files) is **byte-identical to this branch at `commit-62`** (Git blob identities), so System reviewed this code.
- The packet's `review/test_stage4a_verbatim.py` is the `origin/main` review file (blob `9b141bce`).
- System's cited L4 blob `5976b026` is this branch's note at `commit-62`.

**What was preserved.** Following START-HERE, `review/` and `receipts/` sit side by side in `<geometry-lab-project>/reviews/stage4a-repair-commit-62/`, so the reproducer finds `../receipts/`. With them are the packet's `START-HERE.txt`, `README.md` and `PACKET-MANIFEST.json`.
- All 32 copied files re-verified against the manifest after copying.
- I added a one-line `.gitattributes` (`* -text`) so checkouts stay byte-exact.
- **Not copied,** as START-HERE says: `engine/`, the selected reconstruction (it would duplicate this branch), and `continuity/`, System's own handoff.
- Every later run left that folder untouched, with bytecode and cache writes disabled.

## Execution record

Everything in `engine/probes/stage4a/receipts/recheck-repair/` is **this session's own execution**. System's receipts are preserved separately and unchanged.

| Run | Result | Receipt |
|---|---|---|
| System's `test_stage4a_review.py` (its own v2 adapter) and `test_followup.py`, from the preserved folder, at `commit-62` | **21 passed, 3 failed**: the two R01 cases and the R02 case, exactly as the review expected | `red-review-and-followup-at-commit-62.log` |
| The same review's verbatim historical file, at `commit-62` | 14 passed, 1 failed (the obsolete unbound fixture), as expected | `verbatim-at-commit-62.log` |
| My R01/R02 tests first, at `commit-62` | 18 failed, 4 passed. The passes are the positive controls. Failures: 1 `KeyError` (the new `scope` report field did not exist) and 17 assertions. In those, the old re-checker either accepted the fault (12: every R01 case, and the plane-offset, duplicate-ID and ring-incidence R02 cases), crashed into a generic `malformed` rejection (3: zero normal, degenerate hinge, missing reference), or failed only at geometry instead of rejecting first (2: inward normal, bow-tie ring). In the combined positions and shared-hinge test, only the positions fault was reached. | `red-r01-r02-tests.log` |
| System's review and follow-up, after the repair | **24 passed** (15 prior, 9 follow-up) | `system-review-and-followup-after-repair.log` |
| System's verbatim historical file, after the repair | 14 passed, 1 failed (obsolete unbound fixture, rejected by design) | `system-verbatim-after-repair.log` |
| Review-environment tests | **63 passed**: A03 26, adapted prior review 15, R01/R02 22 | `review-env-tests.log` |
| Inherited worker suite | **411 passed** | `inherited-suite.log` |
| Probe controls C1–C7; targets; A01/A02 repair tests | 99, 7 and 36 passed | `controls.log`, `targets.log`, `repair-a01-a02.log` |
| Bound scan | 11 seams, byte-identical across two runs apart from timing; the manifest matches the committed blobs (7 of 7) | `results/`, `run-probe-stdout.log` |
| Hardened re-check of all 11 seams | **exit code 0**. `verified`: 11/11 seams; 605/605 rows; 968/968 coordinates; 110 Theorem S rows; 484 axes **and 484 Euclidean bounds**; 11 witnesses **and 11 witness bounds**; local preconditions `checked` on every seam; 0 failures | `recheck/recheck.json` |
| System's `reproduce_scan.py`, run fresh into this directory | exit code 0, with all its assertions holding: 605 decided (110, 484, 11), square 8/8 exact, re-check verified | `system-reproduce-scan/` |
| System's `probe_remaining_boundaries.py`, on a **scratch copy** so the preserved receipts are not overwritten | `accepted: false` for the inflated witness bound, the inflated distance bound, and the inconsistent plane offset (all three were `true` at `commit-62`) | `system-boundary-probe-after-repair.json` |

**Test edits after the tests-first commit:** none. `git diff commit-64 commit-65` shows no change under `tests/` or the review folder.

**Environments:** `environment.json`.
- The maintained `.venv` was used read-only.
- The throwaway **review** environment and **mpmath-only** environment are the same ones used in the A01–A03 repair: copied pinned packages, `RECORD`-verified, no network, outside the repository.

## R01: quantitative bounds are verified, never passed over

In `recheck_mpmath.py`, after the existing checks succeed:

- **Witness.** Require `0 < recorded cross_lower_bound ≤ m`, where `m` is the re-checker's own exact recomputed lower bound on the recorded boxes. A smaller valid bound is accepted. Failure code: `witness_bound`.
- **Axis.** For axis `d` with verified projected gap `g`, the recorded `euclidean_gap_lower_bound` `b` must be present and canonical (`euclidean_gap_bound_shape`, `noncanonical_number`), and `b ≥ 0`. Then **`b²·(d·d) ≤ g²`** is checked in exact rational arithmetic, with no square-root backend. Failure code: `euclidean_gap_bound`.
- **Field classification.** Every row and certificate field is now either **verified** or **declared a diagnostic**. Unrecognized fields are **rejected** (`unrecognized_field`), never ignored.
  - Verified: pair, method, outcome, `positions` (code `positions`), the certificate `method` (code `certificate_method`), axis, order, `axis_gap`, both bounds, the witness point, and the shared-hinge record: `pair`, `hinge`, `method`, `outcome`, empty `problems`, `sides` against the recomputed sides, and `σ` (code `shared_hinge_record`).
  - Unverified diagnostics, listed in the report as `diagnostic_fields_not_verified`: `bits`, `attempts`, `reason`, `shared_hinge.reason`, and the shared-hinge record on `unknown` rows.
- **Tests:**
  - witness bound at exactly the recomputed value (verified); a third of it (verified); just above it (rejected); hugely inflated (rejected)
  - Euclidean bound zero (verified); the probe's own recorded bounds (verified); a hair above the exact limit, built with exact `isqrt` (rejected); huge (rejected); negative, non-canonical or missing (rejected with shape codes)
  - an unrecognized certificate field; wrong positions; flipped shared-hinge sides

## R02: the re-checker's local geometry preconditions

`_local_geometry` runs **before any geometric confirmation**, on the bound material and cut payloads only, with its own exact code (no glab or probe code). Failure codes in parentheses:

- **Identities.** Vertex, face and hinge IDs are unique strings (`identity_ambiguous`), and every reference exists (`reference_missing`).
- **Chain and incidence.** Each hinge is the entry of exactly one face and the exit of exactly one face, the chain continues from the seam, and each ring contains both endpoints of its hinges with at least three distinct vertices (`incidence`).
- **Nondegeneracy.** Hinges are nondegenerate (`hinge_degenerate`), and normals are nonzero (`normal_zero`).
- **On the plane.** Every ring vertex and hinge endpoint lies exactly on the stated plane (`ring_not_on_plane`). This is the review's case.
- **Outward orientation.** Every material vertex satisfies `n·v ≤ d` (`orientation_not_outward`).
- **Clipped rings.** Every clipped ring is strictly counterclockwise and convex about `n` (`trimmed_ring_not_convex_ccw`).

A failure makes the seam `rejected`, with `local_preconditions: "failed"` and **no coordinates checked**.

**Scope, stated in every report** (`scope`):
- **Checked:** the local preconditions.
- **Not checked:** Stage 2 source correspondence and Run evidence are **not re-verified here**. They are established at in-Run certificate issuance.
- **Meaning:** `verified: true` means the bundle's certificates, bounds and declared verdicts were confirmed. **It is not a safety statement.** The per-seam recomputed verdict on `D` is, and `unknown` is never a safety pass.

**Tests:** eight single faults. Each mutates the material, then rehashes material, cut, spec and ID self-consistently, so only the geometry is wrong:
- plane offset changed
- inward normal
- zero normal
- degenerate hinge
- duplicated vertex ID
- a face pointing to a missing hinge
- a ring missing a hinge endpoint
- one hinge's `lower`/`upper` swapped, which turns the clipped rings into bow-ties while the planes stay valid

Each is rejected before geometry with its reason code. A rehash with no mutation still verifies.

## L4 clarifications (`probes/stage4a/L4-CORRESPONDENCE.md`, now blob `ed135840`)

The revision note at the top records both changes. The reviewed version (`5976b026`) stays in Git history.

1. **Notation.** The chain position `j` is used consistently: `F_{k+j}` at position `j`, with maps `Ψ_{k+j}`, `Φ^δ_{k+j}` and `𝒰_{k,j}`, in §4, Claim 6, the common translation, and §8. No face index sits in the slot of `𝒰_{k,·}` any more.
2. **Trims covered by a pass.** "A pass says nothing about other trims" is replaced by the precise statement. For the same fixed maps, a pass at `δ₀` also holds on every more-trimmed `δ₀ ≤ δ < 1/2`, because `F^δ ⊆ F^{δ₀}` and interiors of subsets lie in the interiors of the sets. It does not establish less-trimmed material, all positive trims, the untrimmed limit, or full safety.

The frontmatter records System's acceptance as an **AI review**. The note remains **not machine-checked, not formally verified, and not reviewed by a human mathematician**.

## Remaining limits

- **Same author.** The re-checker is independent arithmetic and construction, not independent peer review.
- **What it now checks.** It verifies local preconditions, geometry and bounds for the bound states. Source correspondence and Run evidence remain in-Run issuance checks.
- **O1 and O3 are unchanged:** the lemmas are written derivations, and the interval implementation is tested, not formally verified.
- **Scope.** The untrimmed glued-vertex case, Stage 4B and maintained integration remain out of scope.

## Not done and not authorized

- Stage 4B or any maintained integration; registry, core or action-context changes; production `rigorous_enclosure` or `formal_proof` claims.
- Motion, a proof selector, caps, Lean, CGAL or FOLD, a viewer, publishing or website work, research-publishing revision 0.4.
- Merge, PR, release, deployment, external contact, purchases, scheduler changes, new agents.
- Nothing was installed into the maintained environment.
- The packet's `continuity/` was not copied.
- The branch is pushed as a work branch only.
