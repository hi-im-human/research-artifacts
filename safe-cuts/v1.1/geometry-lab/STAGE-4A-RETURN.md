---
title: Geometry Lab Stage 4A return - arithmetic assessment and isolated probe
status: Stage 4A complete; stopped before Stage 4B / maintained integration
dg-publish: false
---

# Stage 4A return: arithmetic assessment and isolated probe

**From:** Claude Code session (Claude Opus 5.5), outside the project's agent team. I wrote the design and the probe, so I am their implementer, not an independent reviewer.

**Assignment:** `<geometry-lab-project>/SYSTEM-TO-CLAUDE-STAGE-4A.md` at authorization `commit-53`. I also read System's acceptance review `reviews/stage3-repair-commit-52/` (its `REVIEW.md`, `RESULTS.json`, test file and receipts). Everything was read from `origin/main` without merging.

## Answer

**Yes, on this bounded evidence.** Exact-input rational intervals together with an exact shared-hinge argument resolve every contact that Stage 3 left uncertain on the eleven-panel specimen. They do this for a clearly separate subject: the ideal trimmed development `D`, defined from the exact material. The rounded Stage 3 placement is never an input and never a subject.

On that specimen, at height = δ = 1/10000:
- **Every pair decided.** All 605 face pairs are decided (11 seams × 55 pairs):
  - 110 retained-neighbour pairs **exactly**, by Theorem S
  - 484 other pairs by a certified separating axis
  - 11 pairs by a certified interior witness
- **Seam verdicts for `D`:**
  - `pass` on E0, E1, E2, E4, E5, E6 and E7
  - `fail` on E3, E8, E9 and E10
- **Historical comparison.** After classification, every verdict agrees with the mapped historical exact classes, and the four historical witness points are certified strictly inside both of their faces in `D`.

**What this does not establish.**
- It is **not a universal proof**. It is one exact specimen plus a square-prism control.
- Nothing of the Stage 3 float states changes: their `unknown`s stay `unknown` for those subjects.
- The `pass` and `fail` verdicts about `D` are conditional on the documented lemmas (O1) and the implementation (O3). §7 lists these.

## Where it is

- **Repository:** `<private-repo>`
- **Branch:** `<private-branch>`
- **Reviewed head:** `commit-52`. There were no later worker commits, and the worktree was clean.
- **Commits:**
  - `commit-54`: `STAGE-4A-DESIGN.md`, written and committed **before any probe code**
  - `commit-55`: the probe (`ratint`, `ideal`, `classify`, `firewall`, `specimens`) and controls C1–C8, committed and passing **before any target ran**
  - `commit-56`: targets, eleven-seam scan, historical reference, L4 hypothesis checks, independent re-checker and its negative controls, receipts
  - the commit that adds this file
- **Write scope.** Only `engine/STAGE-4A-DESIGN.md`, `engine/probes/stage4a/` and this file changed since `commit-52`, and I checked this. `glab/`, earlier returns and plans, receipts, the assessment, fixtures, the manuscript and frozen Lean are untouched.
- **What the probe does not do:**
  - it registers nothing in a glab `Registry`
  - it issues no `rigorous_enclosure` or `formal_proof` evidence
  - every receipt is labeled "isolated Stage 4A prototype"

## What was executed

| Run | Result | Receipt (`engine/probes/stage4a/receipts/`) |
|---|---|---|
| Controls C1–C7, before targets | 99 passed | `controls/controls-before-targets.log` |
| C8: inherited worker suite, before targets | 411 passed | `controls/inherited-suite-C8.log` |
| C8: Stage 3 float mutation controls (`test_develop.py`, `test_trim.py`) | 33 passed, unchanged | `controls/stage3-float-mutation-controls-C8.log` |
| Targets, first run | 6 passed, **1 failed** (square prism: box widths not zero), preserved | `targets-first-run.log` |
| Controls, final (after the rounding refinement) | 99 passed | `controls/controls-final.log` |
| Targets, final | 7 passed | `targets-final.log` |
| Inherited worker suite, final | 411 passed | `inherited-suite-final.log` |
| Probe run | 11 seams decided; byte-identical across two runs apart from `timing.json` | `results/` (+ `MANIFEST.json`; committed blobs match) |
| Independent re-check (throwaway environment) | 110/110 Theorem S rows, 968/968 box coordinates contained, 484/484 axes, 11/11 witnesses, **0 failures** | `recheck/recheck.json`, `recheck/environment.json` |
| Re-checker negative controls | 5/5 tampered bundles rejected: shifted box, altered axis gap, moved witness, altered side value, inward normal input | `recheck/recheck-negative-controls.log`, `recheck/controls/*.out.json` |

**Collection versus assertion failures.** Every recorded run collected and imported cleanly. The one recorded assertion failure is the first target run above.

**Failures during development that no receipt captured,** reported here instead:
1. **C7 first run.** A cross-Run certificate-digest test failed because the full digest legitimately includes Run-specific prerequisite evidence IDs. I split out a `classification_digest` for the verdicts about `D` and tested both properties.
2. **C4 was weak.** At 0–16 bits every interval pair on E11 was `unknown`, so its "never a false verdict" check was trivial. I extended the sweep to 32–56 bits, where decisions are partial, and it now asserts that a partial precision was exercised.
3. **C1–C3 had no red run.** I wrote `ratint.py` right after its control tests, without a red run in between.
4. **A control rested on a wrong assumption.** Before running, I replaced it: a denominator-relative square root never has a zero lower bound (§5 below).
5. **A witness proposal would have masked thin overlaps.** Before running, I removed its `limit_denominator` coarsening.
6. **A re-checker control used the wrong mechanism.** The shifted-box control first shifted by less than the box width, so containment was not what caught it. It now shifts by more than twice the width.
7. **I deleted receipts by mistake.** A cleanup glob deleted the negative-control outputs. I regenerated them deterministically.

## The subject and the firewall (design §§2–3)

**The subject.** `D` is fixed by exact inputs read from real Run states:
- source, material with its `identity`, and cut state hashes
- the seam, and δ
- orientation `outward`: each face map preserves orientation with respect to its outward normal
- normalization `N0`: the first chain face's entry-hinge low trim point goes to the origin, with that hinge on +x

It is defined by a recursion of orientation-preserving isometries that agree on each retained hinge. Lemma L2 guarantees that this recursion exists and is unique.

**Subject ID and source link.** The `ideal_subject` ID is `content_hash` of that specification. Each certificate carries:
- the subject;
- the prerequisite evidence from `two_rim.check.source` v2, `two_rim.check.material` v2 (including `matches_parent_source`) and `two_rim.check.cut` v1, each re-validated as `current`;
- a `source_linked` flag.

If a prerequisite is missing or failing, the seam verdict is `not_source_linked`.

**Firewall controls (C7):**
- A mutated Stage 3 float placement still fails the unchanged Stage 3 v2 checker.
- `applies_to` refuses every float state, original or altered.
- The ideal certificate does not change when float states exist in the same Run, and its verdicts about `D` are identical across Runs.
- Diagnostic only: the unaltered float placement lies within 4.1e-13 of `D`'s enclosure after a **rotation**; the altered one is more than 0.1 away.

## The shared-hinge argument, and what it rests on

**Theorem S (design §4).** Two consecutive chain faces that share a retained hinge are `pass` when four exact checks hold:
- **S1 (identity):** the chain positions, the exit and entry roles, "not the seam", and the endpoint IDs are present in both material rings, with the same exact coordinates;
- **S2:** the hinge and both normals are non-degenerate;
- **S3:** both rings lie exactly on their recorded planes;
- **S4:** the exact rational values `σ(w) = (e × (w − L))·n` put one trimmed ring on each closed side of the hinge.

**Why that suffices.** Lemma L1, `cross2(Aa, Ab) = (a × b)·n̂` for orientation-preserving frames, carries each `σ` sign into the plane unchanged. Both faces are measured against **one** planar line, because `D` agrees on the hinge by definition. So the two images lie in opposite closed half-planes.

**What it does not use:** numbers from `Φ`, boxes, identifier coincidence alone, tolerances, snapping, or skipping the pair.

**Results:**
- **T1** (E4, F4/F5 across E5): `pass` with sides −1 and +1.
- The same pair **on intervals alone** stays `unknown` at every precision up to 512 bits, which is why the exact argument is needed.

**Controls (C6).** Theorem S refuses each of these, giving `unknown` with the reasons:
- a wrong hinge
- faces that are not consecutive
- the seam pair, which is shared in 3D but cut in `D`
- matching hinge IDs whose ring uses a renamed endpoint
- an inward normal

**Remaining assumptions:**

| Id | Statement | Status after 4A |
|---|---|---|
| O1 | L1, L2, Theorem S, and the separation and witness lemmas | written derivations in the design; **not machine-checked** |
| O2 | L4: `D` equals the manuscript's chart development `W`, up to an isometry | derivation sketched; per-instance hypotheses **checked exactly** (midpoints at h/2, positive hinge z-extents, every chart orientation sign +1) on E11 and the prism; the derivation itself is **not established**; not used by any probe verdict |
| O3 | the probe's interval implementation is correct | controls, plus an independent re-check (different construction, different arithmetic library) with negative controls; **not formally verified** |
| O4 | the material is the source's exact body, with outward normals and counterclockwise rings | Stage 2 v2 evidence (exact computation), carried per certificate |
| O5 | faces are planar; trimmed rings are strictly convex and counterclockwise | checked exactly per face in every run |
| O6 | how a verdict on `D` relates to the manuscript's safety statement | outside 4A |

## Enclosures, precision and performance

**The trusted base.**
- CPython `int`, `fractions.Fraction`, `math.isqrt`, and about 150 lines of `ratint.py`.
- Square roots use `isqrt(N·D·4^P)`, and every one is re-checked exactly as `lo² ≤ a ≤ hi²`.
- Division refuses any denominator interval that contains zero.
- Floats never decide anything. Candidate axes and witnesses are proposed from exact box midpoints, and only certification counts.

**Rounding refinement (a deviation from design §5.2).** The design rounded every intermediate value outward to a 2⁻ᴾ grid. The square-prism target showed that this widens exact but non-dyadic values such as 1/3. That is still a valid enclosure, but it breaks the exact path.
- **Now:** zero-width values stay exact, and only intervals that already have width are rounded.
- The controls were rerun after the change: 99/99.
- The first target run, with the failure, is preserved.

**Design error kind that never fires.** The design's §5.2 error kind `sqrt_lower_bound_zero` cannot occur, because the square root is relative to the radicand's denominator. Loss of precision instead shows up as `zero_denominator` after absolute rounding, and C3 covers that.

**Precision profile (E11).**
- Nothing interval-based decides at 16 bits. The first decisions come at 32 bits (3 pairs), and all 495 interval pairs are decided at 64 bits.
- The reason is the flat band (h = 1e-4). There the frame factor `1/(|n||e|)` is about 1e-8, and absolute rounding destroys it at low precision.
- The largest box width at 128 bits is 6.3e-25.
- The budget went up to 512 bits, but nothing needed more than 64.

**Performance.**
- About 0.29 s per seam for the full schedule; 3.2 s for all 11 seams (`results/timing.json`).
- The 400-bit mpmath re-check takes about 0.34 s in total.
- The work is `O(n²)` pairs times a few candidate axes. Nothing beyond n = 11 was run: I deliberately did not scan the random corpus, to keep the probe bounded.

**Backends:**
- **mpmath 1.3.0 `iv`.** Its documentation calls the interval support "still experimental, and many functions do not yet properly support intervals".
  - I used it only for `+ − × ÷` and `sqrt`, in the re-checker.
  - It ran in a throwaway venv outside the repository, with no network access and nothing installed into the maintained `.venv`. The copy came from the already-present Python 3.11 user site.
  - All 92 hashed files verify against `RECORD` with 0 mismatches. I deleted the 87 copied `.pyc` files and ran with `-I -B`. Tree hash: `89a0d9e219a4d35e0fc6c5de0466432675827849a1a8247f5c05d6504875f82c`.
- **FLINT/Arb.** Evaluated against its documentation only. **Not installed or executed**, and not needed at this scale.
- **The historical verifier** was read as prior art and **not executed**. Its side choice uses an interval sign of the previous panel's centre; the exact `σ` route replaces that.

## Recommendation for Stage 4B (for review; not started)

**Representation.** Use standard-library rational intervals, as in the probe, plus the exact Theorem S path. No external backend is needed. Use relative outward rounding (floating style), or keep frame factors unrounded, so that flat inputs do not need about 40 extra bits.

**Proposed evidence contract.** This is design §8, refined:

1. **Exact state `two_rim.ideal_trimmed_development`** (`two_rim.ideal_trim/1`), produced by action `two_rim.ideal.define` v1.
   - Its parent is the **cut** state, never a float state.
   - Its payload holds the exact cut copy, δ, the orientation, the normalization and the definition version.
2. **Contextual checker `two_rim.check.ideal_trimmed_development` v1**, with these claims:

   | Claim | Method | Notes |
   |---|---|---|
   | `…record_schema` | `exact_computation` | |
   | `…cut_copy_matches_parent` | `exact_computation` | |
   | `…trim_faces_convex_counterclockwise` | `exact_computation` | |
   | `…retained_neighbours_opposite_sides` | `exact_computation` | coverage `retained_hinges`; the receipt holds the `σ` values and names its lemmas (O1) |
   | `…nonadjacent_pairs_certified` | `rigorous_enclosure`, `rational_interval` domain | coverage `pairs_without_retained_hinge`; `Claim.tolerances` = an `ENCLOSURE_POLICY` giving the arithmetic, square-root rule, rounding policy, schedule and budget; the receipt holds the axes, witnesses and gap and margin bounds |
3. **A new aggregate**, `source_linked_ideal_trimmed_obligations`. It combines the source and material bundles, the cut claims, and the ideal claims, with the enclosure policy required. The existing float totals are unchanged.
4. **Where the code lives.** The arithmetic goes in a small standard-library module outside `glab/core`. There is no core or action-context change: `rigorous_enclosure` is already a supported method.
5. **Tests.** Port controls C1–C7. Keep the historical comparison and any second, independent re-checker **test-side**.

**Decisions for System:**
- whether `D`, with its `outward` orientation and `N0` normalization, is the accepted subject;
- whether Theorem S rows may use `exact_computation` while depending on written lemmas (O1), or need an explicit lemma-dependency field or label;
- whether O2 (L4) must be established before any maintained text relates `D` to the manuscript's `W`;
- the rounding policy (relative versus absolute);
- how to package the re-checker: mpmath in a throwaway environment, or a second standard-library implementation;
- whether the untrimmed glued-vertex argument is ever in scope.

## Not done and not authorized

- Stage 4B or any maintained integration: registry, `glab/` or core changes, production `rigorous_enclosure` or `formal_proof` claims.
- Continuous motion, proof-guided seam selection, caps, Lean, CGAL or FOLD, an interactive viewer, a publishing workflow.
- Merge, PR, release, deployment, external contact, purchases, scheduler changes, or additional agents.
- Nothing was installed into the maintained environment.
- The branch is pushed as a work branch only.
