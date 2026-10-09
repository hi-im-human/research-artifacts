---
title: Geometry Lab engine - Stage 3 repair plan (S01-S04)
status: plan written before the repairs; Stage 4 held
dg-publish: false
---

# Stage 3 repair plan: S01-S04

**Inputs.**
- System's review `<geometry-lab-project>/reviews/stage3-review/REVIEW.md` at review `commit-48`, read from `origin/main` without merging main.
- The adjacent `test_stage3_regressions.py` (blob `0ec7cd01`), `RESULTS.json`, and `ADAPTER-NOTE.md`.
- Reviewed head: `commit-47`. The worker branch has no commits after it, and the worktree was clean at the start.

**Scope.** Only the four bounded repairs:
- no core change and no action-context extension
- no Stage 4 arithmetic
- no change to the static generator (`cut.py`, `develop.py`, `trim.py` stay byte-identical)
- earlier returns and receipts stay unchanged, and new receipts go to `receipts/stage3-repair/`

## Reproduction before fixes

`review-cases/stage3-review/test_stage3_regressions.py` is System's file, copied verbatim; its Git blob matches `0ec7cd01`.

At `commit-47` it gives **3 passed, 8 failed**, matching the review. Receipt: `receipts/stage3-repair/red-review-cases-at-commit-47.log`.

## Versioning

The development and trimmed-development checkers change their claim contracts:
- stricter record schemas (S02)
- renamed and redefined holonomy receipt fields (S03)
- populated tolerance policy (S04)

So they are registered as **v2 only**. v1 is not re-registered.

The cut checker's claim contract does not change, so it stays **v1**. Its revision still changes, because the revision hashes the shared checker file.

The verbatim review file calls the development checkers at v1. After the repair those calls hit the version lookup, as happened with the Stage 2 review. An adapted copy, `tests/two_rim_dev/test_review_stage3_adapted.py`, makes only these documented changes:
- checker versions
- the S01 registry fixture, as `ADAPTER-NOTE.md` allows
- the S03 receipt field name

No assertion about geometry is weakened.

## S01: source-linked aggregates in the search

`glab/two_rim/search.py` will:

1. **Run the Stage 2 prerequisites once per search.** It runs `two_rim.check.source` v2 on the material's actual parent source and `two_rim.check.material` v2 on the material, through the Run.
   - If a checker is not registered, the rejected attempt stays in the history and the report says so.
   - The requirement then has no evidence, so the core summary gives `not_run`, never `pass`.
   - If the material has no `two_rim.source` parent, the source-linked result is `not_run` with that reason.
   - Nothing is inferred from ancestry hashes or from an action succeeding.
2. **Keep two clearly labeled local totals:**
   - `full_obligations`: cut claims plus development claims
   - `trimmed_obligations`: cut claims, **the development's exact claims** (`record_schema`, `cut_copy_matches_parent`), and the trim claims

   The development's exact claims are new in the trimmed total; this closes the dropped parent-copy failure. Local totals never include source correspondence, and the report labels them "local".
3. **Add `source_linked_full_obligations` and `source_linked_trimmed_obligations`.** Each is the local total plus every source claim on the source hash and every material claim, including `matches_parent_source`, on the material hash. Every claim is required with coverage `all`.
4. **The trimmed aggregate never requires full untrimmed nonoverlap.** It inherits the exact source, cut, development-copy and map-identity contracts only. A trim is a smaller domain and may remove an overlap.
5. **Optional tolerance policy.** A caller may pass an expected numerical tolerance policy (S04). Numerical requirements are then summarized against it, and exact requirements against `None`. The two summaries combine conservatively.

The search still never imports a checker. It duplicates the Stage 2 claim names, and a consistency test pins them, as for the Stage 3 names.

**New tests:**
- positive complete aggregate with the real Stage 2 v2 bundle
- missing prerequisite checker
- changed source (height 3 source, height 4 material)
- a failed development cut copy
- a seam whose full domain fails but whose trimmed domain may pass: the full failure must not propagate
- local versus source-linked labels

The demo and the view description will show both the local and the source-linked status.

## S02: development and trim schemas enforce their declared meaning

Small explicit validators in the checker, with no schema framework.

**Development:**
- exact key set, schema `two_rim.development/1`, `numeric_domain` `float64`
- `map_convention` must equal the one supported string (image = linear @ xyz + offset)
- maps are finite, non-bool numbers of the right shape, in chain order
- `cut` must be an object
- `generator` must be an object with exactly `name`, `port_of`, `turns_q` and `sum_q`:
  - `name` and `port_of` are strings
  - `turns_q` is a list of finite numbers, one per face
  - `sum_q` is a finite number

  These are shape checks only. The generator's values are never used as evidence.

**Trim:**
- exact key set, schema `two_rim.trim/1`
- `delta` is a canonical exact string
- `height_parameter` must equal the one supported string ("original normalized height t = z/h")
- every trim point is an object with exactly `hinge` (a string), `t` (a canonical exact string), and `xyz` (exactly three canonical exact strings)
- bools, floats, ints and non-canonical spellings such as `"2/4"` or `" 1"` fail
- faces and maps as before

An unsupported record gives `record_schema: fail`, and every dependent claim is `unknown`. Valid records are not repaired or reinterpreted.

**New tests:**
- the four supplied mutations
- malformed nested points: wrong arity, a point that is not an object, extra keys
- a malformed generator block
- a valid canonical-spelling control, including negative and fractional coordinates, that still passes

## S03: principal rotation versus lifted total turn

`_holonomy` will report these separately:

- **`principal_rotation`**: the angle in (−π, π] from the two seam-copy images, and its `principal_rotation_sign`.
- **`lifted_total_turn`**: reconstructed by the checker. It is the sum over chain faces of the principal angle from each face's entry-hinge image to its exit-hinge image. Each hinge image is computed within that face's own image, from the actual material, or from the trim points.
  - The lift is **decided** only if every increment satisfies |increment| ≤ π − 1e-9, the branch margin.
  - Its sign is reported only if the lift is decided and |lift| > 1e-9; otherwise it is `unknown`.
  - A probe over all 1893 golden seams matched the generator's `sum_q` within 8e-15 (E9: −6.2076).
- **`generator_sum_q`**: recorded and explicitly attributed to the generator. Agreement with it is reported but is not evidence.
- **Rotation comparison.** The lift and the principal rotation are compared **modulo 2π**, by wrapped difference. Absolute magnitudes are no longer compared, and there is no `defect_sign` field.

**Outcome:**

| Outcome | When |
|---|---|
| `pass` | the lift is decided, agrees with the principal rotation mod 2π, and agrees with the generator's recorded sum |
| `fail` | a decided lift disagrees with either one |
| `unknown` | the lift is undecided |

**New tests:**
- E9 has a negative lift and a positive principal rotation
- synthetic positive and negative lifts that cross the principal branch
- a near-identity control (translated prism: the sign is `unknown`, and no epsilon sign choice is made)
- an increment at the branch gives an undecided lift

## S04: the tolerance policy goes in `Claim.tolerances`

There is one instance-independent policy object, `NUMERICAL_TOLERANCE_POLICY` (`two_rim.development.numerical/1`), marked as a heuristic, not an error bound. It distinguishes:

| Part | Value |
|---|---|
| Scale rule | max(1, largest absolute coordinate among material points and images) |
| Length tolerance | relative 1e-9 × scale (glued-point agreement, pair separation depth) |
| Rigidity threshold | dimensionless 1e-8 (relative squared-distance error, Gram deviation) |
| Area threshold | length tolerance × scale (nonempty images) |
| Angle threshold | 1e-9 rad (holonomy branch and sign) |

Every numerical claim and numerical diagnostic carries it. Exact claims keep `tolerances: null`. The effective values stay in the receipts.

**Tests:**
- `Run.validate` and `Run.summarize` with the matching policy give current/pass
- a mismatched policy gives `policy_mismatch` and a non-pass summary
- exact claims validate against `None`
- the policy survives save, load and replay

## Verification and return

- Full inherited suite, adapted and verbatim review files, the earlier review cases, the eleven-panel comparison, and the demo with replay. New receipts go in `receipts/stage3-repair/`.
- Update `TWO-RIM-DEVELOPMENT-SCHEMA.md` and `README.md` to the actual interfaces.
- Return `engine/STAGE-3-REPAIR-RETURN.md`, with a short documentation-only Stage 4 proposal.
