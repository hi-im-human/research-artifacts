# Codex Forge return — general static two-rim Lean endpoint

**Verdict: PASS for the September 25 continuation contract, at the existing positive-area two-rim scope.**

The public raw and finite-hull endpoints, the full original cut surface, and one fixed cut/map family for all positive trims now compile. Their recursive axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. No external ordinary-band theorem, T-mixedness, radial-support certificate, supplied safety fact, or supplied development is a public input.

This is **Codex Forge's implementation and verification receipt**, following Summer Bee's authorization to continue Letta-Forge's partial handoff. It is separate from Letta's historical receipts and from the earlier independent paper review. The original `LETTA-FORGE-RETURN.md` remains unchanged.

## Exact public boundary

The new public module is `GeneralTwoRimEndpoint.lean`, in namespace `GeneralTwoRimUnfolding`. Its checked raw inputs are the original `ReducedConvexPolygon` values `A`, `B`, their existing `NeZero` instances, and `hh : 0 < h`.

| Public theorem | Checked conclusion |
|---|---|
| `exists_sameCutSameMaps` | `Nonempty (SameCutSameMapsResult A B hh)` |
| `general_rawCutSurfaceConclusion` | `RawCutSurfaceConclusion A B hh` |
| `general_setSameCutSameMaps` | Canonical presentations, both original rim-body equalities, exact physical-body equality, and the same-cut/same-map result |
| `general_setCutSurfaceConclusion` | The existing `SetCutSurfaceConclusion`, with no mixedness or external-band input |

The set theorems accept only `KA`, `KB`, finite-hull evidence, nonempty planar interiors, and positive physical height. They construct the raw presentations internally. The body is the unchanged Euclidean convex hull of the lower rim at height `0` and upper rim at height `h`.

The complete elaborated types, unchanged contracts, and recursive axiom outputs are saved in [public-types-and-axioms.txt](formal-results/codex-2026-09-25/public-types-and-axioms.txt).

## What the completed result retains

- **Original material:** the unchanged `certificate` domains/charts, original lateral coverage, and actual original hinge segment.
- **One cut:** a single original source seam, with the original cut-index transport.
- **One map family:** `development.U` is literally reused in `every_positive_trim`. Reflexive `_e` and `_U` theorems identify the chosen seam and original direct maps in both nonzero branches.
- **Full safety:** distinct full developed face interiors are disjoint. Boundary contact is permitted by the unchanged `Safe` definition.
- **Full gluing and quotient:** all retained original material hinges are glued, including their endpoints. The existing `CutSurfaceDevelopment` provides continuous developed/material maps, material surjectivity, face inclusion injectivity, cut segment identity, and distinct seam copies at both endpoints.
- **Triangles:** the original domains remain intact. No condition requiring every individual upper/lower rim run to be positive was introduced.

The trim coordinate is the existing normalized height parameter: every `0 < d < 1/2` uses the same stored full-domain maps. The endpoint asserts a static layout, within the two-positive-area-rim model. It does not add arbitrary-polyhedron/slab normalization, collapsed whole rims, cap placement, motion, or full boundary injectivity.

## Completion of the missing positive step

`SelectedPositiveMaterialHit.lean` isolates two small typed consequences of the existing checked geometry: reflection of the actual source point into the normalized strip with height `1-t`, and its `MaterialHit` at the point's own real polar lift.

The previously uncompiled `SelectedPositiveFullSafe.lean` now uses the compiled image-interior boundary to obtain strict physical source coordinates. A collision reflects to one physical normalized point; positive radii identify the two real polar lifts modulo an integer full turn. Recentring the second hit at the first hit's lift lets the existing distinct-face-interior collision theorem exclude it. The literal original-domain/map `Safe` statement is retained.

The repairs were proof engineering: the missing namespace opening, exact finite-index bounds, and separately typed coordinate lemmas. The original combined uncompiled helper is preserved in the initial snapshot. No geometric premise was substituted for the missing proof.

## Source assembly and sign split

`SourceFullDevelopmentAssembly.lean` packages arbitrary original source maps from proved full safety and original gluing. `ArbitraryCutFullDevelopment.lean` supplies the already checked adjacent-hinge theorem for the actual direct maps. These conditional interfaces are internal construction tools; the public endpoint discharges their obligations.

`SelectedPositiveFullDevelopment.lean` supplies the newly proved positive full safety. `SelectedNegativeDirectDevelopment.lean` supplies the inherited, checked negative full-safety theorem. Both consume the same assembly and retain their literal original maps. The zero branch reuses the existing proof that zero intrinsic defect implies T-mixedness and its checked same-map result. Trichotomy then closes the public endpoint.

The inherited `SelectedNegativeFullDevelopment.lean` remains byte-for-byte unchanged. Its fresh rebuild was stopped after 402.56 seconds; **that attempt is not a pass**. The public endpoint imports the new compact negative adapter instead. No fresh standalone rebuild of the unused historical negative wrapper is claimed. This build limitation does not leave an assumption in the completed public theorem.

## Actual source checks

Both new frustum files compile with standard foundational axioms only:

- Upper square `[-1,2]^2`, lower square `[0,1]^2`, height `1`: every actual intrinsic local turn is positive; total defect is positive; shifted T-mixedness fails; both the direct positive construction and general endpoint apply.
- The physically reversed pair: every actual local turn is negative; total defect is negative; shifted T-mixedness fails; both the direct negative construction and general endpoint apply.

These proofs derive directions, hinge vectors, source order and angle signs from the actual polygons. They are not scalar turn assignments. See [frustum-sanities.txt](formal-results/codex-2026-09-25/frustum-sanities.txt).

The endpoint sanity also checks the exact oblique zero-defect source, triangle/square and reversed inputs, an actual collapsed upper facet run, and the previously certified non-nested finite-hull sets. The set application has no external-band argument.

## Codex's fresh verification

| Command / check | Result |
|---|---|
| Positive reflection/material helpers, source and Lake builds | PASS |
| `SelectedPositiveFullSafeSanity` | PASS; 177.55 s, full Safe plus recursive axioms |
| `SourceFullDevelopmentAssembly` | PASS; 68.16 s overall, 18 s new module |
| `ArbitraryCutFullDevelopment` | PASS; 175.81 s |
| `SelectedPositiveFullDevelopment` | PASS; 164.80 s |
| `GeneralTwoRimEndpointSanity` | PASS; 266.67 s, including the fresh negative adapter, public endpoint, types and axioms |
| Both frustum sanity modules | PASS; 39.42 s |
| Unchanged default build | PASS |
| 36 registered baseline modules and the general/radial sanity targets | PASS |
| Seven remaining baseline sanity sources, checked individually | PASS |
| All 43 baseline Lean source hashes | Unchanged |

The project contains 73 Lean sources: the 64 handed-off sources plus nine additions. Among the 64 inherited Lean files, only the previously uncompiled `SelectedPositiveFullSafe.lean` changed. Pins and the default target remain unchanged. The token scan found no source `sorry`, `admit`, custom axiom, `unsafe`, or `implemented_by` bypass; its keyword hits are comments. Recursive public axiom checks independently exclude `sorryAx`.

Lake reused unchanged dependencies where its traces permitted. This is a fresh build/check receipt for the named modules and targets, **not a clean standalone recompilation of every transitive dependency**.

Python suites were independently rerun by path and kept separate:

| Suite | Live count | Exit |
|---|---:|---:|
| Historical geometry/recovery controls | 108 | 0 |
| Position-sensitive packet | 23 | 0 |
| Physical-source floating diagnostics | 8 | 0 |
| Radial-window controls | 10 | 0 |
| Extremal-seam controls | 14 | 0 |
| Folded-turn / RF controls | 14 | 0 |

The historical suite has grown beyond the older handoff's count of 69. Finite exact-certificate and numerical controls are not universal proof evidence; the eight source diagnostics remain floating. Test names, paths and output are included in the results directory.

## Preserved failures and delivery state

The receipt set retains the manually aborted first positive assembly, namespace/index failures, low-heartbeat diagnostics, the 600-second combined assembly timeout, the 180-second scoped-opacity diagnostic timeout, and the stopped historical negative-wrapper rebuild. The first frustum attempt failed on a dependent `Sigma.ext` application; its error-generated `sorryAx` output is a failed receipt, superseded by the fully passing corrected build. No source placeholder was added.

Checkout: `<lean-worktree>`, branch `<private-branch>`, base/HEAD `commit-10`. Existing dirty work and the initial 67-file backup remain preserved. No reset, clean, commit or push was performed in this continuation.

Pinned Lean: `leanprover/lean4:v4.34.0`. Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`. Default: `ConvexSectionNesting`.

Portable evidence and reproduction instructions: [formal-results/codex-2026-09-25/README.md](formal-results/codex-2026-09-25/README.md). Full local logs and preservation snapshot: `<local-temp>\codex-general-lean-20260925`.

All compiler processes launched in this continuation finished or were explicitly stopped. The final checkout process check found zero active Lean/Lake processes.

## Subsequent commit/push authorization — 2026-09-25

Summer Bee subsequently authorized committing and pushing this completed packet to `<private-repo>`. The delivery branch is the existing `<private-branch>`. A fresh combined build of `GeneralTwoRimEndpointSanity`, `GeneralTwoRimReversedFrustumSanity`, and `SelectedPositiveFullSafeSanity` passed in 51.75 seconds (exit 0), with unchanged source hashes and replayed cached dependencies. Its receipt and complete output (trailing whitespace normalized) are included as `pre-push-endpoint-build.json` and `pre-push-endpoint-build.txt` in the results directory.

The staged whitespace check found only an inherited extra blank line at the end of `ArbitraryCutDirectMap.lean`; it is preserved to retain the verified source bytes. The earlier statement that no commit or push had occurred records the continuation's original delivery state, before this new authorization.
