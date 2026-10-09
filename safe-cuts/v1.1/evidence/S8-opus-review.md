---
title: Independent review of the static two-rim band-unfolding theorem and its Lean formalization
author: Opus 5.5 (Anthropic Claude, model id claude-opus-5-5), one Claude Code desktop session
date: 2026-09-25
brief: commit-13 (NON-GPT-REVIEW.md)
implementation-reviewed: commit-11
documentation-snapshot: commit-12
status: independent review record; committed on 2026-09-26 with Summer Bee's authorization, after fast-forwarding main to commit-13; no contributor contacted
dg-publish: false
---

# Independent review: static two-rim unfolding theorem

## Verdicts at a glance

| Question | Verdict |
|---|---|
| Mathematical validity | **Accepted at the stated scope.** No false step found in the paper argument (folded-turn projection, radial support in one frame, max-radius inward seam, winding and cross-component separation, trims and triangles, zero defect). Four exposition gaps, none a gap in the mathematics. |
| Formal-model correspondence | **Match** for the Section 2 claim of the brief. Three qualifications are listed in §2.6. None is a mismatch. |
| Reproduction | **Endpoint closure passes.** All 60 project modules in the endpoint and fixture closure were compiled fresh from the commit-11 sources: every exit code 0, no `sorry`, and every axiom report is within {propext, Classical.choice, Quot.sound}. My four independent Lean checks also compile. Mathlib and its packages were reused as pin-verified binaries, not rebuilt. The 13 remaining modules also compile, 73/73 in all, including the historical negative wrapper that the implementer had stopped. |
| Coverage | Statement layer, quotient, metric, facet construction, and the paper argument read closely. Most large internal Lean proofs were not read line by line; I relied on the kernel for them (§4). |

Nothing here is a blanket acceptance of the whole project. The acceptance covers the four public declarations in `GeneralTwoRimEndpoint.lean` at commit-11, the definitions they unfold to, and the paper argument listed in §1.

## 0. Reviewer, independence and access

**Instance.** Opus 5.5, model id `claude-opus-5-5`, in one Claude Code desktop session on Summer Bee's Windows 11 machine. The session started without the development transcript.

**Prior involvement.** This instance has no memory of contributing to this proof, and nothing in the repository names this session. I cannot rule out correlated error with other Claude-family runs. The provenance file `<historical-folder>/PROVENANCE-AND-LITERATURE-BASELINE.md` (commit-12, §3; this document is included, sanitized, as `supporting-sources/S10-contributions-and-literature.md`) lists a "Claude literature assistant" for the 2026-09-18 literature search and email draft. It also lists "Haven" for numerical probes and diagnostic review, and Haven's local agent file (`haven.md`, a local configuration file not included here) currently specifies `model: claude-opus-4-6`. I could not verify which model ran those earlier passes. Neither is recorded as an author of the proof manuscripts or the Lean code.

**Access.** Local clone `<private-repo-clone>`. `git fetch origin` was needed to obtain commit-13; commit-11 and commit-12 were already present. The fetch moved the remote-tracking ref `origin/main` from commit-12 to commit-13; no local branch changed. I read files with `git show <commit>:<path>`. For the build I used `git archive commit-11` in my scratch directory. The main worktree (`main`, commit-10, clean) and the implementer's worktree `<lean-worktree>` were not reset, cleaned, moved, built in, or edited. In `<lean-worktree>` I only read files: package revisions and file hashes. Its `.lake/packages` were copied read-only (robocopy) into my scratch area. Nothing was inaccessible.

**Reading order.** I followed the brief's staging. My notes were saved in the session scratchpad at these times (UTC):

- 21:24, step-1 obligations, before opening any Lean.
- 21:32, first-pass statement audit, before any manuscript or receipt.
- 21:47, second-pass mathematics, before any `*RETURN*`, receipt or results file.

The notes are reproduced in Appendix A. One limitation: `THEOREM-NOTE.md` §2 already summarizes compiler outcomes ("only propext, Classical.choice, Quot.sound"). The brief assigns that note to the second pass, so I read it after my first-pass statement audit was saved, but before my own build finished.

## 1. Mathematical validity

**Scope accepted.** The scope is the static, lateral-only statement of brief §2, for all finite-hull rims with nonempty interiors and all h>0. The surface is the explicit quotient described in §2 below. Boundary contact is allowed. No caps, motion, prescribed hinge, global boundary injectivity or slab normalization is claimed, and none of those exclusions is counted against the result.

I checked each step from its hypotheses, then its application. Section references are to the manuscripts at commit-11 (paths under `O = <research-record>/`).

### 1.1 Source geometry (SYSTEM-TO-CODEX-FORGE §1–6; Lean `PhysicalMixedTurnSource`)

- **Middle section.** The height-h/2 section is (A+B)/2. It has one edge per lateral facet, with exterior turns τ_i ∈ (0,π) summing to 2π.
- **Retained lengths.** On a trim δ∈(0,1/2): b(δ) = (1−δ)b + δa and a(δ) = δb + (1−δ)a. Both are positive whenever a+b>0, so original triangles (a=0 or b=0) cause no division by zero.
- **Intrinsic turn.** q_i = ∠(u_i,G_i) − ∠(u_{i−1},G_i). The Gram identity (1−x²)(1−y²) − (c−xy)² = (w_z·det(u_{i−1},u_i))² > 0 gives cos q_i > cos τ_i, hence |q_i| < τ_i and Σ|q_i| < 2π. I verified the algebra; Lean has `abs_intrinsicQ_lt_middleExteriorTurn` and `intrinsic_sum_abs_lt_two_pi`.
- **Charts and gluing.** The canonical charts ψ_i send the hinge E_{i+1}'s upward unit vector to (cos φ⁺, −sin φ⁺) in chart i+1 and to (cos φ⁻, −sin φ⁻) in chart i. So R(q_{i+1}) plus the midpoint translation glues the whole hinge line. The two incident faces fall on opposite sides of the hinge: det = −sin φ⁻ < 0 on one side and sin φ⁺ > 0 on the other. Every panel has det(e,d) = −b(δ)(1−2δ)s < 0, so the orientation is coherent.

### 1.2 Folded-turn projection lemma (FOLDED-TURN-RF §1): verified

The indexing includes the closing interval [s_{n−1},2π], with gap τ_0 and change q_0, and θ_n = Δ.

- Θ is κ-Lipschitz, where κ = max|q_i|/τ_i < 1.
- Set g = Θ − Δ/2 and f = |g|. Then f(0) = f(2π) = |Δ|/2, so f (not g) is periodic, which is the point of the half-shift. The IVT gives a zero α of g.
- Going around both arcs gives f(s) ≤ κ·d(s,α) ≤ d(s,α) ≤ π, strictly when d(s,α) > 0.
- Hence cos(θ_j − Δ/2) = cos f(s_j) ≥ cos(s_j − α), strictly away from α.
- Closure gives Σ a_j cos(s_j − α) = 0. Some a_j > 0 must sit away from α, since a positive multiple of a single unit vector cannot sum to zero. So Π > 0.

Zero weights are allowed. `FoldedTurnProjection.Chain` encodes exactly these hypotheses: positive gaps, |turn| < gap, n+2 knots including the closing interval, nonnegative weights with positive sum, and both closure sums.

### 1.3 Radial support (RF) from the full affine circuit (FOLDED-TURN-RF §2–3): verified

- E_i = Σ_j a_{i+j} Rot(θ_j) v, because a face's developed upper edge is parallel to its developed middle edge.
- E_i = H(Y_0) − Y_0 = (Q−I)(Y_0 − O). This uses the full affine H, with the translation kept.
- Q − I = 2 sin(Δ/2) Rot(Δ/2) J and dot(v, Jx) = det(x, v). Therefore Π_i = 2 sin(Δ/2) det(Y_0 − O, v). I checked this identity by hand.
- **Δ<0.** Here det(U_i − O, v_i) < 0. Coherent orientation (§1.1) gives det(G_i, v_i) > 0, and L_i = U_i − G_i, so det(L_i − O, v_i) = det(U_i − O, v_i) − det(G_i, v_i) < 0.
- **Δ>0.** Lower-rim closure gives det(L_i − O, v_i) > 0, and then det(U_i − O, v_i) > 0.
- **Transport between signs.** One global reflection S plus the rim swap (b′ = Sa, a′ = Sb, e′ = λSe, d′ = −Sd) keeps det(e′,d′) = λ·det(e,d), flips every radial determinant and flips Δ. I verified this.
- **Conjugacy, not repositioning.** In one baseline frame the chain satisfies φ_{k+n} = H∘φ_k. So a circuit started at any face is the same H with the same pole O, and changing frames is one rigid motion under which every inequality is invariant. Lean: `FixedBaselineCyclicConjugacy` (`baselineAlignment_circuitPole`, `baseline_physical_negative_RF`, `baseline_physical_positive_RF`).

### 1.4 Seam selection, winding and global separation (EXTREMAL-SEAM §2–4, POLAR-WINDOW §3, §5): verified

- **Inward hinge from the max-radius vertex.**
  - The two neighbour inequalities give a·f ≥ |f|²/2 and a·e ≤ −|e|²/2. Wrapped neighbours are Q^{±1} copies, which have the same radius.
  - Adding R gives f_x > 0, f_y < 0, e_x < 0, e_y < 0, hence det(f,e) < 0.
  - Coherent orientation gives det(f,g) < 0 and det(e,g) < 0. For the incoming panel this uses d_k = d_{k−1} + (λ−1)e_{k−1}.
  - Cramer's rule gives g = A(−f) + Be with A, B > 0, so a·g < 0.
  - The squared-radius identity (t₂−t₁)[2a·g − (2−t₁−t₂)|g|²] < 0 then shows the hinge is strictly radially inward.
- **Winding.** η = θ − φ ∈ (−π,0) is forced by R. At a hinge both η values lie in (−π,0), so their difference is in (−π,π) and is congruent to q_i with |q_i| < π; the two are therefore equal as real numbers. After one circuit η returns to its start, so the lifted polar sweep is exactly Δ, not merely Δ mod 2π.
- **One ray, all heights.**
  - The seam lies in an open half-plane about O, so its polar angle α is monotone with range ω < π.
  - At height t the section covers lifted angles exactly [α(t) − L, α(t)], with L = −Δ ∈ (0,2π).
  - The eligible heights for each lift form a closed interval, and there are at most two such intervals, because ω + L < 3π.
  - Within one lift the radius is r_i(t) = [det(b_i,e_i) + t·det(d_i,e_i)]/det(v,e_i). Every slope is strictly negative (det(v,e_i) < 0 by R, det(d_i,e_i) > 0), and the pieces agree at retained hinges.
  - Where two components face each other, the endpoints are the root seam and its Q-copy. They have equal radius, and the seam is strictly inward, so every radius on the lower component exceeds every radius on the upper one.
  - At equal heights, points are separated by strict polar advance together with L < 2π.
  - So cross-component separation comes from the seam comparison, not from per-panel slope signs alone.
- **Triangles and one cut.**
  - The lexicographic coefficient triple selects one index k that maximizes every small trim.
  - Letting δ→0 gives U_k·G_k ≤ 0. With G_k ≠ 0 and 2 − t₁ − t₂ > 0, the whole original hinge is strictly inward.
  - So the same k and the same full maps are safe at every δ ∈ (0,1/2).
  - A full-face interior overlap would have preimages at strictly intermediate heights and would survive a small trim. This is formalized as `FiniteWitnessClosure.fixed_overlap_survives`.

### 1.5 Zero defect (THEOREM-NOTE §3.6, MixedTurnSafeCut, SYSTEM-TO-CODEX-FORGE §7–8): verified independently of the pole route

- Δ = 0 gives P = N, and P + N = Σ|q| < 2π gives P = N < π.
- `intrinsicTMixed_of_intrinsicDelta_eq_zero` (GeneralTwoRimUnfolding.lean:73) shows that some q_i ≤ Δ ≤ some q_j, by averaging.
- `mixed_budget_selection` then yields a cut whose two retained budgets are both below π.
- The developed headings therefore stay inside an open interval of width less than π. So there is a common forward direction, the strip is monotone in that direction, and its trace slopes share one sign. This gives injectivity (`small_variation_injective`, `mixed_family_safe_cut`).
- No pole and no division by sin(Δ/2) is used, so a pure-translation holonomy is harmless.

### 1.6 Exposition gaps (incomplete exposition, not mathematical defects)

| # | Location | Gap | Why it is not a hole |
|---|---|---|---|
| X1 | FOLDED-TURN-RF §3.3; EXTREMAL-SEAM §1 | The positive-Δ reflection/rim-swap transport is described in one paragraph. | I checked the transport identities (§1.3). Lean proves the positive branch through its own `SelectedPositive*` modules. |
| X2 | FOLDED-TURN-RF §3.2, eq. (8) | "Established source orientation det(v_i,G_i)<0" is imported, not re-derived. | It is derived in SYSTEM-TO-CODEX-FORGE §6: det(e,d) = −b(1−2d)s < 0. |
| X3 | EXTREMAL-SEAM §1, §3 | The winding lemma (lifted sweep = Δ) is cited, not restated. | Stated and proved in POLAR-WINDOW §3; I checked it (§1.4). |
| X4 | THEOREM-NOTE §3.4 | The synthesis omits why facing endpoints are seam copies (equality in the eligibility constraint) and the "at most two components" bound. | Both are in EXTREMAL-SEAM §3.1 and §3.3. |

**Mathematical verdict:** proof accepted at the explicit scope above. I found no false implication and no counterexample. No counterexample is proposed at any level: not as a scalar array, not as a free strip, not as a realizable source.

## 2. Formal-model correspondence

`L` = `<lean-project>/` at commit-11 (included as `formal/`).

### 2.1 Public endpoints and their inputs

`L/GeneralTwoRimEndpoint.lean`, namespace `GeneralTwoRimUnfolding`:

| Declaration | Inputs | Conclusion |
|---|---|---|
| `exists_sameCutSameMaps` (l.22) | `A B : ReducedConvexPolygon`, `hh : 0 < h` | `Nonempty (SameCutSameMapsResult A B hh)` |
| `general_rawCutSurfaceConclusion` (l.30) | same | `∃ e, Nonempty (CutSurfaceDevelopment A B hh Plane e)` |
| `general_setSameCutSameMaps` (l.38) | `KA KB : Set Plane`, `∃ S : Finset, convexHull S = K`, `(interior K).Nonempty`, `0 < h` | `PA.polygon.body = KA ∧ PB.polygon.body = KB ∧ physicalBodyOfSets KA KB h = physicalPrismatoid PA.polygon PB.polygon h ∧ Nonempty (SameCutSameMapsResult …)` |
| `general_setCutSurfaceConclusion` (l.56) | same | `SetCutSurfaceConclusion …`: the same three identities plus `∃ e, Nonempty (CutSurfaceDevelopment …)` |

None of these takes a cut, a development, a `Safe` fact, a radial certificate, `IntrinsicTMixed`, a nesting assumption or an external band theorem as input. The branch lemmas that do take `hΔ` or `hmix` are all discharged inside `exists_sameCutSameMaps`: trichotomy for the sign, and `intrinsicTMixed_of_intrinsicDelta_eq_zero` for the zero case.

### 2.2 Definition-by-definition correspondence with brief §2

| Brief §2 requirement | Formal object | Assessment |
|---|---|---|
| A, B are hulls of finite planar sets with nonempty interior | `canonicalPresentation` = `Classical.choice (exists_reduced_polygon_of_polygon_set …)`, with `RawPresentation.body_eq : polygon.body = K` | Covers every such set. Redundant and collinear generators are removed internally (`exists_minimal_generators`). |
| Euclidean plane and 3-space | `Plane = EuclideanSpace ℝ (Fin 2)`; `PhysicalAmbient = EuclideanSpace ℝ (Fin 3)` (EuclideanPrismatoidCoordinates.lean:18) | L2 metric. The max-norm `Ambient = Plane × ℝ` is used only for membership algebra, through the linear map `pack`. The file itself warns about this. |
| K defined independently: B at 0, A at h | `physicalBodyOfSets` = hull of the lifted sets (PolygonSetReconstruction.lean:395); `physicalPrismatoid` (EuclideanPrismatoidCoordinates.lean:61) | Correct, with B at the bottom. The set theorem states the equality to these sets as part of its conclusion. |
| Maximal lateral facets | `Side A B` = unit edge normals of A and B, deduplicated; row `sideRow h u`; `halfspaces_body : (halfspaces A B h).body = physicalPrismatoid A B h`; `materialFace u = body ∩ {sideRow u = 0}` | Each face is the whole supporting-plane face, so a trapezoid is one face. `samples_strict` and `center_interior` show every row is facet-defining (nonempty 2D relative interior). Because the H-representation equals K, every lateral facet of K is some row. |
| Excluding cap interiors | `lateralBoundary H = {p ∈ body ∣ ∃ non-cap row k, row k p = 0}` and `constructed_lateral_coverage` | This is exactly the union of the lateral facets, rims included. |
| Faces mapped isometrically | `FaceSpace = ker sideLinear` (2-dimensional, `faceSpace_finrank`), `chart x = origin + x` with `norm_map := rfl`, `U i : FaceSpace →ᵃⁱ[ℝ] Plane` | Genuine Euclidean affine isometries of each face plane. |
| Original lateral hinge e | `e : Fin (sideCount A B)`; `cut A B hh e` is an `OriginalEdge` between `order e (last)` = `cycle e` and `order e 0` = `cycle (e+1)` | `cut_segment` states that the two faces meet exactly in the segment between the lifted rim vertices. |
| Continuous development of the opened surface | `CutSurfaceDevelopment.developedMap : CutSurface → Plane`, continuous; `developed_face` fixes it to `U i` on every face piece | See §2.3 for the quotient. |
| Distinct face-image interiors disjoint | `Safe F U := ∀ i j, i ≠ j → Disjoint (interior (U i '' F i)) (interior (U j '' F j))`, interior taken in `Plane` | All pairs are quantified, not only neighbours, and the predicate is not vacuous (§2.4). Boundary contact is allowed, as intended. |
| Same e and same U on every trim 0<d<1/2 | `SameCutSameMapsResult.every_positive_trim` uses `development.U` literally; `heightTrim F z d = F ∩ {d ≤ z ≤ 1−d}` with `z = certificate.height` = z/h | Matches `∃e ∃U, Full ∧ ∀d, Trimmed`. |

### 2.3 Material identifications: the explicit quotient is the one-cut annulus

`CutSurfaceQuotient.CutRelated x y` holds when x and y have the same ambient point **and** that point lies in `materialFace (order e k)` for every opened index k between x.1 and y.1. The relation is fixed by the definition and is not supplied by the caller. My audit of it:

- **No extra cut.** Every point shared by adjacent opened faces is related, by `adjacent_cutRelated`. `DevelopmentOn`'s first clause requires adjacent faces to agree at every common ambient point, which is the whole common edge. Non-adjacent identifications, such as a rim vertex shared by a run of faces, follow by chaining (`developed_eq_forward`). A surjective material map alone would not show this; the relation's definition does.
- **High-valence rim vertices.** The faces containing any lateral point form one contiguous cyclic run, and that run is never the whole cycle. If the run does not contain the seam, it is an interval of the opened order and the vertex is one class. If it does contain the seam, it splits into [j..N−1] and [0..i] and the vertex becomes two classes. This is exactly the slit annulus.
- **Nothing over-identified.** Membership in every intermediate face plus equal ambient point is also necessary for being the same point of the slit surface.
- **The seam really is cut.** `seam_copies_ne` proves that the two copies of every seam point, endpoints included, are distinct classes. The proof exhibits a face (`lowerMissingSide`, or `upperMissingSide` at t=1) that misses the seam point.
- **The chain is K's real cycle.** `MaterialAdjacent` is defined independently (two distinct faces meeting at a strictly interior height). `original_cycle_adjacency` shows it holds exactly for cyclic successors, and `everyOriginalEdge_cyclic` shows every certified edge is cyclic.
- **Quotient points versus planar images.** The quotient keeps the seam copies apart even if their planar images happen to coincide. `Safe` constrains only face interiors, so boundary contact, including contact between the seam images, is allowed. That is the stated convention.

### 2.4 Non-vacuity

Each face domain has a point in its 2D interior (`center_interior`). Each `U i` is an isometry between two 2-dimensional spaces, hence open. So every developed face image has nonempty planar interior, and `Safe` is a real constraint. I re-proved this myself in Lean as `OpusReviewChecks.face_image_interior_nonempty`; see §3.4.

### 2.5 Soundness scan of all 82 files at commit-11

The scan found no `sorry`, `admit`, `axiom` declaration, `native_decide`, `implemented_by`, `@[extern]`, `unsafe`, `opaque`, `run_cmd`, `#eval`, custom `elab`/`macro`/`syntax`, `debug.*` option or `Lean.Elab`/`Lean.Meta` import. The only `set_option`s are `maxHeartbeats` (including one `0`), `autoImplicit false` and `pp.proofs false`. The lakefile has no `leanOptions`. `MutationRejected.lean.fail` is not a `.lean` file and is not built.

### 2.6 Qualifications (not mismatches)

1. **Quotient, not slit-surface homeomorphism.** "Continuous development" means continuity on the explicit quotient topology. No theorem identifies that quotient with a disk or with an independently defined slit completion. The brief says this absence is not a counterexample. My argument in §2.3 shows the identifications are the right ones.
2. **Per-face orientation is not fixed by type, but it is forced.** Each `U i` may reflect. With 2D faces, whole-edge agreement and disjoint adjacent interiors put consecutive faces on opposite sides of their hinge. So U is the genuine edge-unfolding up to one global isometry. This is my argument, not a Lean theorem, and it is not an escape route.
3. **The trimmed clause adds little.** It follows from the full clause, since sub-domains have smaller image interiors and gluing restricts. I checked this in Lean as `OpusReviewChecks.trimmed_safe_of_full`. Storing it is correct but does not strengthen the result.

**Formal-model verdict: match.** The public types express brief §2 exactly for every finite-hull input with nonempty interiors and every h>0, subject to the three qualifications above.

### 2.7 Cosmetic source issues (documentation only)

- **D1.** `MergedNormalPrismatoid.lean:32` names `rotateCW v = (−v₁, v₀)`, which is a counter-clockwise quarter-turn. The docstring at l.41 says "counterclockwise cyclic polygon", but `supports` (l.49) forces clockwise vertex order, and `OriginalFacetCertificates.lean:11` says "raw clockwise polygons". The definitions are consistent with each other; only the names and comments are not.
- **D2.** Fourteen compiled modules still carry "UNCOMPILED DRAFT" / "NOT COMPILED" headers: BandGeometryAssembly, CommonSupportMerge, CyclicCutOrders, CyclicCutOrdersSanity, EuclideanPrismatoidCoordinates, FiniteWitnessClosure, MaximalSupportCells, NormalFanSplice, OriginalFacetCertificates, PolygonSupportCompleteness, PolygonSupportCompletenessSanity, PolyhedralInputBridge, SingleCutRecovery, TrimmedFacetWitnesses.
- **D3.** Several module headers describe premises, such as external band theorems, that the final endpoint no longer uses. Examples are PolyhedralInputBridge.lean:17–19 and FiniteWitnessClosure.lean:13–17. A reader has to know which theorems are conditional adapters.

## 3. Reproduction

### 3.1 Environment and pins

| Item | Value | How checked |
|---|---|---|
| Host | Windows 11 Home 10.0.26200; i9-13900KF; 32 GB RAM | — |
| Lean | 4.34.0, x86_64-w64-windows-gnu, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Release | `lean --version` from `~/.elan/toolchains/leanprover--lean4---v4.34.0/bin` |
| Project sources | all 82 tracked files of `L` at commit-11, via `git archive` into scratch | 82/82 match the tree's git blob IDs (`git hash-object`) |
| Mathlib | `5ed2965256430c3649e86755f9576b54eca72435` (tag v4.34.0) | `git rev-parse HEAD` in the copied package; clean working tree |
| Other packages | batteries `f2effa3…`, aesop `355695d…`, Qq `6a489d9…`, proofwidgets `106ff4f…`, plausible `118aa17…`, importGraph `e928b72…`, LeanSearchClient `ddf04cf…`, Cli `e92c9f1…` | each equals `lake-manifest.json`; each working tree clean |
| Package bytes | 144,505 files, 7.506 GB, copied from `<lean-worktree>\…\.lake\packages` with robocopy (0 failed) | robocopy log |

I inspected the pins and did not update them.

### 3.2 Method, and what was fresh versus reused

1. **Lake could not run from the scratch location.** `lake build MergedNormalPrismatoid` replayed Mathlib up to job 6257 of 6281. It then stopped with "no such file or directory" on `…/Rpow/IntegralRepresentation.olean.server.hash`, a 267-character path. That file exists. `lean.exe` itself wrote a 324-character path without trouble. This is tool limitation T1.
2. **I compiled with `lean.exe` directly instead.** A small driver resolves each module's local imports, orders them topologically and runs `lean -R <proj> -o out/M.olean -i out/M.ilean M.lean`. `LEAN_PATH` holds the nine package `lib/lean` directories plus a new, empty `out/`. Four jobs ran in parallel, and every module's command, exit code, elapsed time and output was logged.
3. **What was fresh:** every one of the 60 project modules in the import closure of `GeneralTwoRimEndpointSanity`, `GeneralTwoRimFrustumSanity` and `GeneralTwoRimReversedFrustumSanity`, compiled from source. No project `.olean` was copied from anywhere. The closure contains the 52-module closure of `GeneralTwoRimEndpoint`.
4. **What was reused:** Lean core, Mathlib and the eight other packages, as prebuilt `.olean` files. They were neither rebuilt nor kernel-replayed (T2, T3).

### 3.3 Results of the fresh compile (run 21:40:23 → 22:36:31 UTC)

| Check | Result |
|---|---|
| Modules compiled | 60/60, every exit code 0; sum of per-module times 4,774 s |
| Error diagnostics | none |
| Any `sorry` in any output | none |
| `#print axioms` reports across all 60 logs | 307 reports: 306 are exactly `[propext, Classical.choice, Quot.sound]`, and one is a subset (`[propext, Quot.sound]`). None mentions `sorryAx` or any other axiom. |
| `exists_sameCutSameMaps`, `general_rawCutSurfaceConclusion`, `general_setSameCutSameMaps`, `general_setCutSurfaceConclusion` | each `[propext, Classical.choice, Quot.sound]` |
| Endpoint sanity fixtures: shifted square (Δ=0), triangle/square and reversed (collapsed upper run), non-nested finite hulls | compile, standard axioms |
| Positive-defect frustum (`frustum_delta_pos`, `frustum_not_tmixed`, `frustum_general`, `frustum_selected_positive`) | compile, standard axioms |
| Reversed frustum (`frustum_delta_neg`, `frustum_not_tmixed`, `frustum_general`, `frustum_selected_negative`) | compile, standard axioms |
| Slowest modules | PhysicalMixedTurnState 923 s, SelectedRootInteriorWitness 822 s, PhysicalMixedTurnLayout 544 s; the other 57 each took under 206 s |

### 3.4 My own Lean checks

I wrote a scratch file, `OpusReviewChecks.lean`, and compiled it against the fresh build. It is not part of the project.

| Declaration | What it establishes | Axioms |
|---|---|---|
| `face_image_interior_nonempty` | For any returned development, every face image has nonempty planar interior, so `Safe` is not vacuous. | standard 3 |
| `adjacent_faces_glued` | Adjacent opened faces are equal in the quotient at every common material point: no extra cut. | standard 3 |
| `trimmed_safe_of_full` | Full safety implies safety at every height trim with the same maps. | standard 3 |
| `restated_set_endpoint` | Derived from `general_setSameCutSameMaps`. For any finite-hull KA, KB with nonempty interiors and any h>0, there exist presentations with `body = K`, the physical-body equality, a cut e and maps U, satisfying: exact lateral coverage; agreement at every common point of every adjacent pair; pairwise disjoint image interiors for *all* distinct faces; nonempty image interiors; and `Safe` at every trim 0<d<1/2. | standard 3 |

**First attempt failed, and is preserved as such.** I had not opened `EuclideanPrismatoidCoordinates`, so `autoImplicit` turned `physicalPrismatoid` into a bound variable. Lean reported an error, and `restated_set_endpoint` showed `sorryAx` in its axioms (`checks-attempt1-FAILED.log`). The other three checks already passed in that attempt. Attempt 2 added the `open` and `set_option autoImplicit false`, and compiled with exit 0 and standard axioms only.

### 3.5 Comparison with the stored receipts

| Stored item | Verdict |
|---|---|
| `public-types-and-axioms.txt` | Consistent. The types match the sources I read, and the axiom lists match my fresh run. |
| `source-audit.json` | 58 of 73 hashes match the committed blobs as bytes (48 directly, 10 as CRLF). All 73 match the implementer's working tree. The other 15 come from mixed line endings (E1); their content equals the blobs. |
| `command-receipts.json` | 33 commands. The 23 marked `required_final_pass` all exited 0. Ten failed or aborted attempts are kept and marked non-required: two timeouts (600 s and 180 s), namespace/index failures and the two manual stops. This matches the README and the return. |
| Abort notes | Consistent with the receipts. The 402.56 s endpoint run was stopped while it rebuilt `SelectedNegativeFullDevelopment`, and it is not claimed as a pass. My fresh compile of that module passes (§3.6). |
| `pre-push-endpoint-build.*` | 51.75 s, exit 0, with project modules *replayed* from cache (E2). |
| Config hashes | `lean-toolchain` and `lake-manifest.json` match after line-ending normalization. `lakefile.toml` differs only by mixed endings; its content is identical. |

### 3.6 Remaining 13 modules

After the endpoint run I compiled the other 13 modules the same way (22:37:13 → 22:57:35 UTC). They were:

- BandGeometryAssemblySanity, CommonSupportMergeSanity, FiniteWitnessClosureSanity, FixedBaselinePolarTraceSanity
- GeneralTwoRimUnfoldingSanity, MixedTurnSafeCutSanity, NormalFanSpliceSanity, OriginalFacetCertificatesSanity
- PolygonSupportCompletenessSanity, RadialOriginalSeamSanity, SelectedPositiveFullSafeSanity, SingleCutRecoverySanity
- SelectedNegativeFullDevelopment

**Results.** All 13 exited 0. Across all 73 logs:

- 356 `#print axioms` reports, each within {propext, Classical.choice, Quot.sound};
- no error diagnostics;
- no `sorry`.

The sum of per-module times was 6,136 s.

**The historical wrapper.** `SelectedNegativeFullDevelopment` sets `maxHeartbeats 0`. The implementer stopped its rebuild at 402.56 s and did not claim it. Here it compiled in 1,190.0 s with exit 0. Its six reported declarations (`selectedNegativeSameCutSameMaps`, `…_U`, `selectedNegativeCutSurfaceDevelopment`, `…_U`, `selectedNegativeDirectMap_allUncutGlued`, `selectedNegativeDirectMap_full_developmentOn`) use only the standard axioms.

This module is outside the public endpoint's closure, so the result does not affect the endpoint. It closes the open item recorded in the return: the unused wrapper compiles when given about 20 minutes.

### 3.7 Reproduction verdict

All 73 project modules at commit-11 compile from source into a fresh output directory. That includes the public endpoint, its complete project dependency closure, every sanity file and the historical wrapper. They use only the standard three axioms and no `sorry`. Mathlib and the other packages were reused from a pin-verified binary cache, not rebuilt.

## 4. Coverage

### 4.1 Read closely

**Lean statement layer, read in full or in the relevant parts:**

- `GeneralTwoRimEndpoint`
- `GeneralTwoRimUnfolding`
- `GeneralTwoRimEndpointSanity`
- `CutSurfaceQuotient` (all 696 lines)
- `FiniteWitnessClosure` §§Height/Witnesses
- `BandGeometryAssembly` (`DevelopmentOn`, `planeEquiv`, `image_interior_eq`)
- `TrimmedFacetWitnesses` (`heightTrim`)
- `PolyhedralInputBridge` (all)
- `OriginalFacetCertificates` (all)
- `EuclideanPrismatoidCoordinates` (all)
- `MergedNormalPrismatoid` (all)
- `CommonSupportMerge` (rays and support definitions)
- `CyclicCutOrders` (cycle, order, hinge, cut)
- `MaximalSupportCells` (adjacency characterization)
- `PolygonSetReconstruction` (presentation and body)
- `PhysicalMixedTurnSource` (conclusions, intrinsic q/Δ/T-mixed)
- `MixedTurnSafeCut` (declaration map and opening)
- `FoldedTurnProjection.Chain`
- `ArbitraryCutDirectMap`
- `ArbitraryCutFullDevelopment`
- `SelectedNegativeDirectDevelopment`
- `SelectedPositiveFullDevelopment`

**Manuscripts:** `THEOREM-NOTE.md` §1–4 (commit-12), `FOLDED-TURN-RF.md` §0–4, `EXTREMAL-SEAM.md` §0–8, `POLAR-WINDOW.md` §1–6 and `SYSTEM-TO-CODEX-FORGE.md` §0–8 (commit-11).

**Receipts (third pass):**

- `CODEX-FORGE-RETURN.md`
- `results/codex-2026-09-25/README.md`, `public-types-and-axioms.txt`, `source-audit.json`, `command-receipts.json`, `verification.json`, `pre-push-endpoint-build.json`/`.txt`, `frustum-sanities.txt`, `upstream-axioms.txt`, and both abort notes
- `PROVENANCE-AND-LITERATURE-BASELINE.md` §3, read for the independence disclosure only

### 4.2 Not examined line by line (kernel-trusted, via my fresh compile)

These proofs I did not read line by line; I rely on my fresh compile running the Lean kernel over them:

- the negative and positive root-polar lifts: `SelectedNegativeRootPolarLift` (2310 lines) and `SelectedPositiveRootPolarLift` (1809 lines);
- the seam selection and radial support: `RadialOriginalSeam`, `RadialExtremalSafety`, `PhysicalRadialSupport`;
- the fixed-baseline modules: `FixedBaselinePolarRayGeometry`, `FixedBaselinePolarTrace`, `FixedBaselineCyclicConjugacy`;
- the physical mixed-turn construction: `PhysicalMixedTurnGeometry`, `PhysicalMixedTurnDevelopment`, `PhysicalMixedTurnLayout`, `PhysicalMixedTurnState`;
- the remaining proofs in `NormalFanSplice`, `CommonSupportMerge` (`physicalPrismatoid_eq_merged_halfspaces`), `PolygonSetReconstruction`, `PolygonSupportCompleteness`, `SingleCutRecovery`, `SelectedPositiveFullSafe`, `SelectedRootInteriorWitness`, `SelectedNegativeHingeGluing` and `SourceFullDevelopmentAssembly`.

I read these only for their statements where the argument needed them. That is enough for the theorem, because the public statement and every definition it unfolds to were audited in §2.

### 4.3 Dependencies not examined

- **Mathlib at 5ed2965 and its companion packages.** I reused their prebuilt oleans without rebuilding or replaying them, so their correctness is trusted.
- **The Lean 4.34.0 kernel** and the three standard axioms.
- **The Python regression suites.** I did not rerun them; they are not part of the proof.
- **The historical manuscripts** before the brief's route: the uniform-sign residual, the earlier window reviews, the 69-suite history.
- **The Aloupis thesis and all literature or priority questions.** The brief excludes these.
- **The 13 modules outside the endpoint closure.** I compiled them (§3.6) but did not read them.

### 4.4 Access and tool limitations (not proof defects)

- **T1.** `lake.exe` 5.0.0 on this host cannot open Mathlib cache paths longer than 260 characters when the project sits in the session scratch directory. `lean.exe` can. I therefore compiled with `lean` directly (§3.2). This does not change what is checked, but it is not a Lake-native build.
- **T2.** I did not run a `leanchecker` kernel replay. `leanchecker --help` is not a supported option: it started a replay that reached 19 GB of memory, and I terminated it. I did not attempt a `--fresh` replay of Mathlib.
- **T3.** I did not rebuild Mathlib from source.

## 5. Findings by category

| Category | Findings |
|---|---|
| False theorem | None found. |
| Formalization mismatch | None found. |
| Incomplete exposition | X1–X4 (§1.6); D1–D3 (§2.7). |
| Evidence and record | E1–E3 below. |
| Access and tool limitation | T1–T3 (§4.4). |

- **E1. Stored source hashes cannot be reproduced from git byte-for-byte for 15 of 73 files.**
  - *Affected files:* `source-audit.json`; `lakefile.toml` is affected the same way.
  - *Cause:* the hashes were taken of working-tree files with mixed CRLF/LF line endings: BandGeometryAssembly, CommonSupportMerge, CyclicCutOrders(+Sanity), FiniteWitnessClosure, both frustum sanities, HingeExtensionUniqueness, MaximalSupportCells, NormalFanSplice, OriginalFacetCertificates, PolygonSupportCompleteness(+Sanity), PolyhedralInputBridge, SelectedPositiveFullSafe. Git normalizes line endings, so no checkout reproduces those bytes.
  - *What I verified:* all 73 stored hashes equal the implementer's current working-tree files in `<lean-worktree>`, which I read-only hashed. Every one of those files equals the committed commit-11 blob after line-ending normalization.
  - *Consequence:* the audited sources are the committed sources. This is a record-keeping weakness, not a content discrepancy. Recording git blob IDs would make the audit reproducible.
- **E2. The final pre-push receipt replayed cached project modules.** The implementer disclosed this; it does not claim otherwise. My run in §3 supplies a fresh compile of every project module in the endpoint closure.
- **E3. THEOREM-NOTE §2 relied on the implementer's receipts.** It says: "System did not perform another Lean compilation." The records I inspected contain no earlier compilation of the endpoint by a non-author; §3 of this report is one.

## 6. Smallest justified next action

With Summer Bee's authorization, commit this report as a new file. No change to the proof, the Lean sources, the pins or the historical records is justified by this review.

The E1 and D1–D3 items are optional. They are documentation-only, and a separate authorized change could address them: record git blob IDs in the audit, and correct stale headers and orientation names. They do not affect the result.

## Appendix A. Pre-receipt notes, verbatim

These are the notes I saved during the first two passes, reproduced without edits. Where later work changed a judgement, Appendix B says so.

### A.1 Step-1 obligations (saved 21:24 UTC, before any Lean was opened)


Written 2026-09-25T21:24Z, after reading NON-GPT-REVIEW.md (commit-13) and before
opening any Lean source, manuscript, receipt, RETURN/AUDIT/ACCEPTANCE file.

#### Geometry I expect (my own derivation)

K = conv(B x {0} U A x {h}), A,B convex polygons with nonempty interior, h > 0.
For a horizontal direction u, the support face of K in the lateral direction
(u, t) with t = (h_B(u) - h_A(u))/h is conv(F_B(u) x 0, F_A(u) x h), where F_X(u)
is the u-face (vertex or edge) of X. It is 2-dimensional iff u is an edge
normal of A or of B. So lateral facets <-> merged set of edge normals of A and
B (N of them, N >= 3); a facet is a triangle (only one polygon has an edge with
that normal) or a trapezoid (both do). Between consecutive merged normals the
face is a segment b--a: these are the N lateral hinges. Lateral surface = an
annulus; consecutive facets meet exactly in their common hinge; a rim vertex
lies in a contiguous (non-cyclic) run of facets.

#### Obligations for the claimed statement

1. Inputs: every pair of finite planar sets with nonempty-interior hulls and
   every h > 0 must be covered; no general-position restriction (collinear
   generators, parallel edges of A and B, equal/homothetic/translated
   polygons, triangles only, very small or large h, non-nested/disjoint
   projections).
2. Faces: the maximal lateral facets of the actual K (triangles and
   trapezoids merged correctly, no fake subdivision into triangles that would
   add extra hinges, no omitted facet).
3. Metric: face maps must be isometries for the Euclidean metric of R^3 into
   Euclidean R^2 (Lean pitfall: `ℝ × ℝ` / `Fin n → ℝ` carry the sup metric).
4. Non-vacuous interiors: "interior" of each face image must be the planar
   (2D) interior of a full-dimensional convex polygon, not an R^3 interior of a
   planar set (empty) or an interior computed in a degenerate domain.
5. Material identifications: the quotient must glue consecutive facets
   F_i, F_{i+1} along the whole common hinge for every non-cut hinge (N-1 of
   them), and nothing across the cut hinge e. Points of a rim vertex should
   end up as one class unless the vertex is an endpoint of e (then two
   classes). A surjection onto K's lateral material is not enough: extra cuts
   would still be surjective.
6. Development: a single map from the quotient, affine-isometric on each face,
   well defined (hence continuous) on classes. With nondegenerate faces,
   disjoint interiors force consecutive faces onto opposite sides of each
   hinge, so the development is then the genuine edge-unfolding up to a
   global isometry; I will check that this reasoning is actually available
   (i.e. that gluing is along full segments, not just points).
7. Safety: for i != j, image(int F_i) ∩ image(int F_j) = ∅, quantified over
   ALL distinct pairs, not just consecutive ones or ones in a window.
8. Quantifier order: exists e, exists U, Full(e,U) and forall d in (0,1/2),
   Trimmed(e,U,d). The public endpoint must not take a cut, development,
   Safe fact, radial certificate, shifted-turn condition, nesting assumption
   or ordinary-band theorem as hypothesis. No sorry/axiom/native_decide/
   implemented_by/unsafe/opaque shortcuts in the dependency cone.
9. Trim: the trimmed band (heights d*h .. (1-d)*h) with the same U. I expect
   this to be a near-corollary of the full result (sub-faces have smaller
   interiors); I will check it is not instead defined in a way that changes
   the face structure.

#### Plausible definitional escape routes to test

- sup-metric isometries; interiors that are always empty; faces allowed to be
  degenerate segments; U allowed to reflect individual faces (harmless only if
  the gluing forces full-hinge agreement).
- quotient that only glues at vertices or at a subset of hinges; quotient
  built from a caller-chosen chain rather than K's actual facet cycle.
- the "original" facets computed from a presentation that the endpoint
  constructs, but where the presentation is not tied to conv(finite set)
  (e.g. only proved for strictly convex, no parallel edges, or no collinear
  input points).
- h hidden normalization (h = 1 only) not actually transported back to the
  stated h.
- Safe only asserted for faces of one type, or only for pairs within some
  window, or only at a generic trim level.

#### Plausible mathematical counterexample families (to keep in view)

- Strongly non-nested rims: small A far outside B's projection (cone-like
  skew band), small h (nearly flat, projections fold over each other).
- Mixed curvature: rims whose unfolded turning angles change sign many times.
- Holonomy/defect cases: total curvature on one rim above, below, equal to
  2*pi (rotation vs pure translation of the seam copies).
- Many triangles fanning from one high-valence rim vertex (large rim vertex
  angle sum), triangles only (A and B with no parallel edges).
- Near-degenerate thin facets; parallel edges giving trapezoids.

Context note: to my knowledge (not re-checked here), edge-unfolding of
general non-nested bands is listed as open in the literature (Aloupis et al.
proved the nested case). A complete proof would therefore be a significant
claim, which raises the bar for the formal-correspondence check.

### A.2 First-pass statement audit (saved 21:32 UTC, before any manuscript or receipt)


Saved 2026-09-25T21:32Z. Read so far: NON-GPT-REVIEW.md (commit-13) and Lean
sources at commit-11 only (git archive into scratch). NOT yet opened: any
THEOREM-NOTE, manuscripts, *RETURN*, *AUDIT*, *ACCEPTANCE*, build-receipt.txt,
mutation-rejection.txt, WORKLOG.md, README.md, results/.

#### Public statements (GeneralTwoRimEndpoint.lean)

- `exists_sameCutSameMaps A B hh : Nonempty (SameCutSameMapsResult A B hh)`
  for all `ReducedConvexPolygon`s A, B and `hh : 0 < h`. Only hypotheses: A, B,
  hh. Proof = trichotomy on `intrinsicDelta` (neg / zero / pos branches).
- `general_rawCutSurfaceConclusion : RawCutSurfaceConclusion A B hh`
  = `∃ e, Nonempty (CutSurfaceDevelopment A B hh Plane e)`.
- `general_setSameCutSameMaps` / `general_setCutSurfaceConclusion`: inputs are
  sets KA KB with `∃ S : Finset, convexHull S = K` and nonempty interior, h>0.
  Conclusion carries `PA.polygon.body = KA`, `PB.polygon.body = KB`,
  `physicalBodyOfSets KA KB h = physicalPrismatoid PA.polygon PB.polygon h`,
  and the development for the canonical presentations.
- No cut, development, Safe, radial certificate, T-mixedness, nesting, or
  external band theorem is a hypothesis of any of these four.

#### Definitions expanded, against my step-1 obligations

1 Inputs: `canonicalPresentation` = Classical.choice of
  `exists_reduced_polygon_of_polygon_set` (any finite hull with nonempty
  interior). `RawPresentation.body_eq : polygon.body = K`. Covers collinear /
  redundant generators (minimal generators derived). OK.
2 Faces: `Side A B` = unit rays of all edge normals of A and B (deduplicated
  Finset image). Row u: `sideRow h u p = h_B(u) - <u,flat p> + (h_A(u)-h_B(u)) z/h`.
  `halfspaces_body`: H-rep body = `physicalPrismatoid` (independent V-hull).
  `materialFace u = body ∩ {sideRow u = 0}` (whole supporting-plane face, so
  trapezoids are single faces, not triangulated). `certificate u` samples =
  all tight raw vertices; `samples_strict` proves every other row (caps and
  other sides) is strict at some sample ⇒ `center_interior` ⇒ each face has
  nonempty 2D relative interior. `constructed_lateral_coverage`: union of faces
  = `lateralBoundary` = body points on some non-cap row. OK.
3 Metric: `PhysicalAmbient = EuclideanSpace ℝ (Fin 3)`, `Plane =
  EuclideanSpace ℝ (Fin 2)`; `FaceSpace = ker sideLinear` ⊂ PhysicalAmbient
  with inherited norm; `chart x = origin + x`, `norm_map := rfl`;
  `faceSpace_finrank = 2`. `U i : FaceSpace →ᵃⁱ[ℝ] Plane`. Old max-norm
  `Ambient = Plane × ℝ` only used for membership algebra via linear `pack`.
  OK (explicitly guarded in EuclideanPrismatoidCoordinates).
4 Interiors: `Safe F U := ∀ i j, i ≠ j → Disjoint (interior (U i '' F i))
  (interior (U j '' F j))` with interior taken in the 2D Plane; F i has
  nonempty interior in the 2D FaceSpace and U i is an isometry between
  2-dimensional spaces, so image interiors are nonempty: not vacuous. OK.
5 Material identifications (`CutSurfaceQuotient`): tagged points (i, x),
  i in the opened order `order A B e : Fin (N-1+1) ≃ Side`; `CutRelated x y`
  iff same ambient point AND that point lies in every face whose opened index
  is between x.1 and y.1. Equivalence proved. My analysis: because the faces
  containing any lateral point form one contiguous cyclic run that is never
  the whole cycle, this is exactly the cut annulus: adjacent faces are glued on
  their whole common edge (`adjacent_cutRelated`), a high-valence rim vertex
  is one class unless its run crosses the seam (then two classes), the seam
  segment has two copies (`seam_copies_ne`, proven with an explicit missing
  side). No extra cut is possible because the relation is fixed, not
  caller-supplied, and every adjacent shared point is related.
  Adjacency is independently characterized: `MaterialAdjacent` (distinct
  faces sharing a strictly-interior-height point) ⇔ cyclic successor
  (`original_cycle_adjacency`), and every `OriginalEdge` is cyclic
  (`everyOriginalEdge_cyclic`). So the opened chain is K's real facet cycle.
6 Development: `CutSurfaceDevelopment` fields pin `developedMap` and
  `materialMap` on every face inclusion; `DevelopmentOn` = adjacent faces agree
  on every common ambient point + adjacent image interiors disjoint. A map on
  the quotient with `developed_face` exists only if U respects CutRelated. With
  2D faces and disjoint interiors, consecutive faces must lie on opposite sides
  of their common hinge, so U is the genuine edge-unfolding up to one global
  isometry (my argument; not a Lean theorem). OK.
7 Safe quantifies over ALL distinct opened indices. OK.
8 Quantifiers: `SameCutSameMapsResult` = e, development (with U), and
  `∀ d, 0<d → d<1/2 → DevelopmentOn charts (heightTrim dom height d) U ∧
  Safe (heightTrim dom height d) U`, with the same `development.U`. Matches
  `∃e ∃U, Full ∧ ∀d Trimmed`. `height` = normalized z/h, `heightTrim F z d =
  F ∩ {d ≤ z ≤ 1-d}`. OK.
9 Trim: as expected, the trimmed clause is mathematically a corollary of the
  full clause (subsets have smaller interiors; gluing restricts). It is not a
  different face structure. Not a defect; it just means the "stronger stored
  result" adds little beyond the full result.

Soundness scan: no `sorry`, `admit`, `axiom`, `native_decide`,
`implemented_by`, `extern`, `unsafe`, `opaque`, `run_cmd`, `#eval`, custom
elab/macro, or `debug.*` option in any of the 82 files. `maxHeartbeats 0`
once (timeout only). lakefile has no leanOptions; Mathlib pinned
5ed2965256430c3649e86755f9576b54eca72435 (tag v4.34.0); toolchain v4.34.0.

#### Preliminary judgement (formal side)

Qualified-to-exact match: the public types express the Section 2 claim for all
finite-hull inputs with nonempty interiors and all h>0, with a faithful
Euclidean model, genuine maximal facets, the correct one-cut quotient, and
all-pairs planar interior disjointness. Qualifications so far:
- "continuous development" is continuity on the explicit quotient topology;
  no separate theorem identifies that quotient with a disk / the geometric
  slit surface (not needed for the stated claim, as the brief notes);
- orientation of U is not fixed per face, but is forced by the hypotheses
  (see 6), so this is not an escape route;
- the trimmed clause is a near-corollary, not independent strength.
These are not defects. Compilation and axioms still to be reproduced.

#### Mathematical side, not yet examined

The case split uses `intrinsicQ i = angle(mid_i, hinge_i) - angle(mid_{i-1},
hinge_i)` (signed turn at hinge i between middle-section edge directions),
`intrinsicDelta = Σ q`, `Σ|q| < 2π` proved. Zero branch: Δ=0 ⇒ T-mixed
(some q ≤ Δ ≤ some q) by averaging; reuses T-mixed construction. Positive and
negative branches not yet read.

### A.3 Second-pass mathematics (saved 21:47 UTC, before any receipt)


Saved 2026-09-25T21:47Z. Read: THEOREM-NOTE.md @commit-12 (Sections 1-4; I did
not rely on its evidence claims); FOLDED-TURN-RF.md §0-4, EXTREMAL-SEAM.md
§0-8, POLAR-WINDOW.md §1-6, SYSTEM-TO-CODEX-FORGE.md §0-8 @commit-11; Lean:
MixedTurnSafeCut (declaration list + opening), FoldedTurnProjection.Chain,
PhysicalMixedTurnSource (intrinsicQ/Delta/TMixed), branch packaging files
SelectedNegativeDirectDevelopment, SelectedPositiveFullDevelopment,
ArbitraryCutFullDevelopment, ArbitraryCutDirectMap.

Still NOT opened: any CODEX-FORGE-RETURN / *AUDIT* / *ACCEPTANCE* /
SYSTEM-INTEGRATION-RECEIPT / results/ / build-receipt / WORKLOG / README.

#### B. Folded-turn lemma (FOLDED-TURN-RF §1) — verified line by line
- Indexing: last interval [s_{n-1}, 2π] has gap τ_0 and change q_0; θ_n = Δ.
- Θ is κ-Lipschitz (κ = max |q_i|/τ_i < 1), g = Θ - Δ/2, f = |g|;
  f(0) = f(2π) = |Δ|/2, so f (not g) descends to the circle; IVT gives α.
- f(s) ≤ κ d(s,α) ≤ d(s,α) ≤ π, strict when d > 0.
- cos(θ_j - Δ/2) = cos f(s_j) ≥ cos(s_j - α), strict off α.
- Σ a_j cos(s_j - α) = 0 by closure; some a_j > 0 sits off α (else the
  positive sum of one unit vector could not vanish). Hence Π > 0. Correct;
  zero weights allowed. `FoldedTurnProjection.Chain` encodes exactly these
  hypotheses (gap_pos, |turn| < gap, closure_cos/sin, weights ≥ 0, Σ > 0,
  closing interval included via n+2 knots).

#### B'. Application (§2-3)
- Upper-rim closure Σ a_j u_j = 0 with u_j = Rot(-s_j) u_0 gives (1).
- E_i = Σ_j a_{i+j} Rot(θ_j) v: developed upper edges are parallel to the
  developed middle edge of the same face; headings accumulate the intrinsic
  q exactly (source bridge §5 gluing rotation R(q_{i+1})). OK.
- E_i = H(Y_0) - Y_0 = (Q-I)(Y_0-O) uses the full affine H (t kept). OK.
- Q - I = 2 sin(Δ/2) Rot(Δ/2) J; dot(v, Jx) = det(x, v); so
  Π_i = 2 sin(Δ/2) det(Y_0-O, v). Verified.
- Δ<0 ⇒ det(U_i-O, v_i) < 0; with det(v_i,G_i) < 0 (orientation of the
  canonical charts: det(e,d) = -b(1-2d)s < 0) ⇒ det(L_i-O, v_i) < 0. OK.
- Conjugacy: in one baseline frame φ_{k+n} = H∘φ_k, so the circuit started
  at any face is the same H with the same pole O. Frame changes are one
  rigid motion; the determinant statements are invariant. Not free
  repositioning. OK.
- Δ>0: lower-rim closure gives det(L_i-O,v_i) > 0, then det(U_i-O,v_i) > 0.
  Transport (S reflection + rim swap): b'=Sa, a'=Sb, e'=λSe, d'=-Sd gives
  det(e',d') = λ det(e,d) (orientation kept), radial dets flip, Δ flips.
  Verified. (Lean has a separate SelectedPositive* development.)

#### C. Extremal seam + winding (EXTREMAL-SEAM §2-3, POLAR-WINDOW §3,5)
- Max-radius upper vertex: a·f ≥ |f|²/2, a·e ≤ -|e|²/2; with R:
  f_x>0,f_y<0,e_x<0,e_y<0 ⇒ det(f,e)<0; coherent orientation gives
  det(f,g)<0, det(e,g)<0 (incoming panel via d_k = d_{k-1}+(λ-1)e_{k-1});
  Cramer g = A(-f)+Be, A,B>0 ⇒ a·g<0 ⇒ squared radius along hinge strictly
  decreasing; identity (t2-t1)[2a·g-(2-t1-t2)|g|²] checked. Virtual wrapped
  neighbours use Q^{±1} copies (radius invariant). OK.
- Winding: η = θ - φ ∈ (-π,0) by R; at a hinge both η's in (-π,0) so
  their difference is in (-π,π), ≡ q_i and |q_i| < τ_i < π ⇒ equal; after
  the circuit η returns ⇒ lifted polar sweep = Δ exactly. OK.
- Ray argument: seam in an open half-plane ⇒ α monotone, width ω<π; each
  height has the section's lifted angles = [α(t)-L, α(t)], L=-Δ∈(0,2π);
  eligible height sets I_j are closed intervals; at most two (ω+L<3π);
  within one lift radius r_i(t) = [det(b_i,e_i)+t det(d_i,e_i)]/det(v,e_i)
  has strictly negative slope on every eligible panel; pieces agree on
  retained hinges ⇒ strictly decreasing through I_j; two components:
  facing endpoints are root seam / Q-copy of seam at those heights (equality
  in the eligibility constraint), equal radii by Q-invariance, seam strictly
  inward ⇒ every radius on the lower component > every radius on the upper.
  Same height: unique by strict advance and L<2π. ⇒ injective opened strip
  modulo intended hinge identifications. OK. Fixed-sign slopes are NOT used
  alone for cross-component separation; the seam comparison does that.

#### D. Sign cases and degeneration
- Triangles: trims δ∈(0,1/2) have positive retained lengths
  b(δ)=(1-δ)b+δa, a(δ)=δb+(1-δ)a (source bridge §2); R inherited from RF
  by convexity. Eventual maximizer k by lexicographic coefficient triple,
  (U_k-δG_k)·G_k<0 for small δ ⇒ U_k·G_k ≤ 0 ⇒ full hinge strictly inward
  (2-t1-t2>0, G_k≠0) ⇒ same k and same full maps safe at EVERY trim ⇒
  full faces safe (interior witnesses have strictly intermediate height and
  survive a small trim). OK; no positive-run assumption at d=0.
- Δ=0: P=N, P+N=Σ|q|<2π ⇒ P=N<π at every cut; T-mixed selection;
  headings stay in an interval of width <π ⇒ common forward direction ⇒
  X-monotone strip with same-sign trace slopes ⇒ injective. No pole used;
  translation holonomy harmless. OK. (MixedTurnSafeCut:
  exists_forward_of_variations, small_variation_injective, mixed_family_safe_cut.)
- |q_i| < τ_i: Gram identity (1-x²)(1-y²)-(c-xy)² = (w_z det(u,u'))² > 0
  ⇒ cos q > cos τ. Verified; Lean: abs_intrinsicQ_lt_middleExteriorTurn.

#### Preliminary mathematical judgement
I found no false step in the chain folded-turn ⇒ RF (both signs) ⇒
max-radius inward seam ⇒ trimmed injectivity ⇒ full-face safety, nor in the
Δ=0 branch. Exposition gaps (not errors): positive-Δ transport is sketched
in prose; the "established orientation" det(v,G)<0 is imported from the
source-bridge charts; the winding lemma is cited from POLAR-WINDOW rather
than restated in EXTREMAL-SEAM. The paper argument is therefore acceptable
at the stated static/quotient scope, conditional on the formal build that
closes these steps mechanically.

Context correction: my step-1 remark that non-nested band unfolding is
"listed as open" is unverified recollection. THEOREM-NOTE §4 says the
closed-band statement was already attributed to Aloupis. I make no
literature or priority judgement (brief forbids it).

## Appendix B. Changes after seeing receipts

Neither verdict changed after I opened `CODEX-FORGE-RETURN.md` and `results/codex-2026-09-25/`.

- **Added: E1 (§5).** Some stored hashes did not match the reviewed bytes. I traced this to mixed line endings in the implementer's working tree, not to different content.
- **Added: E2 and E3.** The final pre-push check replayed cached project modules, and the theorem note relied on the implementer's receipts. My fresh compile (§3) fills that gap for the endpoint closure.
- **Confirmed.** The historical `SelectedNegativeFullDevelopment` module, whose fresh rebuild the implementer stopped, is outside the public endpoint's import closure. My own import-graph computation places it outside the 52-module closure of `GeneralTwoRimEndpoint`. So the stopped attempt leaves no missing dependency in the active proof. §3.6 reports my separate attempt to build it.
- **Withdrawn.** My step-1 context remark that non-nested band unfolding is "listed as open" was unverified recollection. THEOREM-NOTE §4 and the provenance file say the closed-band statement appears in Aloupis's thesis. I make no literature or priority judgement, as the brief requires.
- **Wording.** My first-pass label "qualified-to-exact match" became "match, with three stated qualifications". The substance is unchanged.

## Appendix C. How to reproduce this review's checks

All of this was scratch work in the session scratchpad
(`<review-scratch>\`).
None of it was written into the repository.

1. `git archive commit-11 "<L>" | tar -x` into scratch. Check each file against `git ls-tree commit-11` with `git hash-object`.
2. Copy `<lean-worktree>\<L>\.lake\packages` read-only with `robocopy /E /COPY:DAT /DCOPY:T` into `<proj>\.lake\packages`. Check every package with `git rev-parse HEAD` against `lake-manifest.json`.
3. `LEAN_PATH` = the nine `<proj>\.lake\packages\<p>\.lake\build\lib\lean` directories plus an empty `out\`.
4. For each module M in import order, run: `lean.exe -R <proj> -o out\M.olean -i out\M.ilean <proj>\M.lean`. The driver is `drive.py`; it logs to `logs\M.log`.
5. Compile `OpusReviewChecks.lean` (below) with the same `LEAN_PATH`.

On a machine where Lake can use short paths, `lake build GeneralTwoRimEndpointSanity GeneralTwoRimFrustumSanity GeneralTwoRimReversedFrustumSanity` in a clean clone at commit-11 should be equivalent. I did not run that form (T1).

### C.1 `OpusReviewChecks.lean` (attempt 2, exit 0)

```lean
import GeneralTwoRimEndpoint

set_option autoImplicit false

/-!
Independent reviewer checks (Opus 5.5, 2026-09-25). Scratch file only; it is
not part of the reviewed project and changes no project source.

1. Re-print the public statements and their axioms from a fresh build.
2. `Safe` is not vacuous: every developed face image has nonempty interior.
3. No extra cut: adjacent opened faces are equal in the explicit quotient at
   every common material point.
4. The trimmed clause follows from the full clause (checks my reading that it
   adds no independent strength).
5. An elementary restatement of the set-level endpoint with the quantifiers
   and the Safe/gluing predicates written out explicitly.
-/

open Set
open MergedNormalPrismatoid PolygonSupportCompleteness CyclicCutOrders
open OriginalFacetCertificates FiniteWitnessClosure BandGeometryAssembly
open CutSurfaceQuotient PhysicalMixedTurnSource GeneralTwoRimUnfolding
open TrimmedFacetWitnesses PolygonSetReconstruction EuclideanPrismatoidCoordinates

namespace OpusReviewChecks
noncomputable section

section Raw
variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

/-- (2) Non-vacuity of `Safe`: each developed face image has nonempty planar
interior. -/
theorem face_image_interior_nonempty (e : Fin (sideCount A B))
    (D : CutSurfaceDevelopment A B hh PhysicalMixedTurnSource.Plane e)
    (i : Fin (sideCount A B - 1 + 1)) :
    (interior (D.U i '' (certificate A B hh (order A B e i)).domain)).Nonempty := by
  have hd : Module.finrank ℝ (FaceSpace A B h (order A B e i)) =
      Module.finrank ℝ PhysicalMixedTurnSource.Plane := by
    rw [faceSpace_finrank]
    simp [PhysicalMixedTurnSource.Plane]
  rw [← embedding_image_interior (E := fun j => FaceSpace A B h (order A B e j))
    (i := i) hd (D.U i) (certificate A B hh (order A B e i)).domain]
  exact ⟨_, (certificate A B hh (order A B e i)).center,
    (certificate A B hh (order A B e i)).center_interior, rfl⟩

/-- (3) Adjacent opened faces are glued at every common material point. -/
theorem adjacent_faces_glued (e : Fin (sideCount A B)) (j : Fin (sideCount A B - 1))
    (x : FacePiece A B hh e j.castSucc) (y : FacePiece A B hh e j.succ)
    (hxy : ambient A B hh e ⟨j.castSucc, x⟩ = ambient A B hh e ⟨j.succ, y⟩) :
    faceInclusion A B hh e j.castSucc x = faceInclusion A B hh e j.succ y := by
  unfold faceInclusion
  exact @Quotient.sound _ (cutSetoid A B hh e) _ _
    (adjacent_cutRelated A B hh e j x y hxy)

/-- (4) Full safety implies safety of every height trim with the same maps. -/
theorem trimmed_safe_of_full (e : Fin (sideCount A B))
    (D : CutSurfaceDevelopment A B hh PhysicalMixedTurnSource.Plane e) (d : ℝ) :
    Safe (fun i => heightTrim (certificate A B hh (order A B e i)).domain
        (certificate A B hh (order A B e i)).height d) (fun i => D.U i) := by
  intro i j hij
  have hsub : ∀ k : Fin (sideCount A B - 1 + 1),
      heightTrim (certificate A B hh (order A B e k)).domain
        (certificate A B hh (order A B e k)).height d ⊆
        (certificate A B hh (order A B e k)).domain :=
    fun _ => inter_subset_left
  exact (D.safe i j hij).mono (interior_mono (image_mono (hsub i)))
    (interior_mono (image_mono (hsub j)))

end Raw

/-- (5) Elementary restatement of the set-level endpoint. -/
theorem restated_set_endpoint (KA KB : Set PhysicalMixedTurnSource.Plane)
    (hfinA : ∃ S : Finset PhysicalMixedTurnSource.Plane, convexHull ℝ (↑S : Set _) = KA)
    (hfinB : ∃ S : Finset PhysicalMixedTurnSource.Plane, convexHull ℝ (↑S : Set _) = KB)
    (hintA : (interior KA).Nonempty) (hintB : (interior KB).Nonempty)
    {h : ℝ} (hh : 0 < h) :
    ∃ (PA : RawPresentation KA) (PB : RawPresentation KB)
      (e : Fin (sideCount PA.polygon PB.polygon))
      (U : (i : Fin (sideCount PA.polygon PB.polygon - 1 + 1)) →
        FaceSpace PA.polygon PB.polygon h (order PA.polygon PB.polygon e i) →ᵃⁱ[ℝ]
          PhysicalMixedTurnSource.Plane),
      PA.polygon.body = KA ∧ PB.polygon.body = KB ∧
      physicalBodyOfSets KA KB h = physicalPrismatoid PA.polygon PB.polygon h ∧
      (⋃ i, (certificate PA.polygon PB.polygon hh (order PA.polygon PB.polygon e i)).chart ''
          (certificate PA.polygon PB.polygon hh (order PA.polygon PB.polygon e i)).domain) =
        PolyhedralInputBridge.lateralBoundary (halfspaces PA.polygon PB.polygon h) ∧
      (∀ j : Fin (sideCount PA.polygon PB.polygon - 1),
        ∀ x ∈ (certificate PA.polygon PB.polygon hh
            (order PA.polygon PB.polygon e j.castSucc)).domain,
        ∀ y ∈ (certificate PA.polygon PB.polygon hh
            (order PA.polygon PB.polygon e j.succ)).domain,
          (certificate PA.polygon PB.polygon hh
              (order PA.polygon PB.polygon e j.castSucc)).chart x =
            (certificate PA.polygon PB.polygon hh
              (order PA.polygon PB.polygon e j.succ)).chart y →
          U j.castSucc x = U j.succ y) ∧
      (∀ i j, i ≠ j →
        Disjoint
          (interior (U i '' (certificate PA.polygon PB.polygon hh
            (order PA.polygon PB.polygon e i)).domain))
          (interior (U j '' (certificate PA.polygon PB.polygon hh
            (order PA.polygon PB.polygon e j)).domain))) ∧
      (∀ i, (interior (U i '' (certificate PA.polygon PB.polygon hh
            (order PA.polygon PB.polygon e i)).domain)).Nonempty) ∧
      (∀ d : ℝ, 0 < d → d < (1 : ℝ) / 2 →
        Safe (fun i => heightTrim
            (certificate PA.polygon PB.polygon hh (order PA.polygon PB.polygon e i)).domain
            (certificate PA.polygon PB.polygon hh (order PA.polygon PB.polygon e i)).height d)
          (fun i => U i)) := by
  obtain ⟨hA, hB, hbody, ⟨D⟩⟩ :=
    general_setSameCutSameMaps KA KB hfinA hfinB hintA hintB hh
  refine ⟨_, _, D.e, D.development.U, hA, hB, hbody, D.development.lateral_coverage,
    D.development.developmentOn.1, D.development.safe, ?_, ?_⟩
  · intro i
    exact face_image_interior_nonempty _ _ hh D.e D.development i
  · intro d hd0 hd1
    exact (D.every_positive_trim d hd0 hd1).2

end
end OpusReviewChecks

#check @OpusReviewChecks.restated_set_endpoint
#print axioms OpusReviewChecks.face_image_interior_nonempty
#print axioms OpusReviewChecks.adjacent_faces_glued
#print axioms OpusReviewChecks.trimmed_safe_of_full
#print axioms OpusReviewChecks.restated_set_endpoint
#print axioms GeneralTwoRimUnfolding.exists_sameCutSameMaps
#print axioms GeneralTwoRimUnfolding.general_rawCutSurfaceConclusion
#print axioms GeneralTwoRimUnfolding.general_setSameCutSameMaps
#print axioms GeneralTwoRimUnfolding.general_setCutSurfaceConclusion
#print FiniteWitnessClosure.Safe
#print BandGeometryAssembly.DevelopmentOn
#print CutSurfaceQuotient.CutRelated
#print CutSurfaceQuotient.CutSurfaceDevelopment
#print GeneralTwoRimUnfolding.SameCutSameMapsResult
#print PhysicalMixedTurnSource.SetCutSurfaceConclusion
#print PolyhedralInputBridge.lateralBoundary
#print EuclideanPrismatoidCoordinates.PhysicalAmbient
#print OriginalFacetCertificates.FaceSpace
```
