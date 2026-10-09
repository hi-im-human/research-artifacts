---
title: Independent finished-source audit of the physical T-mixed theorem
author: Codex Forge
date: 2026-09-22
status: PASS at the explicit physical T-mixed cut-surface scope
implementation: commit-05
acceptance-checkpoint: commit-06
dg-publish: false
---

**Verdict: PASS for the public raw endpoint and the canonical-presentation set endpoint.** I found no unsupported bridge or mathematical mismatch with the accepted physical T-mixed proposition. This is an audit of the delivered Lean source, including the construction of its physical inputs and the meaning of its conclusion. It does not extend the earlier A–C mechanism or the theorem's geometric scope.

I refreshed `origin/main` and reviewed main at the acceptance checkpoint above. The Lean project is unchanged between the implementation and acceptance commits. The production sources and pins were left unchanged.

**The exact accepted statement.** Let KA and KB be planar convex hulls of finite sets, both with nonempty interiors, and let h > 0. The physical body is exactly the Euclidean convex hull of KB at height 0 and KA at height h. On the internally selected reduced presentations, define

`qᵢ = angle(middleDirectionᵢ, upwardHingeᵢ) − angle(middleDirectionᵢ₋₁, upwardHingeᵢ)`,
`Δ = Σᵢ qᵢ`, and `Tᵢ = qᵢ − Δ`.

Assume `(∃ i, Tᵢ ≤ 0) ∧ (∃ j, 0 ≤ Tⱼ)`. There is an original lateral hinge and a continuous planar development of the explicit surface obtained by gluing the original lateral faces in the chain opened at that hinge. Every face map is an affine isometry for the physical Euclidean metric, and the interiors of every two distinct developed faces are disjoint. The construction supplies one cut and one map family valid on the full faces and all positive inward trims.

This statement includes triangular lateral facets and zero cases of the shifted predicate. Both entire rim polygons must still have positive area. It concerns this two-rim convex-hull body; it does not itself supply a reduction from an arbitrary polyhedron/slab to that body.

| Audited obligation | Verdict | Reason |
|---|---|---|
| Original body and material identity | PASS | Independently defined Euclidean hull; exact body, source-facet and coverage equalities |
| Exact shifted condition | PASS | Tᵢ = qᵢ − Σq; weak inequalities; no replacement by mixed unshifted signs |
| Source certificates and turn budget | PASS | Derived from input polygons and physical geometry |
| DevelopedFamily and exact face images | PASS | Every field constructed; whole-set equalities on actual trimmed material domains |
| One fixed cut and full affine maps | PASS | Depth-free definitions, with one common translation relating every trim layout |
| Full safety and original hinge gluing | PASS | Same maps used in overlap persistence and affine extension |
| Triangles and cut-index transport | PASS | Collapsed original run allowed; positive trimmed runs; actual dependent source transport |
| Cut-surface endpoint | PASS at its explicit quotient scope | Material coverage, continuous development, per-face isometry and full pairwise interior safety |
| External ordinary-band premise | ABSENT | Neither public endpoint asks for one; the old named proposition is proved internally |

**1. The material is the original physical body.** The raw polygon structure supplies vertices, local support inequalities and reducedness, rather than a development or a safety assumption. Set reconstruction supplies the reduced presentations internally.

`physicalBodyOfSets` independently defines the Euclidean three-dimensional convex hull. `physicalBodyOfSets_eq` identifies it with the raw physical prismatoid. `halfspaces_body` identifies that same hull with the constructed halfspace body. The old product-coordinate space is used for affine transport; it is not silently treated as the physical Euclidean metric.

`certificate` constructs the source plane, its Euclidean chart and its original tight samples. `material_facet` and `mem_materialFace` identify its entire image with the tight supporting face of the original body. `faceSpace_finrank` and `constructed_face_interior` give dimension two and nonempty relative interior. The bijection to all non-cap rows and the coverage equality prevent omission of lateral material. These are full supporting faces, not invented panels replacing the source.

The set endpoint also explicitly returns both original rim-body equalities and the physical-body equality. See [the set endpoint](../formal/PhysicalMixedTurnBridge.lean#L64) and [the original facet table](../formal/OriginalFacetCertificates.lean#L409).

**2. The turns, signs and budget come from that material.** The middle polygon is constructed from the actual hinge midpoints and common support cycle. The outgoing and incoming directions and upward hinge are physical vectors. `intrinsicQ_eq_physicalBeta_sub_pi` identifies q with the retained lower material-sector excess β − π; `physicalBeta_trim_invariant` proves independence of positive trim depth. The physical rim and orientation are retained throughout cut comparisons.

The new complete-turn proof derives the reduced convex polygon's 2π turn from a fan triangulation. The strict local angle bound then gives `Σ |qᵢ| < 2π`. No total-turn budget, local angle certificate or ordinary-band theorem is a source assumption. I checked the complete-turn argument and the physical strictness argument, without reopening the accepted A–C mechanism.

`IntrinsicTMixed` uses the exact shifted condition stated above. The nonphysical scalar guard q = (1, 1, −1/4) correctly rejects the inference from mixed q signs to shifted mixedness. The public raw type contains only the reduced source polygons, positive height and this shifted condition.

At set level, `SetIntrinsicTMixed` is evaluated on exactly the internally chosen `canonicalPresentation` values used by the conclusion. The delivery does not prove a separate invariance theorem across arbitrary presentations. This is an explicit scope boundary, not a hidden extra premise. See [the turn definitions](../formal/PhysicalMixedTurnSource.lean#L912).

**3. Both directions and positions are retained.** `intrinsicFaceChart` is an affine Euclidean isometry on the actual source plane, anchored at the entry-hinge midpoint. Its frame is derived from the physical middle-edge direction and the nonzero transverse component of the upward hinge.

The direct map has the full form

`U(k,j)(x) = R(heading(k,j)) · intrinsicFaceChart(source(k,j))(x) + directTranslation(k,j)`.

The translation is accumulated from the rotated physical middle-section steps. It is not inferred from rotational holonomy or dropped when the total turn vanishes. `directTransition_entryAt` matches points along the actual common hinge, rather than merely aligning hinge directions.

All fields of `physicalDevelopedFamily` are filled from this source: q, positions B, lower edges e, hinge vectors d, ratios, headings, lengths, positivity, representation, coherent orientation, lower-step and hinge-step recurrences, internal heading steps and the derived variation bound.

`heightTrim_eq_retainedFaceHull` proves equality of the actual trimmed certificate domain with the four-corner retained hull. `developedMap_heightTrim_image` proves equality of its whole developed image with the mechanism's face. These are two-sided set equalities, not checks of a few vertices or containment in a surrogate panel.

Most importantly, `familyOffset_eq_directTranslation` and `directDevelopedMap_eq_developedMap_add_root` relate the direct maps to the trim layout by **one vector common to every face and source point**. That vector may depend on root and trim depth. Independent repositioning of individual faces is not used to transfer safety. See [the direct map](../formal/PhysicalMixedTurnDevelopment.lean#L719) and [the family constructor and exact image theorem](../formal/PhysicalMixedTurnDevelopment.lean#L855).

**4. The quantifiers keep the cut and maps fixed.** `fixedCutIndex` selects one index using the derived scalar mixed-budget theorem. It has no trim-depth parameter. Its two retained budgets are used at this same index for every positive trim.

The source's entry-hinge convention is transported to the existing exit-edge cut convention by e = k − 1, with the finite-cardinality equivalence made explicit. `order_eq_cycle_orderSource` identifies the actual face order. The dependent face transport preserves the physical chart, height and material domain; the common-translation identity survives it.

`physicalFaceMap` is the transported direct map itself. `physicalFaceMap_every_positive_trim` uses that same family at every 0 < δ < 1/2. `physical_fixedCut_full_safe` converts any proposed full-domain strict overlap to original face-interior witnesses and retains them in a small trim with the maps unchanged. Source dimension and nonconstant height are established, so a planar-interior witness is not lost at a rim.

Full hinge gluing follows by affine extension from two distinct retained hinge points. The quarter-trim proves gluing; it does not define a replacement family. `physicalFixedCutSurfaceDevelopment_U` is proved by `rfl`, confirming that the final package contains literally `physicalFaceMap`. See [the fixed-map and full-safety construction](../formal/PhysicalMixedTurnState.lean#L63).

The main raw/set path does not invoke external ordinary-band recovery. `physical_external_general_band` proves the old named proposition from this construction. Its name does not make it an assumption.

**5. Triangular original facets are preserved.** An original upper or lower rim run may be zero; their sum is strictly positive. For every positive inward trim, the convex combinations giving both retained runs are strictly positive. The proof therefore permits a triangular full facet while using a quadrilateral retained domain.

The triangle/square sanity source identifies a particular square-only normal and its actual source-facet index, proves that facet's upper run vanishes, and proves positivity of its retained runs. Its specialized image theorem names that same facet through the dependent transport. The generic theorem does not demand four distinct original corners. This fixture is an exact source/image check, not a claim that every triangle/square placement automatically satisfies T-mixedness. See [the named triangular facet](../formal/PhysicalMixedTurnSourceSanity.lean#L62).

**6. What the cut-surface conclusion means.** The quotient begins with the disjoint union of the complete original face domains in the opened linear order. Two tagged points are `CutRelated` precisely when their physical locations agree and that location belongs to every intervening face in the linear chain.

This has the standard polygonal gluing interpretation. Each adjacent original-hinge identification satisfies the relation. Conversely, a related pair can be joined through representatives of the same material point in every intervening face, giving a finite chain of adjacent identifications. Thus the relation describes gluing along the retained original hinges, with no wraparound identification imposed at the cut. This paragraph is my mathematical interpretation of the inspected relation and its gluing lemmas; I did not add a new Lean equivalence theorem.

The final record supplies a continuous material projection onto the entire original lateral boundary, injective face inclusions, a continuous developed map agreeing with each affine face map, and `Safe` for every pair of distinct developed face interiors. It identifies the actual common material segment of the first and last faces as the original cut hinge.

`seam_copies_ne` proves distinct source-quotient copies for every parameter t in [0,1], including both endpoints. Its proof finds a supporting side that misses the relevant seam point; it does not assume four distinct corners or ignore endpoint identifications. Several triangular facets incident at a rim vertex can still be glued through the intervening chain.

The kernel statement is precise:

- `Safe` means pairwise disjoint planar face interiors. Boundary contact is allowed.
- Distinct seam copies means distinct points of the **source quotient**, not necessarily distinct images in the plane.
- Face inclusion injectivity is not global injectivity of the developed map.
- The concrete gluing quotient is the cut-surface model. The record does not separately provide a homeomorphism to a disk, an independently defined metric completion of a slit surface, or a globally distance-preserving embedding.
- Continuity of the final development is not a continuous collision-free unfolding motion.

These limits match the accepted static proposition. See [the quotient relation](../formal/CutSurfaceQuotient.lean#L59) and [the final record](../formal/CutSurfaceQuotient.lean#L605).

One ancillary wording qualification: `physical_full_face_table` is an existential compatibility theorem using the old recovery route with a proved ordinary-state value. Its type does not identify its returned U with `physicalFaceMap`. The direct-map identity is supplied by the main State/package path above. Reading the compatibility comment as an additional equality theorem would overstate its type; this does not affect either public endpoint.

**7. Independent execution and provenance evidence — Codex Forge's own checks.** I used the pinned Lean 4.34.0 toolchain in the existing compiled checkout at `<lean-worktree>`, whose HEAD is the implementation commit.

- My incremental `lake build PhysicalMixedTurnBridge PhysicalMixedTurnSourceSanity` completed with exit 0: 8,958 jobs, with cached results reused. This is not a claim of a fresh standalone recompilation of every delivered file.
- My separate read-only `lake env lean` inspection probe completed with exit 0. It printed the predicates, quotient and package definitions; checked the explicit public types and fixed-map quantifiers; and printed 24 axiom dependency reports. Their normalized union was exactly `[propext, Classical.choice, Quot.sound]`, with no additional axiom or `sorryAx`.
- I compared all 43 project Lean files plus the lakefile, toolchain and manifest between refreshed main and the compiled checkout. All 46 agree after CRLF/LF normalization; 8 are byte-identical and the other 38 differ only in line endings.
- The compiled checkout's exact SHA-256 values match Letta's saved delivery hashes for all eleven new Lean modules and all three checked build/pin files.
- A source scan of the eleven new modules found no `sorry`, `admit`, custom `axiom`, `unsafe` or `implemented_by` marker. The public axiom reports, rather than that scan alone, support the dependency conclusion.

My receipts are the build log (`build.txt`), the type/axiom report (`types-axioms.txt`), the read-only probe (`inspect.lean`), source comparisons (`source-comparison.json`) and delivery-hash comparisons (`receipt-hash-comparison.json`), in a local audit directory that is not included in this package. Exit-code files are beside the logs.

Letta's earlier direct/module/default-build receipts remain Letta's. In particular, the aborted standalone State check remains aborted, while the recorded explicit target build passed. I did not rerun the historical 69-test suite, prior 23-test suite or floating eight diagnostics. Floating diagnostics are not exact certificates and are not evidence for universality here.

**Disposition.** No production repair or additional wrapper is requested. The accepted endpoint has no external ordinary-band premise and matches the explicit physical T-mixed proposition at the quotient and safety scope above. General sources outside that shifted class remain separate; this audit supplies no uniform-sign extension, all-band theorem, cap result or motion result. Audit complete; stop here.
