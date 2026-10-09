import PhysicalMixedTurnLayout

open Set
open scoped BigOperators Classical NNReal
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CommonSupportMerge OriginalFacetCertificates NormalFanSplice MaximalSupportCells
open CyclicCutOrders EuclideanPrismatoidCoordinates PolyhedralInputBridge
open TrimmedFacetWitnesses BandGeometryAssembly FiniteWitnessClosure SingleCutRecovery
open CutSurfaceQuotient MixedTurnSafeCut PolygonSetReconstruction ConvexPolygonTurning

namespace PhysicalMixedTurnSource
noncomputable section
set_option maxHeartbeats 8000000

section Raw
variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

private noncomputable def trimmedFlatLayout_of_fields {d : ℝ}
    (e : Fin (sideCount A B))
    (T : (i : Fin (sideCount A B-1+1)) →
      FaceSpace A B h (order A B e i) →ᵃⁱ[ℝ] Plane)
    (hs : Safe
      (fun i => heightTrim (certificate A B hh (order A B e i)).domain
        (certificate A B hh (order A B e i)).height d)
      (fun i => T i))
    (hg : ∀ (j : Fin (sideCount A B-1)) (t : ℝ), t ∈ Icc d (1-d) →
      T j.castSucc (AffineMap.lineMap (hinge A B hh e j).aL
        (hinge A B hh e j).bL t) =
      T j.succ (AffineMap.lineMap (hinge A B hh e j).aR
        (hinge A B hh e j).bR t)) :
    NestedBandExternalApplication.TrimmedFlatLayout A B hh Plane d e :=
  NestedBandExternalApplication.TrimmedFlatLayout.mk T hs hg

noncomputable def fixedTrimmedFlatLayout (hmix : IntrinsicTMixed A B hh)
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2) :
    NestedBandExternalApplication.TrimmedFlatLayout A B hh Plane d
      (prev (sourceIndexEquiv A B (fixedCutIndex A B hh hmix))) :=
  trimmedFlatLayout_of_fields A B hh
    (prev (sourceIndexEquiv A B (fixedCutIndex A B hh hmix)))
    (directCutOrderedMap A B hh hmix)
    (directCutOrdered_safe A B hh hmix hd0 hd1)
    (directCutOrderedMap_hinge_glued A B hh hmix hd0 hd1)

noncomputable def fixedTrimmedFlatState (hmix : IntrinsicTMixed A B hh)
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2) :
    NestedBandExternalApplication.TrimmedFlatState A B hh Plane d :=
  NestedBandExternalApplication.TrimmedFlatState.mk
    (prev (sourceIndexEquiv A B (fixedCutIndex A B hh hmix)))
    (fixedTrimmedFlatLayout A B hh hmix hd0 hd1)

/-- The fixed source seam, in the existing exit-edge cut convention. -/
noncomputable abbrev fixedSourceSeam (hmix : IntrinsicTMixed A B hh) :
    Fin (sideCount A B) :=
  prev (sourceIndexEquiv A B (fixedCutIndex A B hh hmix))

/-- The public full face maps are the direct midpoint-anchored source
construction itself, transported through the required `e = k-1` order.  No
trim, safety witness, cofinal choice, or recovered table occurs in this
definition. -/
noncomputable def physicalFaceMap (hmix : IntrinsicTMixed A B hh)
    (i : Fin (sideCount A B-1+1)) :
    FaceSpace A B h (order A B (fixedSourceSeam A B hh hmix) i) →ᵃⁱ[ℝ] Plane :=
  directCutOrderedMap A B hh hmix i

/-- The direct public map is pointwise the old per-trim developed map plus one
common root translation. -/
theorem physicalFaceMap_eq_cutOrderedMap_add_root
    (hmix : IntrinsicTMixed A B hh) (d : ℝ)
    (i : Fin (sideCount A B-1+1))
    (x : FaceSpace A B h (order A B (fixedSourceSeam A B hh hmix) i)) :
    physicalFaceMap A B hh hmix i x = cutOrderedMap A B hh hmix d i x +
      localB A B hh d
        (familySource A B (fixedCutIndex A B hh hmix) 0) :=
  directCutOrderedMap_eq_cutOrderedMap_add_root A B hh hmix d i x

/-- Every positive trim uses exactly the direct source maps. -/
theorem physicalFaceMap_every_positive_trim (hmix : IntrinsicTMixed A B hh)
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ) / 2) :
    DevelopmentOn
        (fun i => (certificate A B hh
          (order A B (fixedSourceSeam A B hh hmix) i)).chart.toAffineMap)
        (fun i => heightTrim
          (certificate A B hh (order A B (fixedSourceSeam A B hh hmix) i)).domain
          (certificate A B hh (order A B (fixedSourceSeam A B hh hmix) i)).height d)
        (fun i => physicalFaceMap A B hh hmix i) ∧
      Safe
        (fun i => heightTrim
          (certificate A B hh (order A B (fixedSourceSeam A B hh hmix) i)).domain
          (certificate A B hh (order A B (fixedSourceSeam A B hh hmix) i)).height d)
        (fun i => physicalFaceMap A B hh hmix i) := by
  let s := fixedTrimmedFlatState A B hh hmix hd0 hd1
  constructor
  · have hdev := NestedBandExternalApplication.developmentOn_of_flat_state hd0 hd1 s
    change DevelopmentOn
        (fun i => (certificate A B hh
          (order A B (fixedSourceSeam A B hh hmix) i)).chart.toAffineMap)
        (fun i => heightTrim
          (certificate A B hh (order A B (fixedSourceSeam A B hh hmix) i)).domain
          (certificate A B hh (order A B (fixedSourceSeam A B hh hmix) i)).height d)
        (fun i => directCutOrderedMap A B hh hmix i) at hdev
    exact hdev
  · simpa only [physicalFaceMap] using directCutOrdered_safe A B hh hmix hd0 hd1

/-- Full original-domain safety for the direct maps.  Any full overlap survives
a sufficiently small trim with the maps unchanged, contradicting the preceding
fixed-cut trim safety theorem. -/
theorem physical_fixedCut_full_safe (hmix : IntrinsicTMixed A B hh) :
    Safe
      (fun i => (certificate A B hh
        (order A B (fixedSourceSeam A B hh hmix) i)).domain)
      (fun i => physicalFaceMap A B hh hmix i) := by
  let F := fun i : Fin (sideCount A B-1+1) =>
    (certificate A B hh (order A B (fixedSourceSeam A B hh hmix) i)).domain
  let z := fun i : Fin (sideCount A B-1+1) =>
    (certificate A B hh (order A B (fixedSourceSeam A B hh hmix) i)).height
  have hdim : ∀ i, Module.finrank ℝ
      (FaceSpace A B h (order A B (fixedSourceSeam A B hh hmix) i)) =
      Module.finrank ℝ Plane := fun i =>
    (faceSpace_finrank A B h _).trans (by simp [Plane])
  by_contra hbad
  have hw := overlap_of_not_safe hdim (physicalFaceMap A B hh hmix) hbad
  change Overlaps F (fun i => physicalFaceMap A B hh hmix i) at hw
  have hLevels : ∀ i, ∃ a b, z i a = 0 ∧ z i b = 1 := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact ⟨(cut A B hh (fixedSourceSeam A B hh hmix)).aL,
        (cut A B hh (fixedSourceSeam A B hh hmix)).bL,
        (cut A B hh (fixedSourceSeam A B hh hmix)).a_height,
        (cut A B hh (fixedSourceSeam A B hh hmix)).b_height⟩
    · exact ⟨(hinge A B hh (fixedSourceSeam A B hh hmix) j).aL,
        (hinge A B hh (fixedSourceSeam A B hh hmix) j).bL,
        (hinge A B hh (fixedSourceSeam A B hh hmix) j).a_height,
        (hinge A B hh (fixedSourceSeam A B hh hmix) j).b_height⟩
  obtain ⟨eps, heps, hcap, hsurvive⟩ := fixed_overlap_survives F z
    (fun i => (certificate A B hh _).height_continuous)
    (fun i x hx => (certificate A B hh _).height_bounds hx)
    hLevels (fun i x => physicalFaceMap A B hh hmix i x) hw
  let d := eps / 2
  have hd0 : 0 < d := by dsimp [d]; linarith
  have hdlt : d < eps := by dsimp [d]; linarith
  have hd1 : d < (1 : ℝ)/2 := by dsimp [d]; linarith
  have hwTrim := hsurvive d hd0 hdlt
  exact not_safe_of_overlap hdim (physicalFaceMap A B hh hmix) hwTrim
    (physicalFaceMap_every_positive_trim A B hh hmix hd0 hd1).2

/-- Full all-uncut gluing for the same direct maps, obtained by affine
extrapolation from their direct quarter-trim layout. -/
theorem physicalFaceMap_full_allUncutGlued (hmix : IntrinsicTMixed A B hh) :
    AllUncutGlued
      (fun i => certificate A B hh
        (order A B (fixedSourceSeam A B hh hmix) i)) 0
      (fun i => physicalFaceMap A B hh hmix i) := by
  let s := fixedTrimmedFlatState A B hh hmix (d := (1/4 : ℝ)) (by norm_num) (by norm_num)
  have hg := NestedBandExternalApplication.allUncutGlued_of_flat_state
    (A := A) (B := B) (hh := hh) (Q := Plane) (d := (1/4 : ℝ))
    (by norm_num) (by norm_num) s
  have hg' : AllUncutGlued
      (fun i => certificate A B hh
        (order A B (fixedSourceSeam A B hh hmix) i)) (1/4 : ℝ)
      (fun i => physicalFaceMap A B hh hmix i) := by
    change AllUncutGlued
      (fun i => certificate A B hh
        (order A B (fixedSourceSeam A B hh hmix) i)) (1/4 : ℝ)
      (fun i => directCutOrderedMap A B hh hmix i) at hg
    exact hg
  exact all_uncut_gluing_extends
    (fun i => certificate A B hh
      (order A B (fixedSourceSeam A B hh hmix) i))
    (fun i => (physicalFaceMap A B hh hmix i).toAffineMap)
    (by norm_num) (by norm_num) hg'

/-- Full original-domain development at exactly the source-selected seam and
at the directly constructed physical maps. -/
theorem physicalFaceMap_full_developmentOn (hmix : IntrinsicTMixed A B hh) :
    DevelopmentOn
      (fun i => (certificate A B hh
        (order A B (fixedSourceSeam A B hh hmix) i)).chart.toAffineMap)
      (fun i => (certificate A B hh
        (order A B (fixedSourceSeam A B hh hmix) i)).domain)
      (fun i => physicalFaceMap A B hh hmix i) := by
  have hMaterial := all_uncut_material_gluing
    (fun i => certificate A B hh
      (order A B (fixedSourceSeam A B hh hmix) i))
    (fun i => faceSpace_finrank A B h _)
    (fun i => physicalFaceMap A B hh hmix i)
    (physicalFaceMap_full_allUncutGlued A B hh hmix)
  constructor
  · intro j
    exact hMaterial j.castSucc j.succ
      (adjacent_not_cutPair (by have hs := three_le_sideCount A B; omega) j)
      (hinge A B hh (fixedSourceSeam A B hh hmix) j)
  · intro j
    exact physical_fixedCut_full_safe A B hh hmix j.castSucc j.succ (by
      intro he
      have hv := congrArg Fin.val he
      change j.val = j.val + 1 at hv
      omega)

/-- Inspectable acceptance package: one source cut, one depth-free map family,
its restriction theorem for every positive trim, and full-domain recovery at
those very maps. -/
theorem physical_trimIndependent_map_family (hmix : IntrinsicTMixed A B hh) :
    ∃ U : (i : Fin (sideCount A B-1+1)) →
        FaceSpace A B h (order A B (fixedSourceSeam A B hh hmix) i) →ᵃⁱ[ℝ] Plane,
      U = physicalFaceMap A B hh hmix ∧
      DevelopmentOn
        (fun i => (certificate A B hh
          (order A B (fixedSourceSeam A B hh hmix) i)).chart.toAffineMap)
        (fun i => (certificate A B hh
          (order A B (fixedSourceSeam A B hh hmix) i)).domain) (fun i => U i) ∧
      Safe
        (fun i => (certificate A B hh
          (order A B (fixedSourceSeam A B hh hmix) i)).domain) (fun i => U i) ∧
      ∀ d, 0 < d → d < (1 : ℝ) / 2 →
        DevelopmentOn
          (fun i => (certificate A B hh
            (order A B (fixedSourceSeam A B hh hmix) i)).chart.toAffineMap)
          (fun i => heightTrim
            (certificate A B hh (order A B (fixedSourceSeam A B hh hmix) i)).domain
            (certificate A B hh (order A B (fixedSourceSeam A B hh hmix) i)).height d)
          (fun i => U i) ∧
        Safe
          (fun i => heightTrim
            (certificate A B hh (order A B (fixedSourceSeam A B hh hmix) i)).domain
            (certificate A B hh (order A B (fixedSourceSeam A B hh hmix) i)).height d)
          (fun i => U i) := by
  refine ⟨physicalFaceMap A B hh hmix, rfl,
    physicalFaceMap_full_developmentOn A B hh hmix,
    physical_fixedCut_full_safe A B hh hmix, ?_⟩
  intro d hd0 hd1
  exact physicalFaceMap_every_positive_trim A B hh hmix hd0 hd1

/-- The final cut-surface package, definitionally built from the same
trim-independent public maps. -/
noncomputable def physicalFixedCutSurfaceDevelopment
    (hmix : IntrinsicTMixed A B hh) :
    CutSurfaceDevelopment A B hh Plane (fixedSourceSeam A B hh hmix) := by
  exact {
    U := physicalFaceMap A B hh hmix
    developmentOn := physicalFaceMap_full_developmentOn A B hh hmix
    safe := physical_fixedCut_full_safe A B hh hmix
    developedMap := developed (physicalFaceMap A B hh hmix)
      (physicalFaceMap_full_developmentOn A B hh hmix)
    developedMap_continuous := developed_continuous (physicalFaceMap A B hh hmix)
      (physicalFaceMap_full_developmentOn A B hh hmix)
    materialMap := materialProjection A B hh (fixedSourceSeam A B hh hmix)
    materialMap_continuous := materialProjection_continuous A B hh _
    materialMap_surjective := materialProjection_surjective A B hh _
    face_injective := faceInclusion_injective A B hh _
    developed_face := developed_faceInclusion (physicalFaceMap A B hh hmix)
      (physicalFaceMap_full_developmentOn A B hh hmix)
    material_face := fun i x => congrArg Subtype.val
      (materialProjection_faceInclusion A B hh _ i x)
    seam_material_eq := by
      intro t ht
      apply Subtype.ext
      exact seam_ambient_eq A B hh _ t ht
    seam_copies_distinct := seam_copies_ne A B hh _
    cut_segment := (cut A B hh (fixedSourceSeam A B hh hmix)).common_material_edge
      (faceSpace_finrank A B h _)
    lateral_coverage := by
      rw [material_union_reindex
        (fun j => (certificate A B hh j).chart '' (certificate A B hh j).domain)
        (order A B (fixedSourceSeam A B hh hmix))]
      exact material_band_eq (halfspaces A B h) (certificate A B hh)
        (rowsEquiv A B) (fun _ => rfl) }

@[simp] theorem physicalFixedCutSurfaceDevelopment_U
    (hmix : IntrinsicTMixed A B hh) (i : Fin (sideCount A B-1+1)) :
    (physicalFixedCutSurfaceDevelopment A B hh hmix).U i =
      physicalFaceMap A B hh hmix i := rfl

/-- A cut-surface development at exactly the source-selected seam. -/
theorem physical_fixedCutSurfaceDevelopment (hmix : IntrinsicTMixed A B hh) :
    Nonempty (CutSurfaceDevelopment A B hh Plane (fixedSourceSeam A B hh hmix)) :=
  ⟨physicalFixedCutSurfaceDevelopment A B hh hmix⟩

end Raw
end
end PhysicalMixedTurnSource
