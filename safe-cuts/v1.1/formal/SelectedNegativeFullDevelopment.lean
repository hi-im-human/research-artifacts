import SelectedRootInteriorWitness
import SelectedNegativeHingeGluing
import GeneralTwoRimUnfolding

open Set
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CommonSupportMerge OriginalFacetCertificates NormalFanSplice MaximalSupportCells
open CyclicCutOrders EuclideanPrismatoidCoordinates PolyhedralInputBridge
open TrimmedFacetWitnesses BandGeometryAssembly FiniteWitnessClosure SingleCutRecovery
open CutSurfaceQuotient MixedTurnSafeCut PolygonSetReconstruction ConvexPolygonTurning
open PhysicalMixedTurnSource

namespace GeneralTwoRimUnfolding
noncomputable section
set_option maxHeartbeats 0

variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

private abbrev negEdge
    (hΔ : intrinsicDelta A B (hh := hh) < 0) : Fin (sideCount A B) :=
  prev (sourceIndexEquiv A B (selectedNegativeCutIndex A B hh hΔ))

private def AdjacentFullGlue (e : Fin (sideCount A B))
    (k : Fin (sideCount A B - 1))
    (f₀ : FaceSpace A B h (order A B e k.castSucc) →ᵃⁱ[ℝ]
      PhysicalMixedTurnSource.Plane)
    (f₁ : FaceSpace A B h (order A B e k.succ) →ᵃⁱ[ℝ]
      PhysicalMixedTurnSource.Plane) : Prop :=
  ∀ x ∈ (certificate A B hh (order A B e k.castSucc)).domain,
  ∀ y ∈ (certificate A B hh (order A B e k.succ)).domain,
    (certificate A B hh (order A B e k.castSucc)).chart x =
    (certificate A B hh (order A B e k.succ)).chart y →
      f₀ x = f₁ y

private theorem selected_adjacent_witness
    (hΔ : intrinsicDelta A B (hh := hh) < 0)
    (k : Fin (sideCount A B - 1)) :
    AdjacentFullGlue A B hh (negEdge A B hh hΔ) k
      (selectedNegativeDirectMap A B hh hΔ k.castSucc)
      (selectedNegativeDirectMap A B hh hΔ k.succ) := by
  exact selectedNegativeDirectMap_adjacent_full_glue A B hh hΔ k

/-- Generic source-chain argument: every uncut original edge is one of the
consecutive original hinges, so adjacent full-material agreement suffices. -/
private theorem source_allUncut_of_adjacent (e : Fin (sideCount A B))
    (U : (i : Fin (sideCount A B - 1 + 1)) →
      FaceSpace A B h (order A B e i) →ᵃⁱ[ℝ] PhysicalMixedTurnSource.Plane)
    (hAdjacent : ∀ k : Fin (sideCount A B - 1),
      AdjacentFullGlue A B hh e k (U k.castSucc) (U k.succ)) :
    AllUncutGlued (fun i => certificate A B hh (order A B e i)) 0
      (fun i => U i) := by
  intro i j hNot ed t ht
  let u := order A B e i
  let v := order A B e j
  have hAdj : MaterialAdjacent A B hh u v :=
    (materialAdjacency_iff_gapEndpoints A B hh u v).mpr
      (arbitraryOriginalEdge_covered A B hh u v ed)
  have hNotPair : ¬ SamePair u v
      (order A B e (Fin.last _)) (order A B e 0) := by
    intro hp
    apply hNot
    rcases hp with ⟨hui, hvj⟩ | ⟨huj, hvi⟩
    · exact Or.inl ⟨(order A B e).injective hui,
        (order A B e).injective hvj⟩
    · exact Or.inr ⟨(order A B e).injective huj,
        (order A B e).injective hvi⟩
  obtain ⟨k, hk⟩ := (uncut_iff_chain A B hh e u v).mp ⟨hAdj, hNotPair⟩
  have ht01 : t ∈ Icc (0 : ℝ) 1 := by
    simpa only [sub_zero] using ht
  have hx : AffineMap.lineMap ed.aL ed.bL t ∈ (certificate A B hh u).domain :=
    lineMap_mem_face (certificate A B hh u).domain_convex
      ed.aL_mem ed.bL_mem ht01
  have hy : AffineMap.lineMap ed.aR ed.bR t ∈ (certificate A B hh v).domain :=
    lineMap_mem_face (certificate A B hh v).domain_convex
      ed.aR_mem ed.bR_mem ht01
  have hxy : (certificate A B hh u).chart
        (AffineMap.lineMap ed.aL ed.bL t) =
      (certificate A B hh v).chart
        (AffineMap.lineMap ed.aR ed.bR t) := by
    calc
      _ = AffineMap.lineMap ((certificate A B hh u).chart ed.aL)
          ((certificate A B hh u).chart ed.bL) t :=
        (certificate A B hh u).chart.toAffineMap.apply_lineMap _ _ _
      _ = AffineMap.lineMap ((certificate A B hh v).chart ed.aR)
          ((certificate A B hh v).chart ed.bR) t := by
        rw [ed.match_a, ed.match_b]
      _ = _ := ((certificate A B hh v).chart.toAffineMap.apply_lineMap _ _ _).symm
  rcases hk with ⟨huk, hvk⟩ | ⟨hvk, huk⟩
  · have hik : i = k.castSucc := (order A B e).injective huk
    have hjk : j = k.succ := (order A B e).injective hvk
    subst i
    subst j
    exact hAdjacent k (AffineMap.lineMap ed.aL ed.bL t) hx
      (AffineMap.lineMap ed.aR ed.bR t) hy hxy
  · have hik : i = k.succ := (order A B e).injective hvk
    have hjk : j = k.castSucc := (order A B e).injective huk
    subst i
    subst j
    exact (hAdjacent k (AffineMap.lineMap ed.aR ed.bR t) hy
      (AffineMap.lineMap ed.aL ed.bL t) hx hxy.symm).symm

/-- Every uncut supporting edge, including endpoints, is glued by the
selected original source direct maps. -/
theorem selectedNegativeDirectMap_allUncutGlued
    (hΔ : intrinsicDelta A B (hh := hh) < 0) :
    AllUncutGlued
      (fun i => certificate A B hh (order A B (negEdge A B hh hΔ) i)) 0
      (fun i => selectedNegativeDirectMap A B hh hΔ i) := by
  apply source_allUncut_of_adjacent A B hh
    (negEdge A B hh hΔ) (selectedNegativeDirectMap A B hh hΔ)
  exact selected_adjacent_witness A B hh hΔ

/-- Full development on the original physical charts and complete source domains. -/
theorem selectedNegativeDirectMap_full_developmentOn
    (hΔ : intrinsicDelta A B (hh := hh) < 0) :
    DevelopmentOn
      (fun i => (certificate A B hh (order A B (negEdge A B hh hΔ) i)).chart.toAffineMap)
      (fun i => (certificate A B hh (order A B (negEdge A B hh hΔ) i)).domain)
      (fun i => selectedNegativeDirectMap A B hh hΔ i) := by
  have hg := all_uncut_material_gluing
    (fun i => certificate A B hh (order A B (negEdge A B hh hΔ) i))
    (fun i => faceSpace_finrank A B h _)
    (fun i => selectedNegativeDirectMap A B hh hΔ i)
    (selectedNegativeDirectMap_allUncutGlued A B hh hΔ)
  constructor
  · intro j
    exact hg j.castSucc j.succ
      (adjacent_not_cutPair (by have hs := three_le_sideCount A B; omega) j)
      (hinge A B hh (negEdge A B hh hΔ) j)
  · intro j
    exact SelectedNegativeRootPolar.selectedNegativeDirectMap_full_safe A B hh hΔ
      j.castSucc j.succ (by
        intro he
        have hv := congrArg Fin.val he
        change j.val = j.val + 1 at hv
        omega)

/-- The original full-domain direct maps yield the unchanged quotient package. -/
noncomputable def selectedNegativeCutSurfaceDevelopment
    (hΔ : intrinsicDelta A B (hh := hh) < 0) :
    CutSurfaceDevelopment A B hh PhysicalMixedTurnSource.Plane (negEdge A B hh hΔ) := by
  let U := selectedNegativeDirectMap A B hh hΔ
  let hDev := selectedNegativeDirectMap_full_developmentOn A B hh hΔ
  exact {
    U := U
    developmentOn := hDev
    safe := SelectedNegativeRootPolar.selectedNegativeDirectMap_full_safe A B hh hΔ
    developedMap := developed U hDev
    developedMap_continuous := developed_continuous U hDev
    materialMap := materialProjection A B hh _
    materialMap_continuous := materialProjection_continuous A B hh _
    materialMap_surjective := materialProjection_surjective A B hh _
    face_injective := faceInclusion_injective A B hh _
    developed_face := developed_faceInclusion U hDev
    material_face := fun i x => congrArg Subtype.val
      (materialProjection_faceInclusion A B hh _ i x)
    seam_material_eq := by
      intro t ht
      apply Subtype.ext
      exact seam_ambient_eq A B hh _ t ht
    seam_copies_distinct := seam_copies_ne A B hh _
    cut_segment := (cut A B hh (negEdge A B hh hΔ)).common_material_edge
      (faceSpace_finrank A B h _)
    lateral_coverage := by
      rw [material_union_reindex
        (fun j => (certificate A B hh j).chart '' (certificate A B hh j).domain)
        (order A B (negEdge A B hh hΔ))]
      exact material_band_eq (halfspaces A B h) (certificate A B hh)
        (rowsEquiv A B) (fun _ => rfl) }

/-- Restrict full-domain safety without changing any of the selected maps. -/
theorem selectedNegativeDirectMap_trim_safe
    (hΔ : intrinsicDelta A B (hh := hh) < 0)
    (d : ℝ) (hd0 : 0 < d) (hd1 : d < (1 : ℝ) / 2) :
    Safe
      (fun i => heightTrim
        (certificate A B hh (order A B (negEdge A B hh hΔ) i)).domain
        (certificate A B hh (order A B (negEdge A B hh hΔ) i)).height d)
      (fun i => selectedNegativeDirectMap A B hh hΔ i) := by
  have hfull := SelectedNegativeRootPolar.selectedNegativeDirectMap_full_safe A B hh hΔ
  intro i j hij
  apply (hfull i j hij).mono
  · exact interior_mono (Set.image_mono (fun x hx => hx.1))
  · exact interior_mono (Set.image_mono (fun x hx => hx.1))

/-- Restrict full-domain gluing and safety to every positive height trim. -/
theorem selectedNegativeDirectMap_trim_developmentOn
    (hΔ : intrinsicDelta A B (hh := hh) < 0)
    (d : ℝ) (hd0 : 0 < d) (hd1 : d < (1 : ℝ) / 2) :
    DevelopmentOn
      (fun i => (certificate A B hh (order A B (negEdge A B hh hΔ) i)).chart.toAffineMap)
      (fun i => heightTrim
        (certificate A B hh (order A B (negEdge A B hh hΔ) i)).domain
        (certificate A B hh (order A B (negEdge A B hh hΔ) i)).height d)
      (fun i => selectedNegativeDirectMap A B hh hΔ i) := by
  apply SingleCutRecovery.developmentOn_mono
    (fun i => (certificate A B hh (order A B (negEdge A B hh hΔ) i)).chart.toAffineMap)
    (fun i => (certificate A B hh (order A B (negEdge A B hh hΔ) i)).domain)
    (fun i => heightTrim
      (certificate A B hh (order A B (negEdge A B hh hΔ) i)).domain
      (certificate A B hh (order A B (negEdge A B hh hΔ) i)).height d)
    (fun i => selectedNegativeDirectMap A B hh hΔ i)
  · intro i x hx
    exact hx.1
  · exact selectedNegativeDirectMap_full_developmentOn A B hh hΔ

/-- A literal radial seam and one unchanged map family work on the full band
and simultaneously at every positive trim depth. -/
noncomputable def selectedNegativeSameCutSameMaps
    (hΔ : intrinsicDelta A B (hh := hh) < 0) :
    SameCutSameMapsResult A B hh := by
  refine {
    e := negEdge A B hh hΔ
    development := selectedNegativeCutSurfaceDevelopment A B hh hΔ
    every_positive_trim := ?_ }
  intro d hd0 hd1
  exact ⟨selectedNegativeDirectMap_trim_developmentOn A B hh hΔ d hd0 hd1,
    selectedNegativeDirectMap_trim_safe A B hh hΔ d hd0 hd1⟩

@[simp] theorem selectedNegativeSameCutSameMaps_U
    (hΔ : intrinsicDelta A B (hh := hh) < 0)
    (i : Fin (sideCount A B - 1 + 1)) :
    (selectedNegativeSameCutSameMaps A B hh hΔ).development.U i =
      selectedNegativeDirectMap A B hh hΔ i := rfl

@[simp] theorem selectedNegativeCutSurfaceDevelopment_U
    (hΔ : intrinsicDelta A B (hh := hh) < 0)
    (i : Fin (sideCount A B - 1 + 1)) :
    (selectedNegativeCutSurfaceDevelopment A B hh hΔ).U i =
      selectedNegativeDirectMap A B hh hΔ i := rfl

#print selectedNegativeSameCutSameMaps
#print axioms selectedNegativeSameCutSameMaps
#print axioms selectedNegativeSameCutSameMaps_U
#print selectedNegativeCutSurfaceDevelopment
#print axioms selectedNegativeCutSurfaceDevelopment
#print axioms selectedNegativeCutSurfaceDevelopment_U

#print selectedNegativeDirectMap_allUncutGlued
#print axioms selectedNegativeDirectMap_allUncutGlued
#print selectedNegativeDirectMap_full_developmentOn
#print axioms selectedNegativeDirectMap_full_developmentOn

end
end GeneralTwoRimUnfolding
