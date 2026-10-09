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
set_option maxHeartbeats 8000000

variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

def SourceAdjacentFullGlue (e : Fin (sideCount A B))
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

/-- Generic source-chain argument: every uncut original edge is one of the
consecutive original hinges, so adjacent full-material agreement suffices. -/
theorem sourceAllUncutGlued_of_adjacent (e : Fin (sideCount A B))
    (U : (i : Fin (sideCount A B - 1 + 1)) →
      FaceSpace A B h (order A B e i) →ᵃⁱ[ℝ] PhysicalMixedTurnSource.Plane)
    (hAdjacent : ∀ k : Fin (sideCount A B - 1),
      SourceAdjacentFullGlue A B hh e k (U k.castSucc) (U k.succ)) :
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


/-- Internal assembly for an arbitrary original cut and an already proved
full physical map family. The selected-root geometry is absent from this proof. -/
noncomputable def sourceSameCutSameMaps_of_full
    (e : Fin (sideCount A B))
    (U : (i : Fin (sideCount A B - 1 + 1)) →
      FaceSpace A B h (order A B e i) →ᵃⁱ[ℝ] PhysicalMixedTurnSource.Plane)
    (hSafe : Safe
      (fun i => (certificate A B hh (order A B e i)).domain) (fun i => U i))
    (hGlued : AllUncutGlued
      (fun i => certificate A B hh (order A B e i)) 0 (fun i => U i)) :
    SameCutSameMapsResult A B hh := by
  have hDev : DevelopmentOn
      (fun i => (certificate A B hh (order A B e i)).chart.toAffineMap)
      (fun i => (certificate A B hh (order A B e i)).domain)
      (fun i => U i) := by
    have hg := all_uncut_material_gluing
      (fun i => certificate A B hh (order A B e i))
      (fun i => faceSpace_finrank A B h _)
      (fun i => U i)
      hGlued
    constructor
    · intro j
      exact hg j.castSucc j.succ
        (adjacent_not_cutPair (by have hs := three_le_sideCount A B; omega) j)
        (hinge A B hh e j)
    · intro j
      exact hSafe j.castSucc j.succ (by
        intro he
        have hv := congrArg Fin.val he
        change j.val = j.val + 1 at hv
        omega)
  let D : CutSurfaceDevelopment A B hh PhysicalMixedTurnSource.Plane e := {
    U := U
    developmentOn := hDev
    safe := hSafe
    developedMap := developed U hDev
    developedMap_continuous := developed_continuous U hDev
    materialMap := materialProjection A B hh e
    materialMap_continuous := materialProjection_continuous A B hh e
    materialMap_surjective := materialProjection_surjective A B hh e
    face_injective := faceInclusion_injective A B hh e
    developed_face := developed_faceInclusion U hDev
    material_face := fun i x => congrArg Subtype.val
      (materialProjection_faceInclusion A B hh e i x)
    seam_material_eq := by
      intro t ht
      apply Subtype.ext
      exact seam_ambient_eq A B hh e t ht
    seam_copies_distinct := seam_copies_ne A B hh e
    cut_segment := (cut A B hh e).common_material_edge
      (faceSpace_finrank A B h _)
    lateral_coverage := by
      rw [material_union_reindex
        (fun j => (certificate A B hh j).chart '' (certificate A B hh j).domain)
        (order A B e)]
      exact material_band_eq (halfspaces A B h) (certificate A B hh)
        (rowsEquiv A B) (fun _ => rfl) }
  refine { e := e, development := D, every_positive_trim := ?_ }
  intro d hd0 hd1
  constructor
  · apply SingleCutRecovery.developmentOn_mono
      (fun i => (certificate A B hh (order A B e i)).chart.toAffineMap)
      (fun i => (certificate A B hh (order A B e i)).domain)
      (fun i => heightTrim (certificate A B hh (order A B e i)).domain
        (certificate A B hh (order A B e i)).height d)
      (fun i => U i)
    · intro i x hx
      exact hx.1
    · exact hDev
  · intro i j hij
    apply (hSafe i j hij).mono
    · exact interior_mono (Set.image_mono (fun x hx => hx.1))
    · exact interior_mono (Set.image_mono (fun x hx => hx.1))

@[simp] theorem sourceSameCutSameMaps_of_full_e
    (e : Fin (sideCount A B)) (U) (hSafe) (hGlued) :
    (sourceSameCutSameMaps_of_full A B hh e U hSafe hGlued).e = e := rfl

@[simp] theorem sourceSameCutSameMaps_of_full_U
    (e : Fin (sideCount A B)) (U) (hSafe) (hGlued)
    (i : Fin (sideCount A B - 1 + 1)) :
    (sourceSameCutSameMaps_of_full A B hh e U hSafe hGlued).development.U i = U i := rfl

end
end GeneralTwoRimUnfolding
