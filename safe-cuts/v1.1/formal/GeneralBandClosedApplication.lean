import PolygonSetReconstruction

/-!
# Conditional ordinary-to-closed general annular band reduction

The only imported mathematical premise supplies an ordinary trimmed flat state
at each depth. Both its seam and its layout may depend on that depth. The
existing recovery and cut-surface constructions are reused without alteration.
-/

open Set
open scoped Pointwise Classical
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CommonSupportMerge OriginalFacetCertificates MaximalSupportCells CyclicCutOrders
open EuclideanPrismatoidCoordinates PolyhedralInputBridge
open TrimmedFacetWitnesses BandGeometryAssembly FiniteWitnessClosure SingleCutRecovery
open NestedBandExternalApplication CutSurfaceQuotient PolygonSetReconstruction

namespace GeneralBandClosedApplication
noncomputable section

section Raw
variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)
  (Q : Type*) [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]

/-- The external ordinary general-band theorem supplies only per-depth states. -/
def ExternalGeneralBandTheorem : Prop :=
  ∀ (d : ℝ), 0 < d → d < (1 : ℝ)/2 →
    Nonempty (TrimmedFlatState A B hh Q d)

variable [FiniteDimensional ℝ Q]

/-- Recover one full safe face table; finite/cofinal seam selection belongs to
SingleCutRecovery, not to the external premise. -/
theorem recover_full_face_table_from_external_general_band
    (hExternal : ExternalGeneralBandTheorem A B hh Q)
    (hdQ : Module.finrank ℝ Q = 2) :
    ∃ e : Fin (sideCount A B),
      ∃ U : (i : Fin (sideCount A B-1+1)) →
        FaceSpace A B h (order A B e i) →ᵃⁱ[ℝ] Q,
      DevelopmentOn
          (fun i => (certificate A B hh (order A B e i)).chart.toAffineMap)
          (fun i => (certificate A B hh (order A B e i)).domain)
          (fun i => U i) ∧
      Safe (fun i => (certificate A B hh (order A B e i)).domain)
          (fun i => U i) ∧
      AllUncutGlued (fun i => certificate A B hh (order A B e i)) 0
          (fun i => U i) ∧
      (∀ i j, ¬ CutPair i j →
        ∀ _ed : OriginalEdge
          (certificate A B hh (order A B e i))
          (certificate A B hh (order A B e j)),
        ∀ x ∈ (certificate A B hh (order A B e i)).domain,
        ∀ y ∈ (certificate A B hh (order A B e j)).domain,
          (certificate A B hh (order A B e i)).chart x =
            (certificate A B hh (order A B e j)).chart y →
          U i x = U j y) ∧
      (((certificate A B hh (order A B e (Fin.last _))).chart ''
          (certificate A B hh (order A B e (Fin.last _))).domain) ∩
        ((certificate A B hh (order A B e 0)).chart ''
          (certificate A B hh (order A B e 0)).domain) =
        AffineMap.lineMap
          ((certificate A B hh (order A B e (Fin.last _))).chart
            (cut A B hh e).aL)
          ((certificate A B hh (order A B e (Fin.last _))).chart
            (cut A B hh e).bL) '' Icc (0 : ℝ) 1) ∧
      (⋃ i, (certificate A B hh (order A B e i)).chart ''
        (certificate A B hh (order A B e i)).domain) =
        lateralBoundary (halfspaces A B h) := by
  apply SingleCutRecovery.exists_safe_glued_table_from_trimmed_unfoldings
    (halfspaces A B h) (certificate A B hh) (rowsEquiv A B)
    (fun _ => rfl)
    (by have hs := three_le_sideCount A B; omega)
    (faceSpace_finrank A B h) hdQ
    (order A B) (hinge A B hh) (cut A B hh)
  intro d hd0 hd1
  obtain ⟨s⟩ := hExternal d hd0 hd1
  exact ⟨s.seam, s.layout.T, developmentOn_of_flat_state hd0 hd1 s,
    s.layout.safe, allUncutGlued_of_flat_state hd0 hd1 s⟩

/-- Populate the unchanged actual cut-surface development package. -/
theorem exists_continuous_cut_surface_unfolding_from_external_general_band
    (hExternal : ExternalGeneralBandTheorem A B hh Q)
    (hdQ : Module.finrank ℝ Q = 2) :
    ∃ e : Fin (sideCount A B), Nonempty (CutSurfaceDevelopment A B hh Q e) := by
  obtain ⟨e,U,hDev,hSafe,_hAllUncut,_hMaterialGlue,hCut,hCover⟩ :=
    recover_full_face_table_from_external_general_band A B hh Q hExternal hdQ
  refine ⟨e,⟨{
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
    seam_material_eq := ?_
    seam_copies_distinct := seam_copies_ne A B hh e
    cut_segment := hCut
    lateral_coverage := hCover }⟩⟩
  intro t ht
  apply Subtype.ext
  exact seam_ambient_eq A B hh e t ht

end Raw

/-- The single symbolic external premise for presentations of the original sets. -/
def ExternalGeneralBandForSets (KA KB : Set Plane) {h : ℝ} (hh : 0 < h) : Prop :=
  ∀ (PA : RawPresentation KA) (PB : RawPresentation KB),
    ExternalGeneralBandTheorem PA.polygon PB.polygon hh Plane

/-- Construct raw presentations internally and retain the exact Euclidean body. -/
theorem exists_cut_surface_for_general_polygon_sets (KA KB : Set Plane)
    (hfinA : ∃ S : Finset Plane, convexHull ℝ (↑S : Set Plane) = KA)
    (hfinB : ∃ S : Finset Plane, convexHull ℝ (↑S : Set Plane) = KB)
    (hintA : (interior KA).Nonempty) (hintB : (interior KB).Nonempty)
    {h : ℝ} (hh : 0 < h)
    (hExternal : ExternalGeneralBandForSets KA KB hh) :
    ∃ (PA : RawPresentation KA) (PB : RawPresentation KB),
      PA.polygon.body = KA ∧ PB.polygon.body = KB ∧
      physicalBodyOfSets KA KB h = physicalPrismatoid PA.polygon PB.polygon h ∧
      ∃ e : Fin (sideCount PA.polygon PB.polygon),
        Nonempty (CutSurfaceDevelopment PA.polygon PB.polygon hh Plane e) := by
  obtain ⟨PA⟩ := exists_reduced_polygon_of_polygon_set KA hfinA hintA
  obtain ⟨PB⟩ := exists_reduced_polygon_of_polygon_set KB hfinB hintB
  refine ⟨PA, PB, PA.body_eq, PB.body_eq, physicalBodyOfSets_eq PA PB h, ?_⟩
  exact exists_continuous_cut_surface_unfolding_from_external_general_band
    PA.polygon PB.polygon hh Plane (hExternal PA PB) (by simp [Plane])

end
end GeneralBandClosedApplication

set_option pp.proofs false in
#print GeneralBandClosedApplication.ExternalGeneralBandTheorem
#print axioms GeneralBandClosedApplication.ExternalGeneralBandTheorem
#check @GeneralBandClosedApplication.recover_full_face_table_from_external_general_band
#print axioms GeneralBandClosedApplication.recover_full_face_table_from_external_general_band
#check @GeneralBandClosedApplication.exists_continuous_cut_surface_unfolding_from_external_general_band
#print axioms GeneralBandClosedApplication.exists_continuous_cut_surface_unfolding_from_external_general_band
#print GeneralBandClosedApplication.ExternalGeneralBandForSets
#print axioms GeneralBandClosedApplication.ExternalGeneralBandForSets
#check @GeneralBandClosedApplication.exists_cut_surface_for_general_polygon_sets
#print axioms GeneralBandClosedApplication.exists_cut_surface_for_general_polygon_sets
