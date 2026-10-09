import PhysicalMixedTurnState

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

theorem physical_external_general_band (hmix : IntrinsicTMixed A B hh) :
    GeneralBandClosedApplication.ExternalGeneralBandTheorem A B hh Plane := by
  intro d hd0 hd1
  exact ⟨fixedTrimmedFlatState A B hh hmix hd0 hd1⟩

/-- Raw actual-source cut-surface development, with no supplied charts,
developments, budgets, image certificate, or safety premise. -/
theorem physical_exists_cutSurfaceDevelopment (hmix : IntrinsicTMixed A B hh) :
    ∃ e : Fin (sideCount A B), Nonempty (CutSurfaceDevelopment A B hh Plane e) :=
  ⟨fixedSourceSeam A B hh hmix, physical_fixedCutSurfaceDevelopment A B hh hmix⟩

theorem physical_rawCutSurfaceConclusion (hmix : IntrinsicTMixed A B hh) :
    RawCutSurfaceConclusion A B hh :=
  physical_exists_cutSurfaceDevelopment A B hh hmix

/-- The canonical finite face-hull table on the actual source, recovered from
the one fixed trim-independent source cut.  Its last conjunct is exact source
coverage of the lateral boundary. -/
theorem physical_full_face_table (hmix : IntrinsicTMixed A B hh) :
    ∃ e : Fin (sideCount A B),
      ∃ U : (i : Fin (sideCount A B-1+1)) →
        FaceSpace A B h (order A B e i) →ᵃⁱ[ℝ] Plane,
      DevelopmentOn
          (fun i => (certificate A B hh (order A B e i)).chart.toAffineMap)
          (fun i => (certificate A B hh (order A B e i)).domain)
          (fun i => U i) ∧
      Safe (fun i => (certificate A B hh (order A B e i)).domain) (fun i => U i) ∧
      AllUncutGlued (fun i => certificate A B hh (order A B e i)) 0 (fun i => U i) ∧
      (⋃ i, (certificate A B hh (order A B e i)).chart ''
        (certificate A B hh (order A B e i)).domain) =
        lateralBoundary (halfspaces A B h) := by
  obtain ⟨e,U,hdev,hsafe,hglue,_hmaterial,_hcut,hcover⟩ :=
    GeneralBandClosedApplication.recover_full_face_table_from_external_general_band
      A B hh Plane (physical_external_general_band A B hh hmix) (by simp [Plane])
  exact ⟨e,U,hdev,hsafe,hglue,hcover⟩

end Raw

section Sets

/-- Ordinary finite-hull endpoint using exactly the canonical presentations
constructed from the two input sets.  No presentation, development, budget,
image certificate, or safety fact is supplied by the caller. -/
theorem physical_setCutSurfaceConclusion (KA KB : Set Plane)
    (hfinA : ∃ S : Finset Plane, convexHull ℝ (↑S : Set Plane) = KA)
    (hfinB : ∃ S : Finset Plane, convexHull ℝ (↑S : Set Plane) = KB)
    (hintA : (interior KA).Nonempty) (hintB : (interior KB).Nonempty)
    {h : ℝ} (hh : 0 < h)
    (hmix : SetIntrinsicTMixed KA KB hfinA hfinB hintA hintB hh) :
    SetCutSurfaceConclusion KA KB hfinA hfinB hintA hintB hh := by
  let PA := canonicalPresentation KA hfinA hintA
  let PB := canonicalPresentation KB hfinB hintB
  refine ⟨PA.body_eq, PB.body_eq, physicalBodyOfSets_eq PA PB h, ?_⟩
  exact physical_exists_cutSurfaceDevelopment PA.polygon PB.polygon hh hmix

end Sets
end
end PhysicalMixedTurnSource
