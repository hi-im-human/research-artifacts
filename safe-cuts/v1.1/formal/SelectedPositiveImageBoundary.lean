import SelectedPositiveRootPolarLift

open Set
open scoped Classical NNReal
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CommonSupportMerge OriginalFacetCertificates NormalFanSplice MaximalSupportCells
open CyclicCutOrders EuclideanPrismatoidCoordinates PolyhedralInputBridge
open TrimmedFacetWitnesses BandGeometryAssembly FiniteWitnessClosure SingleCutRecovery
open CutSurfaceQuotient MixedTurnSafeCut PolygonSetReconstruction ConvexPolygonTurning
open FixedBaselinePolarRayGeometry SelectedNegativeRootPolar PhysicalMixedTurnSource

namespace SelectedPositiveRootPolarLift
noncomputable section
set_option maxHeartbeats 8000000
attribute [local irreducible] sourceIndexEquiv positiveRoot

variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

private abbrev N := PhysicalMixedTurnSource.MechanismN A B
private abbrev Δ := PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh)

/-- Keep the dependent source face family generic while consuming the compiled
original-map image-interior theorem. -/
private theorem genericImageBoundary (k : Fin (N A B + 1))
    (i : Fin (N A B + 1)) {p : Plane}
    (hp : p ∈ interior (Set.image
      (fun x : FaceSpace A B h (order A B (prev (sourceIndexEquiv A B k)) i) =>
        GeneralTwoRimUnfolding.arbitraryCutFaceMap A B hh k i x)
      (certificate A B hh (order A B (prev (sourceIndexEquiv A B k)) i)).domain)) :
    ∃ s t : ℝ, s ∈ Ioo (0 : ℝ) 1 ∧ t ∈ Ioo (0 : ℝ) 1 ∧
      p = (rootStrip A B hh k).point i.val s t := by
  exact SelectedNegativeRootPolar.arbitraryCutFaceMap_image_interior_point A B hh k i hp

/-- Strict source-strip coordinates for the full image interior of the actual
positive radial-selected cut; no caller correctness or safety premise. -/
theorem selectedPositiveImageBoundary (hΔ : 0 < Δ A B hh)
    (i : Fin (N A B + 1)) {p : Plane}
    (hp : p ∈ interior (Set.image
      (fun x : FaceSpace A B h
        (order A B (prev (sourceIndexEquiv A B (positiveRoot A B hh hΔ))) i) =>
        GeneralTwoRimUnfolding.arbitraryCutFaceMap A B hh
          (positiveRoot A B hh hΔ) i x)
      (certificate A B hh
        (order A B (prev (sourceIndexEquiv A B (positiveRoot A B hh hΔ))) i)).domain)) :
    ∃ s t : ℝ, s ∈ Ioo (0 : ℝ) 1 ∧ t ∈ Ioo (0 : ℝ) 1 ∧
      p = (rootStrip A B hh (positiveRoot A B hh hΔ)).point i.val s t := by
  exact genericImageBoundary A B hh (positiveRoot A B hh hΔ) i hp

end
end SelectedPositiveRootPolarLift
