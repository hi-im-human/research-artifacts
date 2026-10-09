import SelectedNegativeDirectDevelopment
import SelectedPositiveFullDevelopment

open Set
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CyclicCutOrders NormalFanSplice CutSurfaceQuotient PolygonSetReconstruction
open EuclideanPrismatoidCoordinates
open PhysicalMixedTurnSource

namespace GeneralTwoRimUnfolding
noncomputable section
set_option maxHeartbeats 8000000

section Raw
variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

/-- Every actual positive-area two-rim source has one original cut and one
literal full map family, safe and developed at every positive trim. -/
theorem exists_sameCutSameMaps : Nonempty (SameCutSameMapsResult A B hh) := by
  rcases lt_trichotomy (intrinsicDelta A B (hh := hh)) 0 with hneg | hzero | hpos
  · exact ⟨negativeSameCutSameMaps A B hh hneg⟩
  · exact exists_sameCutSameMaps_of_delta_zero A B hh hzero
  · exact ⟨selectedPositiveSameCutSameMaps A B hh hpos⟩

/-- The public raw original-source endpoint has no additional angular,
safety, radial-support, chart or external ordinary-band premise. -/
theorem general_rawCutSurfaceConclusion : RawCutSurfaceConclusion A B hh := by
  obtain ⟨D⟩ := exists_sameCutSameMaps A B hh
  exact ⟨D.e, ⟨D.development⟩⟩

end Raw

/-- Canonical finite-hull presentations preserve the original rim sets and
body. The same source cut/map contract needs no shifted-mixedness premise. -/
theorem general_setSameCutSameMaps
    (KA KB : Set PhysicalMixedTurnSource.Plane)
    (hfinA : ∃ S : Finset PhysicalMixedTurnSource.Plane, convexHull ℝ (↑S : Set _) = KA)
    (hfinB : ∃ S : Finset PhysicalMixedTurnSource.Plane, convexHull ℝ (↑S : Set _) = KB)
    (hintA : (interior KA).Nonempty) (hintB : (interior KB).Nonempty)
    {h : ℝ} (hh : 0 < h) :
    let PA := canonicalPresentation KA hfinA hintA
    let PB := canonicalPresentation KB hfinB hintB
    PA.polygon.body = KA ∧ PB.polygon.body = KB ∧
      physicalBodyOfSets KA KB h = physicalPrismatoid PA.polygon PB.polygon h ∧
      Nonempty (SameCutSameMapsResult PA.polygon PB.polygon hh) := by
  let PA := canonicalPresentation KA hfinA hintA
  let PB := canonicalPresentation KB hfinB hintB
  exact ⟨PA.body_eq, PB.body_eq, physicalBodyOfSets_eq PA PB h,
    exists_sameCutSameMaps PA.polygon PB.polygon hh⟩

/-- Complete static original-hinge endpoint for two positive-area finite-hull
polygonal rims, retaining the independently defined physical body. -/
theorem general_setCutSurfaceConclusion
    (KA KB : Set PhysicalMixedTurnSource.Plane)
    (hfinA : ∃ S : Finset PhysicalMixedTurnSource.Plane, convexHull ℝ (↑S : Set _) = KA)
    (hfinB : ∃ S : Finset PhysicalMixedTurnSource.Plane, convexHull ℝ (↑S : Set _) = KB)
    (hintA : (interior KA).Nonempty) (hintB : (interior KB).Nonempty)
    {h : ℝ} (hh : 0 < h) :
    SetCutSurfaceConclusion KA KB hfinA hfinB hintA hintB hh := by
  let PA := canonicalPresentation KA hfinA hintA
  let PB := canonicalPresentation KB hfinB hintB
  exact ⟨PA.body_eq, PB.body_eq, physicalBodyOfSets_eq PA PB h,
    general_rawCutSurfaceConclusion PA.polygon PB.polygon hh⟩

end
end GeneralTwoRimUnfolding
