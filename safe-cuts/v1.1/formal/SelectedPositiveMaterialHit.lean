import SelectedPositiveImageBoundary

open Set
open scoped Classical NNReal
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CyclicCutOrders EuclideanPrismatoidCoordinates
open FixedBaselinePolarRayGeometry SelectedNegativeRootPolar PhysicalMixedTurnSource

namespace SelectedPositiveRootPolarLift
noncomputable section
set_option maxHeartbeats 8000000
attribute [local irreducible] positiveRoot sourceIndexEquiv

variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

/-- Reflection of a point already identified in the actual selected source
strip. This interface carries no dependent image/coercion expression. -/
theorem reflected_source_point
    (hΔ : 0 < intrinsicDelta A B (hh := hh))
    {i : ℕ} {s t : ℝ} {p : Plane}
    (hp : p = (rootStrip A B hh (positiveRoot A B hh hΔ)).point i s t) :
    RadialExtremalSafety.reflectPlane p =
      (normalizedStrip A B hh hΔ).point i s (1 - t) := by
  exact (congrArg RadialExtremalSafety.reflectPlane hp).trans
    (normalized_point A B hh hΔ i s t).symm

/-- Strict source coordinates give an actual normalized polar hit at its own
real lift. The height reversal is explicit and is performed exactly once. -/
theorem reflected_source_materialHit
    (hΔ : 0 < intrinsicDelta A B (hh := hh))
    {i : ℕ} (hi : i ≤ MechanismN A B) {s t : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    MaterialHit A B hh hΔ (pointPolarLift A B hh hΔ i s (1 - t))
      0 i s (1 - t) := by
  refine ⟨hi, ⟨hs.1.le, hs.2.le⟩,
    ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
  simp only [Int.cast_zero, mul_zero, add_zero]

end
end SelectedPositiveRootPolarLift
