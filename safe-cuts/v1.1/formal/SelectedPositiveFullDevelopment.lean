import SelectedPositiveFullSafe
import ArbitraryCutFullDevelopment

open Set
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CyclicCutOrders NormalFanSplice
open PhysicalMixedTurnSource SelectedPositiveRootPolarLift

namespace GeneralTwoRimUnfolding
noncomputable section
set_option maxHeartbeats 8000000
attribute [local irreducible] positiveRoot sourceIndexEquiv

variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

/-- The actual positive selected root, with its original source maps, works
on the full lateral surface and on every positive trim. -/
noncomputable def selectedPositiveSameCutSameMaps
    (hΔ : 0 < intrinsicDelta A B (hh := hh)) :
    SameCutSameMapsResult A B hh :=
  arbitraryCutSameCutSameMaps_of_safe A B hh (positiveRoot A B hh hΔ)
    (selectedPositiveDirectMap_full_safe A B hh hΔ)

@[simp] theorem selectedPositiveSameCutSameMaps_e
    (hΔ : 0 < intrinsicDelta A B (hh := hh)) :
    (selectedPositiveSameCutSameMaps A B hh hΔ).e =
      prev (sourceIndexEquiv A B (positiveRoot A B hh hΔ)) := rfl

@[simp] theorem selectedPositiveSameCutSameMaps_U
    (hΔ : 0 < intrinsicDelta A B (hh := hh))
    (i : Fin (sideCount A B - 1 + 1)) :
    (selectedPositiveSameCutSameMaps A B hh hΔ).development.U i =
      arbitraryCutFaceMap A B hh (positiveRoot A B hh hΔ) i := rfl

end
end GeneralTwoRimUnfolding
