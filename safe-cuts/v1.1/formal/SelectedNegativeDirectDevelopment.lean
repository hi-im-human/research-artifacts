import SelectedRootInteriorWitness
import ArbitraryCutFullDevelopment

open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CyclicCutOrders NormalFanSplice PhysicalMixedTurnSource

namespace GeneralTwoRimUnfolding
noncomputable section
set_option maxHeartbeats 8000000
attribute [local irreducible] sourceIndexEquiv selectedNegativeCutIndex

variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

/-- Reuse the checked negative full-safety theorem through the same generic
original-source assembly as the positive branch. The old negative packaging
module remains unchanged as a historical receipt. -/
noncomputable def negativeSameCutSameMaps
    (hΔ : intrinsicDelta A B (hh := hh) < 0) :
    SameCutSameMapsResult A B hh :=
  arbitraryCutSameCutSameMaps_of_safe A B hh (selectedNegativeCutIndex A B hh hΔ)
    (SelectedNegativeRootPolar.selectedNegativeDirectMap_full_safe A B hh hΔ)

@[simp] theorem negativeSameCutSameMaps_e
    (hΔ : intrinsicDelta A B (hh := hh) < 0) :
    (negativeSameCutSameMaps A B hh hΔ).e =
      prev (sourceIndexEquiv A B (selectedNegativeCutIndex A B hh hΔ)) := rfl

@[simp] theorem negativeSameCutSameMaps_U
    (hΔ : intrinsicDelta A B (hh := hh) < 0)
    (i : Fin (sideCount A B - 1 + 1)) :
    (negativeSameCutSameMaps A B hh hΔ).development.U i =
      selectedNegativeDirectMap A B hh hΔ i := rfl

end
end GeneralTwoRimUnfolding
