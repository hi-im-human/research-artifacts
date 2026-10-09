import GeneralTwoRimUnfolding
import PhysicalMixedTurnSourceSanityFixtures

open scoped BigOperators Classical NNReal
open PhysicalMixedTurnSource
open PhysicalMixedTurnSourceSanityFixtures
open GeneralTwoRimUnfolding RadialExtremalSafety
open MixedTurnSafeCut CutSurfaceQuotient NormalFanSplice CyclicCutOrders

namespace GeneralTwoRimUnfoldingSanity
noncomputable section

private lemma one_pos : (0 : ℝ) < 1 := by norm_num

example :
    (∑ i, upperPlanarRun shiftedSquare unitSquare i) = 0 :=
  sum_upperPlanarRun_eq_zero shiftedSquare unitSquare

example :
    0 < ∑ i, upperRunCoeff shiftedSquare unitSquare one_pos i :=
  sum_upperRunCoeff_pos shiftedSquare unitSquare one_pos

example :
    ∃ e : Fin (sideCount shiftedSquare unitSquare),
      Nonempty (CutSurfaceDevelopment shiftedSquare unitSquare one_pos
        PhysicalMixedTurnSource.Plane e) :=
  zero_delta_cutSurfaceDevelopment shiftedSquare unitSquare one_pos shiftedDelta_zero

example (x y : RadialExtremalSafety.Plane) :
    det (reflectPlane x) (reflectPlane y) = -det x y :=
  det_reflectPlane x y

example (c₀ c₁ c₂ : Fin 4 → ℝ) :
    ∃ k ε, 0 < ε ∧ ∀ i δ, 0 < δ → δ < ε →
      quadraticValue c₀ c₁ c₂ i δ ≤ quadraticValue c₀ c₁ c₂ k δ :=
  exists_eventual_quadratic_max c₀ c₁ c₂

end
end GeneralTwoRimUnfoldingSanity

#print axioms FoldedTurnProjection.projection_pos
#print axioms PhysicalMixedTurnSource.circuitPole_fixed
#print axioms PhysicalMixedTurnSource.upper_projection_sum_eq_circuit
#print axioms PhysicalMixedTurnSource.physical_negative_RF
#print axioms PhysicalMixedTurnSource.physical_positive_RF
#print axioms RadialExtremalSafety.exists_eventual_quadratic_max
#print axioms GeneralTwoRimUnfolding.exists_sameCutSameMaps_of_delta_zero
