import GeneralTwoRimEndpoint
import PhysicalMixedTurnSourceSanity
import GeneralBandClosedApplicationSanity

open Set
open MergedNormalPrismatoid PolygonSupportCompleteness CyclicCutOrdersSanity
open PhysicalMixedTurnSource PhysicalMixedTurnSourceSanityFixtures
open GeneralTwoRimUnfolding GeneralBandClosedApplicationSanity

namespace GeneralTwoRimEndpointSanity
noncomputable section
set_option maxHeartbeats 8000000

private lemma one_pos : (0 : ℝ) < 1 := by norm_num

/-- The shifted-square zero-defect source uses the general endpoint directly. -/
theorem shifted_square_general :
    Nonempty (SameCutSameMapsResult shiftedSquare unitSquare one_pos) :=
  exists_sameCutSameMaps shiftedSquare unitSquare one_pos

/-- The actual triangle/square source has a collapsed original upper rim run;
the complete endpoint requires neither mixedness nor a turn-sign certificate. -/
theorem triangle_square_general :
    Nonempty (SameCutSameMapsResult triangle square one_pos) :=
  exists_sameCutSameMaps triangle square one_pos

theorem triangle_square_reversed_general :
    Nonempty (SameCutSameMapsResult square triangle one_pos) :=
  exists_sameCutSameMaps square triangle one_pos

example : upperPlanarRun triangle square
    PhysicalMixedTurnSourceSanity.collapsedUpperFacet = 0 :=
  PhysicalMixedTurnSourceSanity.collapsedUpperFacet_upperPlanarRun

/-- These exact finite clouds are already proved non-nested. Their general
set endpoint now has no external ordinary-band or shifted-mixedness input. -/
theorem nonnested_finite_hull_general :
    SetCutSurfaceConclusion KA KB KA_finite_hull KB_finite_hull
      KA_interior KB_interior one_pos :=
  general_setCutSurfaceConclusion KA KB KA_finite_hull KB_finite_hull
    KA_interior KB_interior one_pos

example : ¬ KA ⊆ KB := KA_not_subset_KB
example : ¬ KB ⊆ KA := KB_not_subset_KA

end
end GeneralTwoRimEndpointSanity

#check @GeneralTwoRimUnfolding.exists_sameCutSameMaps
#check @GeneralTwoRimUnfolding.general_rawCutSurfaceConclusion
#check @GeneralTwoRimUnfolding.general_setSameCutSameMaps
#check @GeneralTwoRimUnfolding.general_setCutSurfaceConclusion
#check @SelectedPositiveRootPolarLift.selectedPositiveDirectMap_full_safe
#check @GeneralTwoRimUnfolding.selectedPositiveSameCutSameMaps_U
#check @GeneralTwoRimUnfolding.negativeSameCutSameMaps_U
#print GeneralTwoRimUnfolding.SameCutSameMapsResult
#print PhysicalMixedTurnSource.RawCutSurfaceConclusion
#print PhysicalMixedTurnSource.SetCutSurfaceConclusion
#print CutSurfaceQuotient.CutSurfaceDevelopment
#print FiniteWitnessClosure.Safe
#check @GeneralTwoRimUnfolding.selectedPositiveSameCutSameMaps
#check @GeneralTwoRimUnfolding.negativeSameCutSameMaps
#check @GeneralTwoRimUnfolding.exists_sameCutSameMaps_of_delta_zero
#print axioms GeneralTwoRimUnfolding.exists_sameCutSameMaps
#print axioms GeneralTwoRimUnfolding.general_rawCutSurfaceConclusion
#print axioms GeneralTwoRimUnfolding.general_setSameCutSameMaps
#print axioms GeneralTwoRimUnfolding.general_setCutSurfaceConclusion
#print axioms GeneralTwoRimUnfolding.selectedPositiveSameCutSameMaps_U
#print axioms GeneralTwoRimUnfolding.negativeSameCutSameMaps_U
#print axioms GeneralTwoRimEndpointSanity.shifted_square_general
#print axioms GeneralTwoRimEndpointSanity.triangle_square_general
#print axioms GeneralTwoRimEndpointSanity.triangle_square_reversed_general
#print axioms GeneralTwoRimEndpointSanity.nonnested_finite_hull_general
