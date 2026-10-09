import SelectedNegativeHingeGluing
import SourceFullDevelopmentAssembly

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
attribute [local irreducible] sourceIndexEquiv arbitraryCutFaceMap

variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

/-- Apply the generic source assembly to the literal direct maps at a
chosen root. Full safety is supplied internally by the completed sign branch. -/
noncomputable def arbitraryCutSameCutSameMaps_of_safe
    (k : Fin (MechanismN A B + 1))
    (hSafe : Safe
      (fun i => (certificate A B hh (order A B (prev (sourceIndexEquiv A B k)) i)).domain)
      (fun i => arbitraryCutFaceMap A B hh k i)) :
    SameCutSameMapsResult A B hh := by
  apply sourceSameCutSameMaps_of_full A B hh
    (prev (sourceIndexEquiv A B k)) (arbitraryCutFaceMap A B hh k) hSafe
  apply sourceAllUncutGlued_of_adjacent A B hh
    (prev (sourceIndexEquiv A B k)) (arbitraryCutFaceMap A B hh k)
  intro j
  exact arbitraryCutFaceMap_adjacent_full_glue A B hh k j

@[simp] theorem arbitraryCutSameCutSameMaps_of_safe_e
    (k : Fin (MechanismN A B + 1)) (hSafe) :
    (arbitraryCutSameCutSameMaps_of_safe A B hh k hSafe).e =
      prev (sourceIndexEquiv A B k) := rfl

@[simp] theorem arbitraryCutSameCutSameMaps_of_safe_U
    (k : Fin (MechanismN A B + 1)) (hSafe)
    (i : Fin (sideCount A B - 1 + 1)) :
    (arbitraryCutSameCutSameMaps_of_safe A B hh k hSafe).development.U i =
      arbitraryCutFaceMap A B hh k i := rfl

end
end GeneralTwoRimUnfolding
