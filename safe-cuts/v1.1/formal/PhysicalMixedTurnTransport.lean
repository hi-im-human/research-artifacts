import PhysicalMixedTurnDevelopment

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
set_option maxHeartbeats 2000000

section Raw
variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

theorem orderedDevelopedMap_heightTrim_image (hmix : IntrinsicTMixed A B hh)
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2)
    (i : Fin (MechanismN A B+1)) :
    orderedDevelopedMap A B hh hmix d i ''
        heightTrim (certificate A B hh (cycle A B
          (orderSource A B (fixedCutIndex A B hh hmix) i))).domain
          (certificate A B hh (cycle A B
            (orderSource A B (fixedCutIndex A B hh hmix) i))).height d =
      (physicalDevelopedFamily A B hh hd0 hd1).face
        (fixedCutIndex A B hh hmix) i := by
  let k := fixedCutIndex A B hh hmix
  let s := orderSource A B k i
  have hs : s = familySource A B k i.val := orderSource_eq_familySource A B k i
  change orderedDevelopedMap A B hh hmix d i '' _ =
    hull (familyB A B hh d k i.val) (familyE A B hh d k i.val)
      (familyD A B hh d k i.val) (familyRatio A B hh d k i.val)
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hlocal : intrinsicFaceChart A B hh s x ∈
        hull (localB A B hh d s) (localE A B hh d s)
          (localD A B hh d s) (localRatio A B hh d s) := by
      rw [← intrinsicFaceChart_heightTrim_image A B hh hd0 hd1]
      exact ⟨x, hx, rfl⟩
    have hp : planarPlacement (familyHeading A B hh k i.val)
        (localB A B hh d s) (familyB A B hh d k i.val)
        (intrinsicFaceChart A B hh s x) ∈
        hull (familyB A B hh d k i.val)
          (planeRotation (familyHeading A B hh k i.val) (localE A B hh d s))
          (planeRotation (familyHeading A B hh k i.val) (localD A B hh d s))
          (localRatio A B hh d s) := by
      rw [← planarPlacement_hull]
      exact ⟨_, hlocal, rfl⟩
    change planarPlacement (familyHeading A B hh k i.val)
        (localB A B hh d s) (familyB A B hh d k i.val)
        (intrinsicFaceChart A B hh s x) ∈
      hull (familyB A B hh d k i.val) (familyE A B hh d k i.val)
        (familyD A B hh d k i.val) (familyRatio A B hh d k i.val)
    simpa [familyE, familyD, familyRatio, hs] using hp
  · intro hz
    have hp : z ∈ planarPlacement (familyHeading A B hh k i.val)
        (localB A B hh d s) (familyB A B hh d k i.val) ''
        hull (localB A B hh d s) (localE A B hh d s)
          (localD A B hh d s) (localRatio A B hh d s) := by
      rw [planarPlacement_hull]
      simpa [familyE, familyD, familyRatio, hs] using hz
    obtain ⟨y, hy, hyz⟩ := hp
    rw [← intrinsicFaceChart_heightTrim_image A B hh hd0 hd1] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    refine ⟨x, hx, ?_⟩
    change planarPlacement _ _ _ (intrinsicFaceChart A B hh s x) = z
    rw [hxy, hyz]


end Raw
end
end PhysicalMixedTurnSource
