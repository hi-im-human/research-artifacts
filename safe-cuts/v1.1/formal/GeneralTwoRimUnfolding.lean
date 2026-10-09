import PhysicalMixedTurnBridge
import ArbitraryCutDirectMap
import PhysicalRadialSupport
import RadialExtremalSafety

open Set
open scoped BigOperators Classical NNReal
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CommonSupportMerge OriginalFacetCertificates NormalFanSplice MaximalSupportCells
open CyclicCutOrders EuclideanPrismatoidCoordinates PolyhedralInputBridge
open TrimmedFacetWitnesses BandGeometryAssembly FiniteWitnessClosure SingleCutRecovery
open CutSurfaceQuotient MixedTurnSafeCut PolygonSetReconstruction ConvexPolygonTurning

namespace GeneralTwoRimUnfolding
noncomputable section
set_option maxHeartbeats 8000000

open PhysicalMixedTurnSource

section Raw
variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

/-- The exact fixed-seam/fixed-map contract needed at the public boundary.
The full-domain map family is literally `development.U`; the same field is
used in every positive trim. -/
structure SameCutSameMapsResult where
  e : Fin (sideCount A B)
  development :
    CutSurfaceDevelopment A B hh PhysicalMixedTurnSource.Plane e
  every_positive_trim :
    ∀ d : ℝ, 0 < d → d < (1 : ℝ) / 2 →
      DevelopmentOn
        (fun i => (certificate A B hh (order A B e i)).chart.toAffineMap)
        (fun i => heightTrim
          (certificate A B hh (order A B e i)).domain
          (certificate A B hh (order A B e i)).height d)
        (fun i => development.U i) ∧
      Safe
        (fun i => heightTrim
          (certificate A B hh (order A B e i)).domain
          (certificate A B hh (order A B e i)).height d)
        (fun i => development.U i)

/-- Existing T-mixed data satisfy the stronger same-map contract. -/
theorem sameCutSameMaps_of_intrinsicTMixed (hmix : IntrinsicTMixed A B hh) :
    Nonempty (SameCutSameMapsResult A B hh) := by
  let D := physicalFixedCutSurfaceDevelopment A B hh hmix
  refine ⟨{
    e := fixedSourceSeam A B hh hmix
    development := D
    every_positive_trim := ?_ }⟩
  intro d hd0 hd1
  change DevelopmentOn
      (fun i => (certificate A B hh
        (order A B (fixedSourceSeam A B hh hmix) i)).chart.toAffineMap)
      (fun i => heightTrim
        (certificate A B hh (order A B (fixedSourceSeam A B hh hmix) i)).domain
        (certificate A B hh (order A B (fixedSourceSeam A B hh hmix) i)).height d)
      (fun i => physicalFaceMap A B hh hmix i) ∧
    Safe
      (fun i => heightTrim
        (certificate A B hh (order A B (fixedSourceSeam A B hh hmix) i)).domain
        (certificate A B hh (order A B (fixedSourceSeam A B hh hmix) i)).height d)
      (fun i => physicalFaceMap A B hh hmix i)
  exact physicalFaceMap_every_positive_trim A B hh hmix hd0 hd1

/-- A zero real rotational defect forces the existing weak shifted crossing on
the actual nonempty finite source cycle.  This branch deliberately constructs
no affine pole: its full circuit may be a nonzero translation. -/
theorem intrinsicTMixed_of_intrinsicDelta_eq_zero
    (hΔ : intrinsicDelta A B (hh := hh) = 0) :
    IntrinsicTMixed A B hh := by
  rw [intrinsicTMixed_iff_sum_between_values]
  constructor
  · by_contra hn
    push_neg at hn
    have hpos : ∀ i : SourceIndex A B, 0 < intrinsicQ A B (hh := hh) i := by
      intro i
      have hi := hn i
      rw [hΔ] at hi
      exact hi
    have hsum : 0 < ∑ i, intrinsicQ A B (hh := hh) i := by
      apply Finset.sum_pos'
      · intro i _
        exact le_of_lt (hpos i)
      · exact ⟨0, Finset.mem_univ 0, hpos 0⟩
    exact (ne_of_gt hsum) hΔ
  · by_contra hn
    push_neg at hn
    have hneg : ∀ i : SourceIndex A B, intrinsicQ A B (hh := hh) i < 0 := by
      intro i
      have hi := hn i
      rw [hΔ] at hi
      exact hi
    have hsum : 0 < ∑ i, -intrinsicQ A B (hh := hh) i := by
      apply Finset.sum_pos'
      · intro i _
        exact le_of_lt (neg_pos.mpr (hneg i))
      · exact ⟨0, Finset.mem_univ 0, neg_pos.mpr (hneg 0)⟩
    have hsum' : (∑ i, intrinsicQ A B (hh := hh) i) < 0 := by
      rw [Finset.sum_neg_distrib] at hsum
      linarith
    exact (ne_of_lt hsum') hΔ

/-- Zero defect reuses the existing checked T-mixed construction, including its
single seam and depth-independent full map family. -/
theorem exists_sameCutSameMaps_of_delta_zero
    (hΔ : intrinsicDelta A B (hh := hh) = 0) :
    Nonempty (SameCutSameMapsResult A B hh) :=
  sameCutSameMaps_of_intrinsicTMixed A B hh
    (intrinsicTMixed_of_intrinsicDelta_eq_zero A B hh hΔ)

/-- Minimal existing quotient endpoint for the zero-defect branch. -/
theorem zero_delta_cutSurfaceDevelopment
    (hΔ : intrinsicDelta A B (hh := hh) = 0) :
    ∃ e : Fin (sideCount A B),
      Nonempty (CutSurfaceDevelopment A B hh PhysicalMixedTurnSource.Plane e) :=
  physical_exists_cutSurfaceDevelopment A B hh
    (intrinsicTMixed_of_intrinsicDelta_eq_zero A B hh hΔ)

end Raw
end
end GeneralTwoRimUnfolding
