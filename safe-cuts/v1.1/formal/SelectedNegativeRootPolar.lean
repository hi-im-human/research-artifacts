import GeneralTwoRimUnfolding
import FixedBaselinePolarRayGeometry

open Set
open scoped BigOperators Classical NNReal
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CommonSupportMerge OriginalFacetCertificates NormalFanSplice MaximalSupportCells
open CyclicCutOrders EuclideanPrismatoidCoordinates PolyhedralInputBridge
open TrimmedFacetWitnesses BandGeometryAssembly FiniteWitnessClosure SingleCutRecovery
open CutSurfaceQuotient MixedTurnSafeCut PolygonSetReconstruction ConvexPolygonTurning

namespace SelectedNegativeRootPolar
noncomputable section
set_option maxHeartbeats 8000000

variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

abbrev Plane := MixedTurnSafeCut.Plane
abbrev N := PhysicalMixedTurnSource.MechanismN A B

/-- The literal direct source family, cyclically rooted at its chosen entry seam. -/
noncomputable def rootStrip (k : Fin (N A B + 1)) :
    RadialExtremalSafety.TriangularRadialStrip (N A B) where
  B i := PhysicalMixedTurnSource.developedLower A B hh k i
  v i := PhysicalMixedTurnSource.developedForward A B hh k i
  d i := PhysicalMixedTurnSource.developedUpper A B hh k i -
    PhysicalMixedTurnSource.developedLower A B hh k i
  lowerCoeff i := PhysicalMixedTurnSource.lowerRunCoeff A B hh
    (PhysicalMixedTurnSource.familySource A B k i)
  upperCoeff i := PhysicalMixedTurnSource.upperRunCoeff A B hh
    (PhysicalMixedTurnSource.familySource A B k i)
  v_ne_zero i hi := PhysicalMixedTurnSource.developedForward_ne_zero A B hh k i
  lowerCoeff_nonneg i hi := PhysicalMixedTurnSource.lowerRunCoeff_nonneg A B hh _
  upperCoeff_nonneg i hi := PhysicalMixedTurnSource.upperRunCoeff_nonneg A B hh _
  lower_step i hi := by
    have hs := PhysicalMixedTurnSource.developedLower_succ_sub A B hh k i
    calc
      _ = (PhysicalMixedTurnSource.developedLower A B hh k (i + 1) -
            PhysicalMixedTurnSource.developedLower A B hh k i) +
          PhysicalMixedTurnSource.developedLower A B hh k i := by abel
      _ = _ := by rw [hs]; abel
  hinge_step i hi := by
    have hu := PhysicalMixedTurnSource.developedUpper_succ_sub A B hh k i
    have hl := PhysicalMixedTurnSource.developedLower_succ_sub A B hh k i
    change PhysicalMixedTurnSource.developedUpper A B hh k (i + 1) -
        PhysicalMixedTurnSource.developedLower A B hh k (i + 1) = _
    rw [show PhysicalMixedTurnSource.developedUpper A B hh k (i + 1) =
        PhysicalMixedTurnSource.developedUpper A B hh k i +
          PhysicalMixedTurnSource.upperRunCoeff A B hh
            (PhysicalMixedTurnSource.familySource A B k i) •
              PhysicalMixedTurnSource.developedForward A B hh k i by
          calc
            _ = (PhysicalMixedTurnSource.developedUpper A B hh k (i + 1) -
                  PhysicalMixedTurnSource.developedUpper A B hh k i) +
                PhysicalMixedTurnSource.developedUpper A B hh k i := by abel
            _ = _ := by rw [hu]; abel,
      show PhysicalMixedTurnSource.developedLower A B hh k (i + 1) =
        PhysicalMixedTurnSource.developedLower A B hh k i +
          PhysicalMixedTurnSource.lowerRunCoeff A B hh
            (PhysicalMixedTurnSource.familySource A B k i) •
              PhysicalMixedTurnSource.developedForward A B hh k i by
          calc
            _ = (PhysicalMixedTurnSource.developedLower A B hh k (i + 1) -
                  PhysicalMixedTurnSource.developedLower A B hh k i) +
                PhysicalMixedTurnSource.developedLower A B hh k i := by abel
            _ = _ := by rw [hl]; abel]
    module
  orientation_neg i hi :=
    PhysicalMixedTurnSource.developed_hinge_orientation_neg A B hh k i

/-- Source headings form one real, rather than merely quotient-angle, lift. -/
noncomputable def rootHeading (k : Fin (N A B + 1)) (i : ℕ) : ℝ :=
  PhysicalMixedTurnSource.familyHeading A B hh k i

theorem rootHeading_terminal (k : Fin (N A B + 1)) :
    rootHeading A B hh k (N A B + 1) =
      PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) :=
  PhysicalMixedTurnSource.familyHeading_full A B hh k

/-- A single real offset, including on wrapped panels: no reduction modulo a turn. -/
theorem rootHeading_alignment (k : Fin (N A B + 1)) (i : ℕ) :
    PhysicalMixedTurnSource.familyHeading A B hh 0 (k.val + i) =
      PhysicalMixedTurnSource.familyHeading A B hh 0 k.val +
        rootHeading A B hh k i :=
  PhysicalMixedTurnSource.baseline_familyHeading A B hh k i

/-- The affine isometry carries each k-root panel point to the corresponding
unwrapped baseline panel point, including positions beyond the first cycle. -/
theorem rootStrip_alignment (k : Fin (N A B + 1)) (i : ℕ) (s t : ℝ) :
    PhysicalMixedTurnSource.baselineAlignment A B hh k
        ((rootStrip A B hh k).point i s t) =
      (FixedBaselinePolarRayGeometry.baselineStrip A B hh).point (k.val + i) s t := by
  let T := PhysicalMixedTurnSource.baselineAlignment A B hh k
  have hl := PhysicalMixedTurnSource.baselineAlignment_developedLower A B hh k i
  have hu := PhysicalMixedTurnSource.baselineAlignment_developedUpper A B hh k i
  have hv := PhysicalMixedTurnSource.baselineAlignment_developedForward A B hh k i
  have hs := PhysicalMixedTurnSource.baseline_familySource A B k i
  have hdiff (x y : Plane) : T x - T y =
      PhysicalMixedTurnSource.planeRotation
        (PhysicalMixedTurnSource.familyHeading A B hh 0 k.val) (x - y) :=
    PhysicalMixedTurnSource.baselineAlignment_heading_sub A B hh k x y
  simp only [RadialExtremalSafety.TriangularRadialStrip.point,
    rootStrip, FixedBaselinePolarRayGeometry.baselineStrip]
  rw [show PhysicalMixedTurnSource.developedLower A B hh k i +
      t • (PhysicalMixedTurnSource.developedUpper A B hh k i -
        PhysicalMixedTurnSource.developedLower A B hh k i) +
      (s * ((1 - t) * PhysicalMixedTurnSource.lowerRunCoeff A B hh
          (PhysicalMixedTurnSource.familySource A B k i) +
        t * PhysicalMixedTurnSource.upperRunCoeff A B hh
          (PhysicalMixedTurnSource.familySource A B k i))) •
        PhysicalMixedTurnSource.developedForward A B hh k i =
      (s * ((1 - t) * PhysicalMixedTurnSource.lowerRunCoeff A B hh
          (PhysicalMixedTurnSource.familySource A B k i) +
        t * PhysicalMixedTurnSource.upperRunCoeff A B hh
          (PhysicalMixedTurnSource.familySource A B k i))) •
        PhysicalMixedTurnSource.developedForward A B hh k i +ᵥ
      (t • (PhysicalMixedTurnSource.developedUpper A B hh k i -
        PhysicalMixedTurnSource.developedLower A B hh k i) +ᵥ
          PhysicalMixedTurnSource.developedLower A B hh k i) by
        simp [vadd_eq_add]; abel]
  rw [T.map_vadd, T.map_vadd, map_smul, map_smul]
  rw [show T.linearIsometry (PhysicalMixedTurnSource.developedUpper A B hh k i -
        PhysicalMixedTurnSource.developedLower A B hh k i) =
      T (PhysicalMixedTurnSource.developedUpper A B hh k i) -
        T (PhysicalMixedTurnSource.developedLower A B hh k i) by
      exact T.map_vsub _ _,
    show T.linearIsometry (PhysicalMixedTurnSource.developedForward A B hh k i) =
      PhysicalMixedTurnSource.planeRotation
        (PhysicalMixedTurnSource.familyHeading A B hh 0 k.val)
          (PhysicalMixedTurnSource.developedForward A B hh k i) by
      have hvsub := PhysicalMixedTurnSource.baselineAlignment_heading_sub A B hh k
        (PhysicalMixedTurnSource.developedForward A B hh k i) 0
      have hvmap := T.map_vsub
        (PhysicalMixedTurnSource.developedForward A B hh k i) 0
      have hvmap' : T.linearIsometry
          (PhysicalMixedTurnSource.developedForward A B hh k i) =
          T (PhysicalMixedTurnSource.developedForward A B hh k i) - T 0 := by
        simpa only [vsub_eq_sub, sub_zero] using hvmap
      simpa only [sub_zero] using hvmap'.trans hvsub]
  simp only [vadd_eq_add]
  rw [hl, hu, hv, ← hs]
  module

/-- The root-zero developed seam at the selected index is exactly the selector's
original affine seam, not a seam at the baseline's zero index. -/
theorem selectedNegativeSeam_eq_baselinePoint
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    (t : ℝ) :
    RadialOriginalSeam.selectedNegativeSeamCurve A B hh hΔ t =
      (FixedBaselinePolarRayGeometry.baselineStrip A B hh).point
        (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ).val 0 t := by
  simp only [RadialOriginalSeam.selectedNegativeSeamCurve,
    RadialOriginalSeam.sourceUpper, RadialOriginalSeam.sourceHinge,
    GeneralTwoRimUnfolding.selectedNegativeCutIndex,
    RadialExtremalSafety.TriangularRadialStrip.point,
    FixedBaselinePolarRayGeometry.baselineStrip, zero_mul, zero_smul, add_zero]
  module

/-- At the selected physical root the actual entry seam is transported by one
explicit affine isometry to the selector's baseline seam. -/
theorem selectedNegativeRoot_seam_alignment
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    (t : ℝ) :
    PhysicalMixedTurnSource.baselineAlignment A B hh
        (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)
        ((rootStrip A B hh
          (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point 0 0 t) =
      RadialOriginalSeam.selectedNegativeSeamCurve A B hh hΔ t := by
  rw [rootStrip_alignment, Nat.add_zero]
  exact (selectedNegativeSeam_eq_baselinePoint A B hh hΔ t).symm

/-- The pole and the terminal seam travel through the same alignment and the
literal translated full circuit, including the wrapped final panel. -/
theorem selectedNegativeRoot_terminal_alignment
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    (t : ℝ) :
    PhysicalMixedTurnSource.baselineAlignment A B hh
        (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)
        (PhysicalMixedTurnSource.fullCircuit A B hh
          (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)
          ((rootStrip A B hh
            (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point 0 0 t)) =
      RadialOriginalSeam.selectedNegativeTerminalSeamCurve A B hh hΔ t := by
  rw [PhysicalMixedTurnSource.baselineAlignment_fullCircuit,
    selectedNegativeRoot_seam_alignment]
  rfl

/-- Explicit k-root affine placement of source material and its pole, with the
single real rotation offset on every (possibly wrapped) panel. -/
theorem selectedNegativeRoot_source_pole_and_angle
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    (i : ℕ)
    (x : FaceSpace A B h
      (cycle A B
        (PhysicalMixedTurnSource.familySource A B
          (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ) i))) :
    let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
    PhysicalMixedTurnSource.baselineAlignment A B hh k
        (PhysicalMixedTurnSource.directDevelopedMap A B hh k i x) =
      PhysicalMixedTurnSource.directDevelopedMap A B hh 0 (k.val + i)
        (PhysicalMixedTurnSource.baselineFacePoint A B k i x) ∧
    PhysicalMixedTurnSource.baselineAlignment A B hh k
        (PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_lt hΔ)) =
      PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ) ∧
    PhysicalMixedTurnSource.familyHeading A B hh 0 (k.val + i) =
      PhysicalMixedTurnSource.familyHeading A B hh 0 k.val +
        rootHeading A B hh k i := by
  dsimp
  exact ⟨PhysicalMixedTurnSource.baselineAlignment_directDevelopedMap A B hh _ i x,
    PhysicalMixedTurnSource.baselineAlignment_circuitPole A B hh _ (ne_of_lt hΔ),
    rootHeading_alignment A B hh _ i⟩

/-- The root-zero RF inequalities remain valid on the literal second sheet:
the full affine circuit fixes the pole and rotates both determinant arguments. -/
private theorem baseline_negative_RF_full_add
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    (j : ℕ) (hj : j < N A B + 1) :
    MixedTurnSafeCut.det
        (PhysicalMixedTurnSource.developedLower A B hh 0 (N A B + 1 + j) -
          PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
        (PhysicalMixedTurnSource.developedForward A B hh 0 (N A B + 1 + j)) < 0 ∧
    MixedTurnSafeCut.det
        (PhysicalMixedTurnSource.developedUpper A B hh 0 (N A B + 1 + j) -
          PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
        (PhysicalMixedTurnSource.developedForward A B hh 0 (N A B + 1 + j)) < 0 := by
  let O := PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)
  let H := PhysicalMixedTurnSource.fullCircuit A B hh 0
  let R := PhysicalMixedTurnSource.planeRotation
    (PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh))
  have hp : H O = O := PhysicalMixedTurnSource.circuitPole_fixed A B hh 0 (ne_of_lt hΔ)
  have hshift : PhysicalMixedTurnSource.developedForward A B hh 0 (N A B + 1 + j) =
      R (PhysicalMixedTurnSource.developedForward A B hh 0 j) := by
    rw [PhysicalMixedTurnSource.developedForward,
      PhysicalMixedTurnSource.developedForward,
      PhysicalMixedTurnSource.baseline_familyHeading_full_add,
      PhysicalMixedTurnSource.planeRotation_comp]
  have hdet (Y : Plane) : MixedTurnSafeCut.det (H Y - O)
      (R (PhysicalMixedTurnSource.developedForward A B hh 0 j)) =
      MixedTurnSafeCut.det (Y - O)
        (PhysicalMixedTurnSource.developedForward A B hh 0 j) := by
    have hv : H Y - O = R (Y - O) := by
      calc
        _ = H Y - H O := by rw [hp]
        _ = R (Y - O) := by
          rw [PhysicalMixedTurnSource.fullCircuit_apply,
            PhysicalMixedTurnSource.fullCircuit_apply, map_sub]
          abel
    rw [hv, PhysicalMixedTurnSource.planeRotation_det]
  have hk := PhysicalMixedTurnSource.baseline_physical_negative_RF A B hh hΔ
    (⟨j, hj⟩ : Fin (N A B + 1))
  constructor
  · rw [PhysicalMixedTurnSource.baseline_developedLower_fullCircuit, hshift]
    change MixedTurnSafeCut.det (H _ - O) (R _) < 0
    rw [hdet]
    exact hk.2
  · rw [PhysicalMixedTurnSource.baseline_developedUpper_fullCircuit, hshift]
    change MixedTurnSafeCut.det (H _ - O) (R _) < 0
    rw [hdet]
    exact hk.1

/-- Source-derived radial support at the selected physical root, including
panels whose baseline-aligned indices lie on the translated full-circuit sheet. -/
theorem selectedRoot_radialSupport
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0) :
    (rootStrip A B hh
      (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).RadialSupport
      (PhysicalMixedTurnSource.circuitPole A B hh
        (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ) (ne_of_lt hΔ)) := by
  let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
  intro i hi
  have hbase : MixedTurnSafeCut.det
        (PhysicalMixedTurnSource.developedLower A B hh 0 (k.val + i) -
          PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
        (PhysicalMixedTurnSource.developedForward A B hh 0 (k.val + i)) < 0 ∧
      MixedTurnSafeCut.det
        (PhysicalMixedTurnSource.developedUpper A B hh 0 (k.val + i) -
          PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
        (PhysicalMixedTurnSource.developedForward A B hh 0 (k.val + i)) < 0 := by
    by_cases hfirst : k.val + i < N A B + 1
    · have hk := PhysicalMixedTurnSource.baseline_physical_negative_RF A B hh hΔ
        (⟨k.val + i, hfirst⟩ : Fin (N A B + 1))
      exact ⟨hk.2, hk.1⟩
    · let j := k.val + i - (N A B + 1)
      have hj : j < N A B + 1 := by
        dsimp [j]
        have hk := k.isLt
        dsimp only [N] at hi hk ⊢
        omega
      have heq : k.val + i = N A B + 1 + j := by
        dsimp [j]
        omega
      rw [heq]
      exact baseline_negative_RF_full_add A B hh hΔ j hj
  have htransport (Y : Plane) : MixedTurnSafeCut.det
      (PhysicalMixedTurnSource.baselineAlignment A B hh k Y -
        PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
      (PhysicalMixedTurnSource.developedForward A B hh 0 (k.val + i)) =
      MixedTurnSafeCut.det
        (Y - PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_lt hΔ))
        (PhysicalMixedTurnSource.developedForward A B hh k i) := by
    rw [← PhysicalMixedTurnSource.baselineAlignment_circuitPole A B hh k (ne_of_lt hΔ),
      ← PhysicalMixedTurnSource.baselineAlignment_developedForward A B hh k i]
    exact PhysicalMixedTurnSource.baselineAlignment_det A B hh k _ _ _
  have hl := htransport (PhysicalMixedTurnSource.developedLower A B hh k i)
  have hu := htransport (PhysicalMixedTurnSource.developedUpper A B hh k i)
  rw [PhysicalMixedTurnSource.baselineAlignment_developedLower] at hl
  rw [PhysicalMixedTurnSource.baselineAlignment_developedUpper] at hu
  have hresult := And.intro (hl ▸ hbase.1) (hu ▸ hbase.2)
  simpa only [rootStrip, add_sub_cancel] using hresult

end
end SelectedNegativeRootPolar

#check SelectedNegativeRootPolar.selectedRoot_radialSupport
#print axioms SelectedNegativeRootPolar.selectedRoot_radialSupport
#check SelectedNegativeRootPolar.rootStrip_alignment
#print axioms SelectedNegativeRootPolar.rootStrip_alignment
#check SelectedNegativeRootPolar.selectedNegativeRoot_source_pole_and_angle
#print axioms SelectedNegativeRootPolar.selectedNegativeRoot_source_pole_and_angle
#check SelectedNegativeRootPolar.selectedNegativeRoot_terminal_alignment
#print axioms SelectedNegativeRootPolar.selectedNegativeRoot_terminal_alignment
