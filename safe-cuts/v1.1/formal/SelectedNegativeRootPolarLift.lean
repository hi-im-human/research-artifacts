import SelectedNegativeRootPolar
import FixedBaselinePolarTrace

open Set
open scoped BigOperators Classical NNReal Topology
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CommonSupportMerge OriginalFacetCertificates NormalFanSplice MaximalSupportCells
open CyclicCutOrders EuclideanPrismatoidCoordinates PolyhedralInputBridge
open TrimmedFacetWitnesses BandGeometryAssembly FiniteWitnessClosure SingleCutRecovery
open CutSurfaceQuotient MixedTurnSafeCut PolygonSetReconstruction ConvexPolygonTurning
open FixedBaselinePolarRayGeometry

namespace SelectedNegativeRootPolar
noncomputable section
set_option maxHeartbeats 8000000

variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

private abbrev M := N A B + 1
private abbrev Δ := PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh)

/-- The physical baseline strip on its second sheet is the actual affine full-circuit
image of the first sheet, not a quotient-angle identification. -/
theorem baselineStrip_point_full_add (j : ℕ) (s t : ℝ) :
    (baselineStrip A B hh).point (M A B + j) s t =
      PhysicalMixedTurnSource.fullCircuit A B hh 0
        ((baselineStrip A B hh).point j s t) := by
  let H := PhysicalMixedTurnSource.fullCircuit A B hh 0
  let R := PhysicalMixedTurnSource.planeRotation (Δ A B hh)
  have hv : PhysicalMixedTurnSource.developedForward A B hh 0 (M A B + j) =
      R (PhysicalMixedTurnSource.developedForward A B hh 0 j) := by
    rw [PhysicalMixedTurnSource.developedForward,
      PhysicalMixedTurnSource.developedForward,
      PhysicalMixedTurnSource.baseline_familyHeading_full_add,
      PhysicalMixedTurnSource.planeRotation_comp]
  have hlinear (v : Plane) : H.linearIsometry v = R v := by
    have hvsub := H.map_vsub v 0
    have hrot := PhysicalMixedTurnSource.fullCircuit_apply A B hh 0 v
    have hrot0 := PhysicalMixedTurnSource.fullCircuit_apply A B hh 0 0
    simpa only [vsub_eq_sub, sub_zero, map_zero, smul_zero, add_zero, R, Δ] using
      (show H.linearIsometry v = H v - H 0 from by simpa using hvsub).trans
        (by rw [hrot, hrot0]; simp)
  change PhysicalMixedTurnSource.developedLower A B hh 0 (M A B + j) +
      t • (PhysicalMixedTurnSource.developedUpper A B hh 0 (M A B + j) -
        PhysicalMixedTurnSource.developedLower A B hh 0 (M A B + j)) +
      (s * ((1 - t) * PhysicalMixedTurnSource.lowerRunCoeff A B hh
        (PhysicalMixedTurnSource.familySource A B 0 (M A B + j)) +
        t * PhysicalMixedTurnSource.upperRunCoeff A B hh
        (PhysicalMixedTurnSource.familySource A B 0 (M A B + j)))) •
        PhysicalMixedTurnSource.developedForward A B hh 0 (M A B + j) = _
  rw [PhysicalMixedTurnSource.baseline_developedLower_fullCircuit,
    PhysicalMixedTurnSource.baseline_developedUpper_fullCircuit,
    PhysicalMixedTurnSource.baseline_familySource_full_add, hv]
  have hsub (x y : Plane) : H x - H y = R (x - y) := by
    simpa only [vsub_eq_sub, hlinear] using (H.map_vsub x y).symm
  rw [hsub]
  change H _ + t • R _ + _ • R _ =
    H (PhysicalMixedTurnSource.developedLower A B hh 0 j +
      t • (PhysicalMixedTurnSource.developedUpper A B hh 0 j -
        PhysicalMixedTurnSource.developedLower A B hh 0 j) +
      (s * ((1 - t) * PhysicalMixedTurnSource.lowerRunCoeff A B hh
        (PhysicalMixedTurnSource.familySource A B 0 j) +
        t * PhysicalMixedTurnSource.upperRunCoeff A B hh
        (PhysicalMixedTurnSource.familySource A B 0 j))) •
          PhysicalMixedTurnSource.developedForward A B hh 0 j)
  rw [show PhysicalMixedTurnSource.developedLower A B hh 0 j +
      t • (PhysicalMixedTurnSource.developedUpper A B hh 0 j -
        PhysicalMixedTurnSource.developedLower A B hh 0 j) +
      (s * ((1 - t) * PhysicalMixedTurnSource.lowerRunCoeff A B hh
        (PhysicalMixedTurnSource.familySource A B 0 j) +
        t * PhysicalMixedTurnSource.upperRunCoeff A B hh
        (PhysicalMixedTurnSource.familySource A B 0 j))) •
          PhysicalMixedTurnSource.developedForward A B hh 0 j =
      (s * ((1 - t) * PhysicalMixedTurnSource.lowerRunCoeff A B hh
        (PhysicalMixedTurnSource.familySource A B 0 j) +
        t * PhysicalMixedTurnSource.upperRunCoeff A B hh
        (PhysicalMixedTurnSource.familySource A B 0 j))) •
          PhysicalMixedTurnSource.developedForward A B hh 0 j +ᵥ
      (t • (PhysicalMixedTurnSource.developedUpper A B hh 0 j -
        PhysicalMixedTurnSource.developedLower A B hh 0 j) +ᵥ
        PhysicalMixedTurnSource.developedLower A B hh 0 j) by
          simp only [vadd_eq_add]; abel]
  rw [H.map_vadd, H.map_vadd, map_smul, map_smul, hlinear, hlinear]
  simp only [vadd_eq_add]
  abel

/-- The panel-local complex coordinate is invariant under simultaneous rotation
of the point and its real heading. -/
theorem panelRelativeComplex_rotate (θ φ : ℝ) (z : Plane) :
    panelRelativeComplex (θ + φ)
      (PhysicalMixedTurnSource.planeRotation θ z) =
        panelRelativeComplex φ z := by
  apply Complex.ext
  · simp [panelRelativeComplex, PhysicalMixedTurnSource.planeRotation,
      PhysicalMixedTurnSource.planeRotationLinear, Real.cos_add, Real.sin_add]
    linear_combination (Real.cos φ * z 0 + Real.sin φ * z 1) *
      (Real.sin_sq_add_cos_sq θ)
  · simp [panelRelativeComplex, PhysicalMixedTurnSource.planeRotation,
      PhysicalMixedTurnSource.planeRotationLinear, Real.cos_add, Real.sin_add]
    linear_combination (-Real.sin φ * z 0 + Real.cos φ * z 1) *
      (Real.sin_sq_add_cos_sq θ)

/-- The baseline polar expression extended onto the literal translated sheet. -/
noncomputable def extendedBaselineLift
    (hΔ : Δ A B hh < 0) (j : ℕ) (s t : ℝ) : ℝ :=
  if hj : j < M A B then
    panelPointPolarLift A B hh hΔ j s t
  else
    Δ A B hh + panelPointPolarLift A B hh hΔ (j - M A B) s t

/-- At the selected root, the local real polar lift is obtained from the
source-computed panel heading and a strict upper-half-plane argument. -/
noncomputable def selectedPointPolarLift
    (hΔ : Δ A B hh < 0) (i : ℕ) (s t : ℝ) : ℝ :=
  let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
  rootHeading A B hh k i + Complex.arg
    (panelRelativeComplex (rootHeading A B hh k i)
      ((rootStrip A B hh k).point i s t -
        PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_lt hΔ)))

/-- The sheet formula equals the intrinsic selected-root polar expression,
including panels crossing the translated full circuit. -/
theorem selectedPointPolarLift_eq_extended
    (hΔ : Δ A B hh < 0) (i : ℕ) (hi : i ≤ N A B) (s t : ℝ) :
    selectedPointPolarLift A B hh hΔ i s t =
      extendedBaselineLift A B hh hΔ
        ((GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ).val + i) s t -
        panelAngleLift A B hh
          (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ).val := by
  let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
  let θ := panelAngleLift A B hh k.val
  let j := k.val + i
  have hheading := rootHeading_alignment A B hh k i
  have hpoint := rootStrip_alignment A B hh k i s t
  have hpole := PhysicalMixedTurnSource.baselineAlignment_circuitPole
    A B hh k (ne_of_lt hΔ)
  have hz : PhysicalMixedTurnSource.planeRotation θ
      ((rootStrip A B hh k).point i s t -
        PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_lt hΔ)) =
      (baselineStrip A B hh).point j s t -
        PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ) := by
    change PhysicalMixedTurnSource.planeRotation
      (PhysicalMixedTurnSource.familyHeading A B hh 0 k.val) _ = _
    rw [← PhysicalMixedTurnSource.baselineAlignment_heading_sub A B hh k,
      hpoint, hpole]
  have hrel : panelRelativeComplex (rootHeading A B hh k i)
      ((rootStrip A B hh k).point i s t -
        PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_lt hΔ)) =
      panelRelativeComplex (panelAngleLift A B hh j)
      ((baselineStrip A B hh).point j s t -
        PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)) := by
    rw [← hz, show panelAngleLift A B hh j = θ + rootHeading A B hh k i
      from hheading, panelRelativeComplex_rotate]
  have hbase : extendedBaselineLift A B hh hΔ j s t =
      panelAngleLift A B hh j + Complex.arg
        (panelRelativeComplex (panelAngleLift A B hh j)
          ((baselineStrip A B hh).point j s t -
            PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))) := by
    by_cases hj : j < M A B
    · simp [extendedBaselineLift, hj, panelPointPolarLift]
    · have hlt : j - M A B < M A B := by
        have hk := k.isLt
        change i ≤ PhysicalMixedTurnSource.MechanismN A B at hi
        change k.val + i - (PhysicalMixedTurnSource.MechanismN A B + 1) <
          PhysicalMixedTurnSource.MechanismN A B + 1
        omega
      have heq : j = M A B + (j - M A B) := by omega
      have hheading' := PhysicalMixedTurnSource.baseline_familyHeading_full_add
        A B hh (j - M A B)
      have hpoint' := baselineStrip_point_full_add A B hh (j - M A B) s t
      have hz' : (baselineStrip A B hh).point j s t -
          PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ) =
        PhysicalMixedTurnSource.planeRotation (Δ A B hh)
          ((baselineStrip A B hh).point (j - M A B) s t -
            PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)) := by
        calc
          _ = PhysicalMixedTurnSource.fullCircuit A B hh 0
              ((baselineStrip A B hh).point (j - M A B) s t) -
              PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ) := by
                conv_lhs => rw [heq, hpoint']
          _ = _ := by
            simpa only [M, Nat.add_sub_cancel_left, Δ] using
              fullCircuit_sub_pole A B hh (ne_of_lt hΔ)
                ((baselineStrip A B hh).point (j - M A B) s t)
      have hangle : panelAngleLift A B hh j =
          Δ A B hh + panelAngleLift A B hh (j - M A B) := by
        calc
          _ = panelAngleLift A B hh (M A B + (j - M A B)) := by rw [← heq]
          _ = Δ A B hh + panelAngleLift A B hh (j - M A B) := by
            simpa only [panelAngleLift, M, Δ] using hheading'
      have hrel' : panelRelativeComplex (panelAngleLift A B hh j)
          ((baselineStrip A B hh).point j s t -
            PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)) =
          panelRelativeComplex (panelAngleLift A B hh (j - M A B))
            ((baselineStrip A B hh).point (j - M A B) s t -
              PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)) := by
        rw [hangle, hz', panelRelativeComplex_rotate]
      simp only [extendedBaselineLift, dif_neg hj, panelPointPolarLift]
      rw [← hrel', hangle]
      ring
  unfold selectedPointPolarLift
  dsimp only
  rw [hrel, hbase]
  have hh' : panelAngleLift A B hh j = θ + rootHeading A B hh k i := hheading
  rw [hh']
  ring

/-- The selected-root panel direction is exactly its compatible real heading. -/
theorem rootForward_eq_direction (k : Fin (M A B)) (i : ℕ) :
    PhysicalMixedTurnSource.developedForward A B hh k i =
      MixedTurnSafeCut.direction (rootHeading A B hh k i) := by
  rw [PhysicalMixedTurnSource.developedForward, rootHeading,
    PhysicalMixedTurnSource.planeRotation_direction]
  simp

/-- A genuine positive-radius polar decomposition of every selected-root
material point, including the wrapped physical panels and boundary heights. -/
theorem selectedPointPolarLift_decomposition
    (hΔ : Δ A B hh < 0) {i : ℕ} (hi : i ≤ N A B)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
    let z := (rootStrip A B hh k).point i s t -
      PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_lt hΔ)
    z = ‖z‖ • MixedTurnSafeCut.direction
      (selectedPointPolarLift A B hh hΔ i s t) ∧ 0 < ‖z‖ := by
  let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
  let j := k.val + i
  let x := (rootStrip A B hh k).point i s t
  let O := PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_lt hΔ)
  let y := (baselineStrip A B hh).point j s t
  let P := PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)
  let θ := panelAngleLift A B hh k.val
  have hpos : 0 < ‖x - O‖ := norm_pos_iff.mpr (sub_ne_zero.mpr
    (RadialExtremalSafety.TriangularRadialStrip.point_ne_pole
      (selectedRoot_radialSupport A B hh hΔ) hi hs ht))
  have htrans : PhysicalMixedTurnSource.planeRotation θ (x - O) = y - P := by
    change PhysicalMixedTurnSource.planeRotation
      (PhysicalMixedTurnSource.familyHeading A B hh 0 k.val) _ = _
    rw [← PhysicalMixedTurnSource.baselineAlignment_heading_sub A B hh k,
      rootStrip_alignment, PhysicalMixedTurnSource.baselineAlignment_circuitPole]
  have hjbound : j < 2 * M A B := by
    have hk := k.isLt
    change i ≤ PhysicalMixedTurnSource.MechanismN A B at hi
    change k.val + i < 2 * (PhysicalMixedTurnSource.MechanismN A B + 1)
    omega
  have hbase : y - P = ‖y - P‖ • MixedTurnSafeCut.direction
      (extendedBaselineLift A B hh hΔ j s t) := by
    by_cases hj : j < M A B
    · have hj' : j ≤ N A B := by
        change j ≤ PhysicalMixedTurnSource.MechanismN A B
        change j < PhysicalMixedTurnSource.MechanismN A B + 1 at hj
        omega
      simpa only [extendedBaselineLift, dif_pos hj] using
        panelPointPolarLift_decomposition A B hh hΔ hj' hs ht
    · have hj' : j - M A B ≤ N A B := by
        change j - (PhysicalMixedTurnSource.MechanismN A B + 1) ≤
          PhysicalMixedTurnSource.MechanismN A B
        change j < 2 * (PhysicalMixedTurnSource.MechanismN A B + 1) at hjbound
        omega
      let u := (baselineStrip A B hh).point (j - M A B) s t
      have hd := panelPointPolarLift_decomposition A B hh hΔ hj' hs ht
      change u - P = ‖u - P‖ • MixedTurnSafeCut.direction
        (panelPointPolarLift A B hh hΔ (j - M A B) s t) at hd
      have heq : j = M A B + (j - M A B) := by omega
      have hcopy : y - P = PhysicalMixedTurnSource.planeRotation (Δ A B hh)
          (u - P) := by
        change (baselineStrip A B hh).point j s t - P = _
        conv_lhs => rw [heq, baselineStrip_point_full_add]
        exact fullCircuit_sub_pole A B hh (ne_of_lt hΔ) u
      have hnorm : ‖y - P‖ = ‖u - P‖ := by
        rw [hcopy]
        exact (PhysicalMixedTurnSource.planeRotation _).norm_map _
      calc
        y - P = PhysicalMixedTurnSource.planeRotation (Δ A B hh) (u - P) := hcopy
        _ = ‖u - P‖ • MixedTurnSafeCut.direction
            (Δ A B hh + panelPointPolarLift A B hh hΔ (j - M A B) s t) := by
              conv_lhs => rw [hd, map_smul,
                PhysicalMixedTurnSource.planeRotation_direction]
        _ = ‖y - P‖ • MixedTurnSafeCut.direction
            (extendedBaselineLift A B hh hΔ j s t) := by
              rw [hnorm]
              simp only [extendedBaselineLift, dif_neg hj]
  have hnorm : ‖y - P‖ = ‖x - O‖ := by
    rw [← htrans]
    exact (PhysicalMixedTurnSource.planeRotation _).norm_map _
  have hangle : extendedBaselineLift A B hh hΔ j s t =
      θ + selectedPointPolarLift A B hh hΔ i s t := by
    rw [selectedPointPolarLift_eq_extended A B hh hΔ i hi s t]
    ring
  constructor
  · have hb : PhysicalMixedTurnSource.planeRotation θ (x - O) =
        ‖x - O‖ • MixedTurnSafeCut.direction
          (θ + selectedPointPolarLift A B hh hΔ i s t) := by
        rw [htrans, hbase, hnorm, hangle]
    have hrot := congrArg (PhysicalMixedTurnSource.planeRotation (-θ)) hb
    rw [map_smul, PhysicalMixedTurnSource.planeRotation_direction] at hrot
    have hinv : PhysicalMixedTurnSource.planeRotation (-θ)
        (PhysicalMixedTurnSource.planeRotation θ (x - O)) = x - O := by
      rw [PhysicalMixedTurnSource.planeRotation_comp]
      simp only [neg_add_cancel, PhysicalMixedTurnSource.planeRotation_zero_angle]
    rw [hinv] at hrot
    have hsimp : -θ + (θ + selectedPointPolarLift A B hh hΔ i s t) =
        selectedPointPolarLift A B hh hΔ i s t := by ring
    simpa only [hsimp] using hrot
  · exact hpos

/-- Strictly clockwise material ordering, including the actual wrapped panels. -/
theorem selectedPointPolarLift_strictAnti
    (hΔ : Δ A B hh < 0) {i : ℕ} (hi : i ≤ N A B)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    StrictAntiOn (fun s => selectedPointPolarLift A B hh hΔ i s t)
      (Icc (0 : ℝ) 1) := by
  let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
  let j := k.val + i
  intro s₁ hs₁ s₂ hs₂ hslt
  change selectedPointPolarLift A B hh hΔ i s₂ t <
    selectedPointPolarLift A B hh hΔ i s₁ t
  rw [selectedPointPolarLift_eq_extended A B hh hΔ i hi s₁ t,
    selectedPointPolarLift_eq_extended A B hh hΔ i hi s₂ t]
  change extendedBaselineLift A B hh hΔ j s₂ t - _ <
    extendedBaselineLift A B hh hΔ j s₁ t - _
  by_cases hj : j < M A B
  · have hj' : j ≤ N A B := by
      change j ≤ PhysicalMixedTurnSource.MechanismN A B
      change j < PhysicalMixedTurnSource.MechanismN A B + 1 at hj
      omega
    simp only [extendedBaselineLift, dif_pos hj]
    have h := (panelPointPolarLift_strictAnti A B hh hΔ hj' ht)
      hs₁ hs₂ hslt
    linarith
  · have hj' : j - M A B ≤ N A B := by
      have hk := k.isLt
      change i ≤ PhysicalMixedTurnSource.MechanismN A B at hi
      change j - (PhysicalMixedTurnSource.MechanismN A B + 1) ≤
        PhysicalMixedTurnSource.MechanismN A B
      dsimp only [j]
      omega
    simp only [extendedBaselineLift, dif_neg hj]
    have h := (panelPointPolarLift_strictAnti A B hh hΔ hj' ht)
      hs₁ hs₂ hslt
    linarith

/-- Every selected physical panel fills its entire real endpoint interval. -/
theorem selectedPointPolarLift_image_Icc
    (hΔ : Δ A B hh < 0) {i : ℕ} (hi : i ≤ N A B)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (fun s => selectedPointPolarLift A B hh hΔ i s t) '' Icc (0 : ℝ) 1 =
      Icc (selectedPointPolarLift A B hh hΔ i 1 t)
        (selectedPointPolarLift A B hh hΔ i 0 t) := by
  let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
  let j := k.val + i
  have hjbound : j < 2 * M A B := by
    have hk := k.isLt
    change i ≤ PhysicalMixedTurnSource.MechanismN A B at hi
    change k.val + i < 2 * (PhysicalMixedTurnSource.MechanismN A B + 1)
    omega
  have himage : (fun s => extendedBaselineLift A B hh hΔ j s t) '' Icc (0 : ℝ) 1 =
      Icc (extendedBaselineLift A B hh hΔ j 1 t)
        (extendedBaselineLift A B hh hΔ j 0 t) := by
    by_cases hj : j < M A B
    · have hj' : j ≤ N A B := by
        change j ≤ PhysicalMixedTurnSource.MechanismN A B
        change j < PhysicalMixedTurnSource.MechanismN A B + 1 at hj
        omega
      simp only [extendedBaselineLift, dif_pos hj]
      exact panelPointPolarLift_image_Icc A B hh hΔ hj' ht
    · have hj' : j - M A B ≤ N A B := by
        change j - (PhysicalMixedTurnSource.MechanismN A B + 1) ≤
          PhysicalMixedTurnSource.MechanismN A B
        change j < 2 * (PhysicalMixedTurnSource.MechanismN A B + 1) at hjbound
        omega
      simp only [extendedBaselineLift, dif_neg hj]
      have him := panelPointPolarLift_image_Icc A B hh hΔ hj' ht
      ext φ
      constructor
      · rintro ⟨s, hs, rfl⟩
        have hm : panelPointPolarLift A B hh hΔ (j - M A B) s t ∈
            Icc (panelPointPolarLift A B hh hΔ (j - M A B) 1 t)
              (panelPointPolarLift A B hh hΔ (j - M A B) 0 t) := by
          rw [← him]; exact ⟨s, hs, rfl⟩
        exact ⟨by linarith [hm.1], by linarith [hm.2]⟩
      · intro hφ
        have hm : φ - Δ A B hh ∈
            Icc (panelPointPolarLift A B hh hΔ (j - M A B) 1 t)
              (panelPointPolarLift A B hh hΔ (j - M A B) 0 t) := by
          exact ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
        rw [← him] at hm
        obtain ⟨s, hs, he⟩ := hm
        exact ⟨s, hs, by linarith⟩
  ext φ
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hm : extendedBaselineLift A B hh hΔ j s t ∈
        Icc (extendedBaselineLift A B hh hΔ j 1 t)
          (extendedBaselineLift A B hh hΔ j 0 t) := by
      rw [← himage]; exact ⟨s, hs, rfl⟩
    change selectedPointPolarLift A B hh hΔ i s t ∈ _
    rw [selectedPointPolarLift_eq_extended A B hh hΔ i hi s t,
      selectedPointPolarLift_eq_extended A B hh hΔ i hi 1 t,
      selectedPointPolarLift_eq_extended A B hh hΔ i hi 0 t]
    exact ⟨by linarith [hm.1], by linarith [hm.2]⟩
  · intro hφ
    rw [selectedPointPolarLift_eq_extended A B hh hΔ i hi 1 t,
      selectedPointPolarLift_eq_extended A B hh hΔ i hi 0 t] at hφ
    have hm : φ + panelAngleLift A B hh k.val ∈
        Icc (extendedBaselineLift A B hh hΔ j 1 t)
          (extendedBaselineLift A B hh hΔ j 0 t) := by
      exact ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
    rw [← himage] at hm
    obtain ⟨s, hs, he⟩ := hm
    refine ⟨s, hs, ?_⟩
    change selectedPointPolarLift A B hh hΔ i s t = φ
    rw [selectedPointPolarLift_eq_extended A B hh hΔ i hi s t]
    linarith

/-- Consecutive real lifts meet at each retained physical hinge; the single
crossing between sheets uses the exact real terminal-sweep identity. -/
theorem selectedPointPolarLift_hinge
    (hΔ : Δ A B hh < 0) {i : ℕ} (hi : i < N A B)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    selectedPointPolarLift A B hh hΔ i 1 t =
      selectedPointPolarLift A B hh hΔ (i + 1) 0 t := by
  let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
  let j := k.val + i
  have hi₁ : i ≤ N A B := Nat.le_of_lt hi
  have hi₂ : i + 1 ≤ N A B := hi
  rw [selectedPointPolarLift_eq_extended A B hh hΔ i hi₁ 1 t,
    selectedPointPolarLift_eq_extended A B hh hΔ (i + 1) hi₂ 0 t]
  have hnext : k.val + (i + 1) = j + 1 := by dsimp [j]; omega
  rw [hnext]
  suffices extendedBaselineLift A B hh hΔ j 1 t =
      extendedBaselineLift A B hh hΔ (j + 1) 0 t by linarith
  have hjbound : j + 1 < 2 * M A B := by
    have hk := k.isLt
    change i < PhysicalMixedTurnSource.MechanismN A B at hi
    change k.val + i + 1 < 2 * (PhysicalMixedTurnSource.MechanismN A B + 1)
    omega
  by_cases hfirst : j + 1 < M A B
  · have hj : j < M A B := by omega
    have hji : j < N A B := by
      change j < PhysicalMixedTurnSource.MechanismN A B
      change j + 1 < PhysicalMixedTurnSource.MechanismN A B + 1 at hfirst
      omega
    simp only [extendedBaselineLift, dif_pos hj, dif_pos hfirst]
    exact panelPointPolarLift_hinge A B hh hΔ hji ht
  · by_cases hboundary : j + 1 = M A B
    · have hj : j < M A B := by omega
      have hjN : j = N A B := by
        change j = PhysicalMixedTurnSource.MechanismN A B
        change j + 1 = PhysicalMixedTurnSource.MechanismN A B + 1 at hboundary
        omega
      have hnot : ¬ j + 1 < M A B := by omega
      simp only [extendedBaselineLift, dif_pos hj, dif_neg hnot]
      rw [hjN, show N A B + 1 - M A B = 0 by
        change PhysicalMixedTurnSource.MechanismN A B + 1 -
          (PhysicalMixedTurnSource.MechanismN A B + 1) = 0
        omega]
      simpa only [longitudinalAlpha, N, Δ, add_comm] using
        panelPointPolarLift_terminal_eq_alpha_add_delta A B hh hΔ ht
    · have hj : ¬ j < M A B := by omega
      have hjnext : ¬ j + 1 < M A B := by omega
      have hji : j - M A B < N A B := by
        change j - (PhysicalMixedTurnSource.MechanismN A B + 1) <
          PhysicalMixedTurnSource.MechanismN A B
        change i < PhysicalMixedTurnSource.MechanismN A B at hi
        change j + 1 < 2 * (PhysicalMixedTurnSource.MechanismN A B + 1) at hjbound
        omega
      simp only [extendedBaselineLift, dif_neg hj, dif_neg hjnext]
      have heq : j + 1 - M A B = j - M A B + 1 := by omega
      rw [heq, panelPointPolarLift_hinge A B hh hΔ hji ht]

/-- Every actual retained hinge identifies the same developed material point
on both neighboring panels, including those on the wrapped sheet. -/
theorem selectedRoot_retainedHinge_point
    (hΔ : Δ A B hh < 0) {i : ℕ} (hi : i < N A B) (t : ℝ) :
    let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
    (rootStrip A B hh k).point i 1 t =
      (rootStrip A B hh k).point (i + 1) 0 t := by
  let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
  let S := rootStrip A B hh k
  change S.point i 1 t = S.point (i + 1) 0 t
  simp only [RadialExtremalSafety.TriangularRadialStrip.point]
  rw [S.lower_step i hi, S.hinge_step i hi]
  simp only [zero_mul, zero_smul, add_zero, one_mul]
  module

/-- Every selected material point lies in the strict local polar window
associated with its compatible physical heading. -/
theorem selectedPointPolarLift_mem_window
    (hΔ : Δ A B hh < 0) {i : ℕ} (hi : i ≤ N A B)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
    rootHeading A B hh k i < selectedPointPolarLift A B hh hΔ i s t ∧
      selectedPointPolarLift A B hh hΔ i s t <
        rootHeading A B hh k i + Real.pi := by
  let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
  let S := rootStrip A B hh k
  let O := PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_lt hΔ)
  let z := S.point i s t - O
  let θ := rootHeading A B hh k i
  let w := panelRelativeComplex θ z
  have hsupport := RadialExtremalSafety.TriangularRadialStrip.support_point
    (selectedRoot_radialSupport A B hh hΔ) hi hs ht
  have him : 0 < w.im := by
    rw [show w.im = MixedTurnSafeCut.det (MixedTurnSafeCut.direction θ) z by
      simp [w, panelRelativeComplex_im]]
    rw [← rootForward_eq_direction A B hh k i]
    change MixedTurnSafeCut.det z (S.v i) < 0 at hsupport
    have hanti : MixedTurnSafeCut.det (S.v i) z =
        -MixedTurnSafeCut.det z (S.v i) := by
      simp [MixedTurnSafeCut.det]; ring
    change 0 < MixedTurnSafeCut.det (S.v i) z
    rw [hanti]
    exact neg_pos.mpr hsupport
  have harg0 : 0 < Complex.arg w := by
    have hnonneg : 0 ≤ Complex.arg w := Complex.arg_nonneg_iff.2 him.le
    exact lt_of_le_of_ne hnonneg (by
      intro he
      have hz := Complex.arg_eq_zero_iff.mp he.symm
      linarith [hz.2])
  have hargpi : Complex.arg w < Real.pi :=
    Complex.arg_lt_pi_iff.2 (Or.inr (ne_of_gt him))
  simpa only [selectedPointPolarLift, k, S, O, z, θ, w] using
    (show θ < θ + Complex.arg w ∧
      θ + Complex.arg w < θ + Real.pi from ⟨by linarith, by linarith⟩)

/-- The virtual final hinge is the literal translated copy of the selected
entry seam, pointwise in physical height (not merely angularly equivalent). -/
theorem selectedRoot_virtualFinalHinge
    (hΔ : Δ A B hh < 0) (t : ℝ) :
    let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
    (rootStrip A B hh k).point (N A B) 1 t =
      PhysicalMixedTurnSource.fullCircuit A B hh k
        ((rootStrip A B hh k).point 0 0 t) := by
  let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
  let T := PhysicalMixedTurnSource.baselineAlignment A B hh k
  apply T.injective
  rw [rootStrip_alignment, PhysicalMixedTurnSource.baselineAlignment_fullCircuit,
    rootStrip_alignment]
  have hjoin : (baselineStrip A B hh).point (k.val + N A B) 1 t =
      (baselineStrip A B hh).point (k.val + N A B + 1) 0 t := by
    rw [baselineStrip_point_one, retainedHinge_eq_next_entry,
      baselineStrip_point_zero]
  rw [hjoin, show k.val + N A B + 1 = M A B + k.val by
    change k.val + PhysicalMixedTurnSource.MechanismN A B + 1 =
      PhysicalMixedTurnSource.MechanismN A B + 1 + k.val
    omega, baselineStrip_point_full_add]
  simp

/-- The full affine circuit acts on the selected seam by exactly the real
intrinsic sweep, not just by a quotient-angle rotation. -/
theorem selectedPointPolarLift_terminal
    (hΔ : Δ A B hh < 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    selectedPointPolarLift A B hh hΔ (N A B) 1 t =
      selectedPointPolarLift A B hh hΔ 0 0 t + Δ A B hh := by
  let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
  have hk : k.val < M A B := k.isLt
  have hterminal : k.val + N A B =
      N A B + k.val := by omega
  rw [selectedPointPolarLift_eq_extended A B hh hΔ (N A B) (le_refl _) 1 t,
    selectedPointPolarLift_eq_extended A B hh hΔ 0 (Nat.zero_le _) 0 t]
  simp only [Nat.add_zero]
  change extendedBaselineLift A B hh hΔ (k.val + N A B) 1 t -
      panelAngleLift A B hh k.val =
    extendedBaselineLift A B hh hΔ k.val 0 t -
      panelAngleLift A B hh k.val + Δ A B hh
  by_cases hz : k.val = 0
  · have hlast : k.val + N A B = N A B := by omega
    have hfirst : k.val < M A B := hk
    have hlast' : k.val + N A B < M A B := by
      rw [hlast]; change PhysicalMixedTurnSource.MechanismN A B <
        PhysicalMixedTurnSource.MechanismN A B + 1; omega
    rw [show k.val + N A B = N A B by omega, hz]
    simp only [extendedBaselineLift,
      dif_pos (show N A B < M A B by
        change PhysicalMixedTurnSource.MechanismN A B <
          PhysicalMixedTurnSource.MechanismN A B + 1; omega),
      dif_pos (show 0 < M A B by
        change 0 < PhysicalMixedTurnSource.MechanismN A B + 1; omega),
      panelAngleLift_zero]
    simpa only [longitudinalAlpha, N, Δ, add_comm, sub_zero] using
      panelPointPolarLift_terminal_eq_alpha_add_delta A B hh hΔ ht
  · have hnot : ¬ k.val + N A B < M A B := by
      change ¬ k.val + PhysicalMixedTurnSource.MechanismN A B <
        PhysicalMixedTurnSource.MechanismN A B + 1
      omega
    have hfirst : k.val < M A B := hk
    simp only [extendedBaselineLift, dif_neg hnot, dif_pos hfirst]
    have hindex : k.val + N A B - M A B + 1 = k.val := by
      change k.val + PhysicalMixedTurnSource.MechanismN A B -
        (PhysicalMixedTurnSource.MechanismN A B + 1) + 1 = k.val
      omega
    have hprev : k.val + N A B - M A B < N A B := by
      change k.val + PhysicalMixedTurnSource.MechanismN A B -
        (PhysicalMixedTurnSource.MechanismN A B + 1) <
        PhysicalMixedTurnSource.MechanismN A B
      omega
    have hhinge := panelPointPolarLift_hinge A B hh hΔ hprev ht
    rw [hindex] at hhinge
    linarith

/-- The exact set of real polar angles occupied at height `t` by every
selected-root physical panel. -/
def selectedLongitudinalLiftSet (hΔ : Δ A B hh < 0) (t : ℝ) : Set ℝ :=
  {φ | ∃ i ≤ N A B, ∃ s ∈ Icc (0 : ℝ) 1,
    φ = selectedPointPolarLift A B hh hΔ i s t}

/-- The selected seam's actual real polar representative. -/
def selectedAlpha (hΔ : Δ A B hh < 0) (t : ℝ) : ℝ :=
  selectedPointPolarLift A B hh hΔ 0 0 t

/-- The selected physical strip realizes exactly the full real angular interval
from its terminal seam to its entry seam, with no quotient-angle weakening. -/
theorem selectedLongitudinalLiftSet_eq_Icc
    (hΔ : Δ A B hh < 0) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    selectedLongitudinalLiftSet A B hh hΔ t =
      Icc (selectedAlpha A B hh hΔ t + Δ A B hh)
        (selectedAlpha A B hh hΔ t) := by
  let lo : ℕ → ℝ := fun i => selectedPointPolarLift A B hh hΔ i 1 t
  let hi : ℕ → ℝ := fun i => selectedPointPolarLift A B hh hΔ i 0 t
  have horder : ∀ i ≤ N A B, lo i ≤ hi i := by
    intro i hiN
    exact (selectedPointPolarLift_strictAnti A B hh hΔ hiN ht).antitoneOn
      (by norm_num) (by norm_num) (by norm_num)
  have hchain : ∀ i < N A B, hi (i + 1) = lo i := by
    intro i hiN
    exact (selectedPointPolarLift_hinge A B hh hΔ hiN
      ⟨ht.1.le, ht.2.le⟩).symm
  have hterminal := selectedPointPolarLift_terminal A B hh hΔ
    ⟨ht.1.le, ht.2.le⟩
  change lo (N A B) = hi 0 + Δ A B hh at hterminal
  rw [show selectedAlpha A B hh hΔ t = hi 0 from rfl,
    ← hterminal]
  ext φ
  constructor
  · rintro ⟨i, hiN, s, hs, rfl⟩
    have hlocal : selectedPointPolarLift A B hh hΔ i s t ∈
        Icc (lo i) (hi i) := by
      rw [← selectedPointPolarLift_image_Icc A B hh hΔ hiN ht]
      exact ⟨s, hs, rfl⟩
    exact Icc_subset_Icc_of_chain horder hchain hiN hlocal
  · intro hφ
    obtain ⟨i, hiN, hlocal⟩ := exists_mem_Icc_of_chain horder hchain hφ
    rw [← selectedPointPolarLift_image_Icc A B hh hΔ hiN ht] at hlocal
    obtain ⟨s, hs, rfl⟩ := hlocal
    exact ⟨i, hiN, s, hs, rfl⟩

/-- The actual interior-height component for a chosen real representative of a
physical ray. Membership is a material point of the selected-root strip, not a
closed-window witness stipulated independently of the development. -/
def selectedRayHeightComponent (hΔ : Δ A B hh < 0) (β : ℝ) (m : ℤ) : Set ℝ :=
  {t | t ∈ Ioo (0 : ℝ) 1 ∧
    ∃ i ≤ N A B, ∃ s ∈ Icc (0 : ℝ) 1,
      selectedPointPolarLift A B hh hΔ i s t = β + 2 * Real.pi * (m : ℝ)}

/-- Exact eligible-height inequalities for the *realized* physical material
strip. Both implications use the full fixed-height image theorem. -/
theorem selectedRayHeightComponent_iff
    (hΔ : Δ A B hh < 0) (β : ℝ) (m : ℤ) (t : ℝ) :
    t ∈ selectedRayHeightComponent A B hh hΔ β m ↔
      t ∈ Ioo (0 : ℝ) 1 ∧
        selectedAlpha A B hh hΔ t + Δ A B hh ≤
          β + 2 * Real.pi * (m : ℝ) ∧
        β + 2 * Real.pi * (m : ℝ) ≤ selectedAlpha A B hh hΔ t := by
  constructor
  · rintro ⟨ht, i, hi, s, hs, he⟩
    have hw : β + 2 * Real.pi * (m : ℝ) ∈
        selectedLongitudinalLiftSet A B hh hΔ t := ⟨i, hi, s, hs, he.symm⟩
    rw [selectedLongitudinalLiftSet_eq_Icc A B hh hΔ ht] at hw
    exact ⟨ht, hw.1, hw.2⟩
  · rintro ⟨ht, hlo, hhi⟩
    have hw : β + 2 * Real.pi * (m : ℝ) ∈
        selectedLongitudinalLiftSet A B hh hΔ t := by
      rw [selectedLongitudinalLiftSet_eq_Icc A B hh hΔ ht]
      exact ⟨hlo, hhi⟩
    obtain ⟨i, hi, s, hs, he⟩ := hw
    exact ⟨ht, i, hi, s, hs, he.symm⟩

/-- Actual membership is equivalent to hitting the corresponding ray with a
positive radius and the specified real polar lift. In particular the reverse
implication is not inferred from Cartesian ray intersection alone. -/
theorem selectedRayHeightComponent_iff_positiveRay
    (hΔ : Δ A B hh < 0) (β : ℝ) (m : ℤ) (t : ℝ) :
    t ∈ selectedRayHeightComponent A B hh hΔ β m ↔
      t ∈ Ioo (0 : ℝ) 1 ∧
        ∃ i ≤ N A B, ∃ s ∈ Icc (0 : ℝ) 1,
          selectedPointPolarLift A B hh hΔ i s t = β + 2 * Real.pi * (m : ℝ) ∧
          ∃ r : ℝ, 0 < r ∧
            (rootStrip A B hh
              (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point i s t -
              PhysicalMixedTurnSource.circuitPole A B hh
                (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)
                (ne_of_lt hΔ) = r • MixedTurnSafeCut.direction
                  (β + 2 * Real.pi * (m : ℝ)) := by
  constructor
  · rintro ⟨ht, i, hi, s, hs, he⟩
    obtain ⟨hdecomp, hpos⟩ := selectedPointPolarLift_decomposition A B hh hΔ
      hi hs ⟨ht.1.le, ht.2.le⟩
    refine ⟨ht, i, hi, s, hs, he, _, hpos, ?_⟩
    simpa only [he] using hdecomp
  · rintro ⟨ht, i, hi, s, hs, he, r, hr, hpoint⟩
    exact ⟨ht, i, hi, s, hs, he⟩

/-- The selected seam lift remains in the strict root-panel half-plane
throughout the closed physical height interval. -/
theorem selectedAlpha_mem_window (hΔ : Δ A B hh < 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
    rootHeading A B hh k 0 < selectedAlpha A B hh hΔ t ∧
      selectedAlpha A B hh hΔ t < rootHeading A B hh k 0 + Real.pi := by
  exact selectedPointPolarLift_mem_window A B hh hΔ (i := 0) (s := 0)
    (by omega) (by norm_num) ht

/-- The selected seam's *real* argument is continuous on the whole closed
height interval: its panel-relative imaginary part stays strictly positive,
so the principal argument never crosses the slit. -/
theorem selectedAlpha_continuousOn (hΔ : Δ A B hh < 0) :
    ContinuousOn (selectedAlpha A B hh hΔ) (Icc (0 : ℝ) 1) := by
  let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
  let θ := rootHeading A B hh k 0
  let w : ℝ → ℂ := fun t => panelRelativeComplex θ
    ((rootStrip A B hh k).point 0 0 t -
      PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_lt hΔ))
  have hre : Continuous (fun t => (w t).re) := by
    dsimp [w, panelRelativeComplex,
      RadialExtremalSafety.TriangularRadialStrip.point]
    fun_prop
  have him : Continuous (fun t => (w t).im) := by
    dsimp [w, panelRelativeComplex,
      RadialExtremalSafety.TriangularRadialStrip.point]
    fun_prop
  have hwcont : Continuous w := by
    have hc : Continuous (fun t => ((w t).re : ℂ) + ((w t).im : ℂ) * Complex.I) :=
      (Complex.continuous_ofReal.comp hre).add
        ((Complex.continuous_ofReal.comp him).mul continuous_const)
    convert hc using 1
    funext t
    apply Complex.ext <;> simp
  intro t ht
  have hslit : w t ∈ Complex.slitPlane := by
    have hsupport := RadialExtremalSafety.TriangularRadialStrip.support_point
      (selectedRoot_radialSupport A B hh hΔ) (i := 0) (by omega)
      (by norm_num : (0 : ℝ) ∈ Icc 0 1) ht
    apply Complex.mem_slitPlane_iff.mpr
    right
    have hanti : MixedTurnSafeCut.det ((rootStrip A B hh k).v 0)
        ((rootStrip A B hh k).point 0 0 t -
          PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_lt hΔ)) =
        -MixedTurnSafeCut.det
          ((rootStrip A B hh k).point 0 0 t -
            PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_lt hΔ))
          ((rootStrip A B hh k).v 0) := by
      simp [MixedTurnSafeCut.det]; ring
    change MixedTurnSafeCut.det
      ((rootStrip A B hh k).point 0 0 t -
        PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_lt hΔ))
      ((rootStrip A B hh k).v 0) < 0 at hsupport
    have himpos : 0 < (w t).im := by
      rw [show (w t).im = MixedTurnSafeCut.det
        (MixedTurnSafeCut.direction θ)
        ((rootStrip A B hh k).point 0 0 t -
          PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_lt hΔ)) by
            simp [w, panelRelativeComplex_im]]
      rw [← rootForward_eq_direction A B hh k 0]
      change 0 < MixedTurnSafeCut.det ((rootStrip A B hh k).v 0) _
      rw [hanti]
      exact neg_pos.mpr hsupport
    exact ne_of_gt himpos
  have harg : ContinuousAt (fun r => (w r).arg) t :=
    (Complex.continuousAt_arg hslit).comp hwcont.continuousAt
  exact (continuousAt_const.add harg).continuousWithinAt

/-- Fixed material coordinates have a continuous real lift along the entire
closed physical height interval, since the support half-plane avoids the slit. -/
theorem selectedPointPolarLift_continuousOn_height (hΔ : Δ A B hh < 0)
    {i : ℕ} (hi : i ≤ N A B) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (selectedPointPolarLift A B hh hΔ i s) (Icc (0 : ℝ) 1) := by
  let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
  let θ := rootHeading A B hh k i
  let w : ℝ → ℂ := fun t => panelRelativeComplex θ
    ((rootStrip A B hh k).point i s t -
      PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_lt hΔ))
  have hre : Continuous (fun t => (w t).re) := by
    dsimp [w, panelRelativeComplex,
      RadialExtremalSafety.TriangularRadialStrip.point]
    fun_prop
  have him : Continuous (fun t => (w t).im) := by
    dsimp [w, panelRelativeComplex,
      RadialExtremalSafety.TriangularRadialStrip.point]
    fun_prop
  have hwcont : Continuous w := by
    have hc : Continuous (fun t => ((w t).re : ℂ) + ((w t).im : ℂ) * Complex.I) :=
      (Complex.continuous_ofReal.comp hre).add
        ((Complex.continuous_ofReal.comp him).mul continuous_const)
    convert hc using 1
    funext t
    apply Complex.ext <;> simp
  intro t ht
  have hslit : w t ∈ Complex.slitPlane := by
    have hsupport := RadialExtremalSafety.TriangularRadialStrip.support_point
      (selectedRoot_radialSupport A B hh hΔ) hi hs ht
    apply Complex.mem_slitPlane_iff.mpr
    right
    have hanti : MixedTurnSafeCut.det ((rootStrip A B hh k).v i)
        ((rootStrip A B hh k).point i s t -
          PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_lt hΔ)) =
        -MixedTurnSafeCut.det
          ((rootStrip A B hh k).point i s t -
            PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_lt hΔ))
          ((rootStrip A B hh k).v i) := by
      simp [MixedTurnSafeCut.det]; ring
    change MixedTurnSafeCut.det
      ((rootStrip A B hh k).point i s t -
        PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_lt hΔ))
      ((rootStrip A B hh k).v i) < 0 at hsupport
    have himpos : 0 < (w t).im := by
      rw [show (w t).im = MixedTurnSafeCut.det
        (MixedTurnSafeCut.direction θ)
        ((rootStrip A B hh k).point i s t -
          PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_lt hΔ)) by
            simp [w, panelRelativeComplex_im]]
      rw [← rootForward_eq_direction A B hh k i]
      change 0 < MixedTurnSafeCut.det ((rootStrip A B hh k).v i) _
      rw [hanti]
      exact neg_pos.mpr hsupport
    exact ne_of_gt himpos
  have harg : ContinuousAt (fun r => (w r).arg) t :=
    (Complex.continuousAt_arg hslit).comp hwcont.continuousAt
  exact (continuousAt_const.add harg).continuousWithinAt

/-- The signed area of two seam radii is affine in the height difference. -/
private theorem selectedAlpha_seam_det (hΔ : Δ A B hh < 0) (s t : ℝ) :
    let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
    let S := rootStrip A B hh k
    let O := PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_lt hΔ)
    MixedTurnSafeCut.det (S.point 0 0 s - O) (S.point 0 0 t - O) =
      (t - s) * MixedTurnSafeCut.det (S.B 0 - O) (S.d 0) := by
  dsimp
  simp only [RadialExtremalSafety.TriangularRadialStrip.point, zero_mul,
    zero_smul, add_zero]
  simp [MixedTurnSafeCut.det]
  ring

/-- The seam determinant has the sign of the difference of its real arguments:
all arguments lie in a single open half-plane. -/
private theorem selectedAlpha_det_sign (hΔ : Δ A B hh < 0)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
    let S := rootStrip A B hh k
    let O := PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_lt hΔ)
    (0 < MixedTurnSafeCut.det (S.point 0 0 s - O) (S.point 0 0 t - O) ↔
      selectedAlpha A B hh hΔ s < selectedAlpha A B hh hΔ t) ∧
    (MixedTurnSafeCut.det (S.point 0 0 s - O) (S.point 0 0 t - O) = 0 ↔
      selectedAlpha A B hh hΔ s = selectedAlpha A B hh hΔ t) := by
  let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
  let S := rootStrip A B hh k
  let O := PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_lt hΔ)
  let z (r : ℝ) := S.point 0 0 r - O
  let a (r : ℝ) := selectedAlpha A B hh hΔ r
  have hds := selectedPointPolarLift_decomposition A B hh hΔ
    (i := 0) (by omega) (by norm_num : (0 : ℝ) ∈ Icc 0 1) hs
  have hdt := selectedPointPolarLift_decomposition A B hh hΔ
    (i := 0) (by omega) (by norm_num : (0 : ℝ) ∈ Icc 0 1) ht
  change z s = ‖z s‖ • MixedTurnSafeCut.direction (a s) ∧ 0 < ‖z s‖ at hds
  change z t = ‖z t‖ • MixedTurnSafeCut.direction (a t) ∧ 0 < ‖z t‖ at hdt
  have hwS := selectedAlpha_mem_window A B hh hΔ hs
  have hwT := selectedAlpha_mem_window A B hh hΔ ht
  change rootHeading A B hh k 0 < a s ∧ a s < rootHeading A B hh k 0 + Real.pi at hwS
  change rootHeading A B hh k 0 < a t ∧ a t < rootHeading A B hh k 0 + Real.pi at hwT
  have hlow : -Real.pi < a t - a s := by linarith
  have hhigh : a t - a s < Real.pi := by linarith
  have hd : MixedTurnSafeCut.det (z s) (z t) =
      ‖z s‖ * ‖z t‖ * Real.sin (a t - a s) := by
    conv_lhs => rw [hds.1, hdt.1, RadialExtremalSafety.det_smul_left,
      RadialExtremalSafety.det_smul_right]
    simp only [MixedTurnSafeCut.det, MixedTurnSafeCut.direction,
      Matrix.cons_val_zero, Matrix.cons_val_one, Real.sin_sub]
    ring
  dsimp only
  rw [hd]
  constructor
  · constructor
    · intro hp
      by_contra hn
      have hnon : a t - a s ≤ 0 := sub_nonpos.mpr (le_of_not_gt hn)
      have hsin : Real.sin (a t - a s) ≤ 0 := by
        have := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith : 0 ≤ -(a t - a s))
          (by linarith : -(a t - a s) ≤ Real.pi)
        rw [Real.sin_neg] at this
        linarith
      nlinarith [mul_pos hds.2 hdt.2]
    · intro hp
      have hsin := Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hp) hhigh
      exact mul_pos (mul_pos hds.2 hdt.2) hsin
  · constructor
    · intro hz
      by_contra hn
      rcases lt_or_gt_of_ne hn with hp | hp
      · have hsin := Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hp) hhigh
        nlinarith [mul_pos hds.2 hdt.2]
      · have hsin := Real.sin_pos_of_pos_of_lt_pi (by linarith : 0 < a s - a t)
          (by linarith : a s - a t < Real.pi)
        have hneg : Real.sin (a t - a s) < 0 := by
          rw [show a t - a s = -(a s - a t) by ring, Real.sin_neg]
          linarith
        nlinarith [mul_pos hds.2 hdt.2]
    · intro he
      change a s = a t at he
      rw [he, sub_self, Real.sin_zero, mul_zero]

/-- The affine seam has exactly one of the three possible real angular orders. -/
theorem selectedAlpha_det_trichotomy (hΔ : Δ A B hh < 0) :
    StrictMonoOn (selectedAlpha A B hh hΔ) (Icc (0 : ℝ) 1) ∨
    StrictAntiOn (selectedAlpha A B hh hΔ) (Icc (0 : ℝ) 1) ∨
    ∀ t ∈ Icc (0 : ℝ) 1,
      selectedAlpha A B hh hΔ t = selectedAlpha A B hh hΔ 0 := by
  let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
  let S := rootStrip A B hh k
  let O := PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_lt hΔ)
  let D := MixedTurnSafeCut.det (S.B 0 - O) (S.d 0)
  rcases lt_trichotomy 0 D with hp | hz | hn
  · left
    intro s hs t ht hst
    have he := (selectedAlpha_det_sign A B hh hΔ hs ht).1
    rw [selectedAlpha_seam_det] at he
    exact he.mp (mul_pos (sub_pos.mpr hst) hp)
  · right; right
    intro t ht
    have he := (selectedAlpha_det_sign A B hh hΔ ht
      (show (0 : ℝ) ∈ Icc 0 1 by norm_num)).2
    apply he.mp
    rw [selectedAlpha_seam_det]
    exact mul_eq_zero_of_right _ hz.symm
  · right; left
    intro s hs t ht hst
    have he := (selectedAlpha_det_sign A B hh hΔ ht hs).1
    rw [selectedAlpha_seam_det] at he
    have hd : 0 < (s - t) * D := mul_pos_of_neg_of_neg (sub_neg.mpr hst) hn
    exact he.mp hd

/-- Positive determinant gives strict increase without an assumed order. -/
theorem selectedAlpha_strictMono_of_det_pos (hΔ : Δ A B hh < 0)
    (hD : 0 < MixedTurnSafeCut.det
      ((rootStrip A B hh (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).B 0 -
        PhysicalMixedTurnSource.circuitPole A B hh
          (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ) (ne_of_lt hΔ))
      ((rootStrip A B hh (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).d 0)) :
    StrictMonoOn (selectedAlpha A B hh hΔ) (Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  have he := (selectedAlpha_det_sign A B hh hΔ hs ht).1
  rw [selectedAlpha_seam_det] at he
  exact he.mp (mul_pos (sub_pos.mpr hst) hD)

/-- Negative determinant gives strict decrease without an assumed order. -/
theorem selectedAlpha_strictAnti_of_det_neg (hΔ : Δ A B hh < 0)
    (hD : MixedTurnSafeCut.det
      ((rootStrip A B hh (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).B 0 -
        PhysicalMixedTurnSource.circuitPole A B hh
          (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ) (ne_of_lt hΔ))
      ((rootStrip A B hh (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).d 0) < 0) :
    StrictAntiOn (selectedAlpha A B hh hΔ) (Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  have he := (selectedAlpha_det_sign A B hh hΔ ht hs).1
  rw [selectedAlpha_seam_det] at he
  exact he.mp (mul_pos_of_neg_of_neg (sub_neg.mpr hst) hD)

/-- Nonadjacent angular representatives cannot both be realized by the
selected physical strip at (possibly different) interior heights. -/
theorem selectedRayHeightComponent_no_three (hΔ : Δ A B hh < 0)
    (β : ℝ) {m₁ m₂ m₃ : ℤ} (h₁₂ : m₁ < m₂) (h₂₃ : m₂ < m₃)
    (h₁ : (selectedRayHeightComponent A B hh hΔ β m₁).Nonempty)
    (h₃ : (selectedRayHeightComponent A B hh hΔ β m₃).Nonempty) : False := by
  obtain ⟨t₁, ht₁⟩ := h₁
  obtain ⟨t₃, ht₃⟩ := h₃
  rw [selectedRayHeightComponent_iff] at ht₁ ht₃
  have ha₁ := selectedAlpha_mem_window A B hh hΔ
    (show t₁ ∈ Icc (0 : ℝ) 1 from ⟨ht₁.1.1.le, ht₁.1.2.le⟩)
  have ha₃ := selectedAlpha_mem_window A B hh hΔ
    (show t₃ ∈ Icc (0 : ℝ) 1 from ⟨ht₃.1.1.le, ht₃.1.2.le⟩)
  have hgap : m₁ + 2 ≤ m₃ := by omega
  have hgap' : (m₁ : ℝ) + 2 ≤ (m₃ : ℝ) := by exact_mod_cast hgap
  have hlen := longitudinalLength_lt_two_pi A B hh
  have hpi := Real.pi_pos
  change -Δ A B hh < 2 * Real.pi at hlen
  dsimp only at ha₁ ha₃
  nlinarith [ht₁.2.1, ht₃.2.2, ha₁.2, ha₃.1]

/-- Every pair of distinct realized representatives is consecutive. -/
theorem selectedRayHeightComponent_consecutive (hΔ : Δ A B hh < 0)
    (β : ℝ) {m₁ m₂ : ℤ} (h₁₂ : m₁ < m₂)
    (h₁ : (selectedRayHeightComponent A B hh hΔ β m₁).Nonempty)
    (h₂ : (selectedRayHeightComponent A B hh hΔ β m₂).Nonempty) :
    m₂ = m₁ + 1 := by
  by_contra hne
  have hm : m₁ < m₁ + 1 ∧ m₁ + 1 < m₂ := by omega
  exact selectedRayHeightComponent_no_three A B hh hΔ β hm.1 hm.2 h₁ h₂

/-- If the selected seam lift increases, actual heights on the lower
representative precede those on the higher representative. -/
theorem selectedRayHeightComponent_order_of_mono (hΔ : Δ A B hh < 0)
    (β : ℝ) (hα : MonotoneOn (selectedAlpha A B hh hΔ) (Icc (0 : ℝ) 1))
    {m₁ m₂ : ℤ} (hm : m₁ < m₂)
    {t u : ℝ} (ht : t ∈ selectedRayHeightComponent A B hh hΔ β m₁)
    (hu : u ∈ selectedRayHeightComponent A B hh hΔ β m₂) : t < u := by
  rw [selectedRayHeightComponent_iff] at ht hu
  have hcast : (m₁ : ℝ) + 1 ≤ (m₂ : ℝ) := by exact_mod_cast (show m₁ + 1 ≤ m₂ by omega)
  have hL := longitudinalLength_lt_two_pi A B hh
  have hpi := Real.pi_pos
  have hsep : selectedAlpha A B hh hΔ t < selectedAlpha A B hh hΔ u := by
    change -Δ A B hh < 2 * Real.pi at hL
    nlinarith [ht.2.1, hu.2.2]
  by_contra hnot
  have hle : u ≤ t := le_of_not_gt hnot
  have hreverse := hα ⟨hu.1.1.le, hu.1.2.le⟩
    ⟨ht.1.1.le, ht.1.2.le⟩ hle
  exact (not_le_of_gt hsep) hreverse

/-- If the selected seam lift decreases, the higher representative occurs
strictly before the lower one. -/
theorem selectedRayHeightComponent_order_of_anti (hΔ : Δ A B hh < 0)
    (β : ℝ) (hα : AntitoneOn (selectedAlpha A B hh hΔ) (Icc (0 : ℝ) 1))
    {m₁ m₂ : ℤ} (hm : m₁ < m₂)
    {t u : ℝ} (ht : t ∈ selectedRayHeightComponent A B hh hΔ β m₁)
    (hu : u ∈ selectedRayHeightComponent A B hh hΔ β m₂) : u < t := by
  rw [selectedRayHeightComponent_iff] at ht hu
  have hcast : (m₁ : ℝ) + 1 ≤ (m₂ : ℝ) := by exact_mod_cast (show m₁ + 1 ≤ m₂ by omega)
  have hL := longitudinalLength_lt_two_pi A B hh
  have hpi := Real.pi_pos
  have hsep : selectedAlpha A B hh hΔ t < selectedAlpha A B hh hΔ u := by
    change -Δ A B hh < 2 * Real.pi at hL
    nlinarith [ht.2.1, hu.2.2]
  by_contra hnot
  have hle : t ≤ u := le_of_not_gt hnot
  have hreverse := hα ⟨ht.1.1.le, ht.1.2.le⟩
    ⟨hu.1.1.le, hu.1.2.le⟩ hle
  exact (not_le_of_gt hsep) hreverse

/-- Each actual fixed-lift component is an interval whenever the selected
seam has increasing real argument. -/
theorem selectedRayHeightComponent_convex_of_mono (hΔ : Δ A B hh < 0)
    (β : ℝ) (m : ℤ)
    (hα : MonotoneOn (selectedAlpha A B hh hΔ) (Icc (0 : ℝ) 1))
    {s t u : ℝ} (hs : s ∈ selectedRayHeightComponent A B hh hΔ β m)
    (hu : u ∈ selectedRayHeightComponent A B hh hΔ β m)
    (hst : s ≤ t) (htu : t ≤ u) :
    t ∈ selectedRayHeightComponent A B hh hΔ β m := by
  rw [selectedRayHeightComponent_iff] at hs hu ⊢
  refine ⟨⟨lt_of_lt_of_le hs.1.1 hst, lt_of_le_of_lt htu hu.1.2⟩, ?_, ?_⟩
  · have h := hα ⟨(hs.1.1.trans_le hst).le, (htu.trans hu.1.2.le)⟩
      ⟨hu.1.1.le, hu.1.2.le⟩ htu
    linarith [hu.2.1]
  · have h := hα ⟨hs.1.1.le, hs.1.2.le⟩
      ⟨(hs.1.1.trans_le hst).le, (htu.trans hu.1.2.le)⟩ hst
    linarith [hs.2.2]

/-- The same actual interval property for a decreasing selected seam lift. -/
theorem selectedRayHeightComponent_convex_of_anti (hΔ : Δ A B hh < 0)
    (β : ℝ) (m : ℤ)
    (hα : AntitoneOn (selectedAlpha A B hh hΔ) (Icc (0 : ℝ) 1))
    {s t u : ℝ} (hs : s ∈ selectedRayHeightComponent A B hh hΔ β m)
    (hu : u ∈ selectedRayHeightComponent A B hh hΔ β m)
    (hst : s ≤ t) (htu : t ≤ u) :
    t ∈ selectedRayHeightComponent A B hh hΔ β m := by
  rw [selectedRayHeightComponent_iff] at hs hu ⊢
  refine ⟨⟨lt_of_lt_of_le hs.1.1 hst, lt_of_le_of_lt htu hu.1.2⟩, ?_, ?_⟩
  · have h := hα ⟨hs.1.1.le, hs.1.2.le⟩
      ⟨(hs.1.1.trans_le hst).le, (htu.trans hu.1.2.le)⟩ hst
    linarith [hs.2.1]
  · have h := hα ⟨(hs.1.1.trans_le hst).le, (htu.trans hu.1.2.le)⟩
      ⟨hu.1.1.le, hu.1.2.le⟩ htu
    linarith [hu.2.2]

/-- At a fixed physical height, the selected strip cannot meet two different
real representatives of the same physical ray. -/
theorem selectedRayHeightComponent_sameHeight_unique (hΔ : Δ A B hh < 0)
    (β : ℝ) {m₁ m₂ : ℤ} {t : ℝ}
    (h₁ : t ∈ selectedRayHeightComponent A B hh hΔ β m₁)
    (h₂ : t ∈ selectedRayHeightComponent A B hh hΔ β m₂) : m₁ = m₂ := by
  rw [selectedRayHeightComponent_iff] at h₁ h₂
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hc : (m₁ : ℝ) + 1 ≤ (m₂ : ℝ) := by
      exact_mod_cast (show m₁ + 1 ≤ m₂ by omega)
    have hL := longitudinalLength_lt_two_pi A B hh
    have hpi := Real.pi_pos
    change -Δ A B hh < 2 * Real.pi at hL
    nlinarith [h₁.2.1, h₂.2.2]
  · have hc : (m₂ : ℝ) + 1 ≤ (m₁ : ℝ) := by
      exact_mod_cast (show m₂ + 1 ≤ m₁ by omega)
    have hL := longitudinalLength_lt_two_pi A B hh
    have hpi := Real.pi_pos
    change -Δ A B hh < 2 * Real.pi at hL
    nlinarith [h₂.2.1, h₁.2.2]

/-- A constant selected-seam argument supports at most one real lift of a
fixed physical ray, even though the strip has positive angular width. -/
theorem selectedRayHeightComponent_constant_unique (hΔ : Δ A B hh < 0)
    (β : ℝ) (hα : ∀ t ∈ Ioo (0 : ℝ) 1,
      selectedAlpha A B hh hΔ t = selectedAlpha A B hh hΔ (1 / 2))
    {m₁ m₂ : ℤ}
    (h₁ : (selectedRayHeightComponent A B hh hΔ β m₁).Nonempty)
    (h₂ : (selectedRayHeightComponent A B hh hΔ β m₂).Nonempty) : m₁ = m₂ := by
  obtain ⟨t₁, ht₁⟩ := h₁
  obtain ⟨t₂, ht₂⟩ := h₂
  rw [selectedRayHeightComponent_iff] at ht₁ ht₂
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hc : (m₁ : ℝ) + 1 ≤ (m₂ : ℝ) := by
      exact_mod_cast (show m₁ + 1 ≤ m₂ by omega)
    have hL := longitudinalLength_lt_two_pi A B hh
    have hpi := Real.pi_pos
    change -Δ A B hh < 2 * Real.pi at hL
    rw [hα t₁ ht₁.1] at ht₁
    rw [hα t₂ ht₂.1] at ht₂
    nlinarith [ht₁.2.1, ht₂.2.2]
  · have hc : (m₂ : ℝ) + 1 ≤ (m₁ : ℝ) := by
      exact_mod_cast (show m₂ + 1 ≤ m₁ by omega)
    have hL := longitudinalLength_lt_two_pi A B hh
    have hpi := Real.pi_pos
    change -Δ A B hh < 2 * Real.pi at hL
    rw [hα t₁ ht₁.1] at ht₁
    rw [hα t₂ ht₂.1] at ht₂
    nlinarith [ht₂.2.1, ht₁.2.2]

/-- Every actual representative-height component is order-convex, with no
monotonicity hypothesis imposed on the seam. -/
theorem selectedRayHeightComponent_convex (hΔ : Δ A B hh < 0)
    (β : ℝ) (m : ℤ) {s t u : ℝ}
    (hs : s ∈ selectedRayHeightComponent A B hh hΔ β m)
    (hu : u ∈ selectedRayHeightComponent A B hh hΔ β m)
    (hst : s ≤ t) (htu : t ≤ u) :
    t ∈ selectedRayHeightComponent A B hh hΔ β m := by
  rcases selectedAlpha_det_trichotomy A B hh hΔ with hinc | hdec | hconst
  · exact selectedRayHeightComponent_convex_of_mono A B hh hΔ β m
      hinc.monotoneOn hs hu hst htu
  · exact selectedRayHeightComponent_convex_of_anti A B hh hΔ β m
      hdec.antitoneOn hs hu hst htu
  · apply selectedRayHeightComponent_convex_of_mono A B hh hΔ β m
    · intro x hx y hy hxy
      rw [hconst x hx, hconst y hy]
    · exact hs
    · exact hu
    · exact hst
    · exact htu

/-- Each realized component is relatively closed in the open height interval. -/
theorem selectedRayHeightComponent_relativelyClosed (hΔ : Δ A B hh < 0)
    (β : ℝ) (m : ℤ) :
    ∃ F : Set ℝ, IsClosed F ∧
      selectedRayHeightComponent A B hh hΔ β m = Ioo (0 : ℝ) 1 ∩ F := by
  let c := β + 2 * Real.pi * (m : ℝ)
  let F := Icc (0 : ℝ) 1 ∩
    (selectedAlpha A B hh hΔ) ⁻¹' Icc c (c - Δ A B hh)
  refine ⟨F, ?_, ?_⟩
  · exact (selectedAlpha_continuousOn A B hh hΔ).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Icc
  · ext t
    rw [selectedRayHeightComponent_iff]
    simp only [F, mem_inter_iff, mem_preimage, mem_Icc, mem_Ioo]
    constructor
    · rintro ⟨ht, hlo, hhi⟩
      exact ⟨ht, ⟨ht.1.le, ht.2.le⟩, hhi, by linarith⟩
    · rintro ⟨ht, hclosed, hhi, hlo⟩
      exact ⟨ht, by linarith, hhi⟩

/-- Distinct realized representatives are strictly ordered in height;
which direction holds is determined by the seam determinant, not assumed. -/
theorem selectedRayHeightComponent_order (hΔ : Δ A B hh < 0)
    (β : ℝ) {m₁ m₂ : ℤ} (hm : m₁ < m₂)
    {t u : ℝ} (ht : t ∈ selectedRayHeightComponent A B hh hΔ β m₁)
    (hu : u ∈ selectedRayHeightComponent A B hh hΔ β m₂) :
    t < u ∨ u < t := by
  rcases selectedAlpha_det_trichotomy A B hh hΔ with hinc | hdec | hconst
  · exact Or.inl (selectedRayHeightComponent_order_of_mono A B hh hΔ β
      hinc.monotoneOn hm ht hu)
  · exact Or.inr (selectedRayHeightComponent_order_of_anti A B hh hΔ β
      hdec.antitoneOn hm ht hu)
  · have hsame := selectedRayHeightComponent_constant_unique A B hh hΔ β
      (by
        intro x hx
        rw [hconst x ⟨hx.1.le, hx.2.le⟩,
          hconst (1 / 2) (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)])
      ⟨t, ht⟩ ⟨u, hu⟩
    omega

/-- Positive signed seam area orders lower representatives first. -/
theorem selectedRayHeightComponent_order_of_det_pos (hΔ : Δ A B hh < 0)
    (β : ℝ)
    (hD : 0 < MixedTurnSafeCut.det
      ((rootStrip A B hh (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).B 0 -
        PhysicalMixedTurnSource.circuitPole A B hh
          (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ) (ne_of_lt hΔ))
      ((rootStrip A B hh (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).d 0))
    {m₁ m₂ : ℤ} (hm : m₁ < m₂) {t u : ℝ}
    (ht : t ∈ selectedRayHeightComponent A B hh hΔ β m₁)
    (hu : u ∈ selectedRayHeightComponent A B hh hΔ β m₂) : t < u :=
  selectedRayHeightComponent_order_of_mono A B hh hΔ β
    (selectedAlpha_strictMono_of_det_pos A B hh hΔ hD).monotoneOn hm ht hu

/-- Negative signed seam area reverses that strict height ordering. -/
theorem selectedRayHeightComponent_order_of_det_neg (hΔ : Δ A B hh < 0)
    (β : ℝ)
    (hD : MixedTurnSafeCut.det
      ((rootStrip A B hh (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).B 0 -
        PhysicalMixedTurnSource.circuitPole A B hh
          (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ) (ne_of_lt hΔ))
      ((rootStrip A B hh (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).d 0) < 0)
    {m₁ m₂ : ℤ} (hm : m₁ < m₂) {t u : ℝ}
    (ht : t ∈ selectedRayHeightComponent A B hh hΔ β m₁)
    (hu : u ∈ selectedRayHeightComponent A B hh hΔ β m₂) : u < t :=
  selectedRayHeightComponent_order_of_anti A B hh hΔ β
    (selectedAlpha_strictAnti_of_det_neg A B hh hΔ hD).antitoneOn hm ht hu

/-- A level between two selected-seam values is attained at an actual height
between the witnesses, including when one component is a singleton. -/
private theorem selectedAlpha_intermediate (hΔ : Δ A B hh < 0)
    {s t q : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hst : s ≤ t) (hlo : selectedAlpha A B hh hΔ s ≤ q)
    (hhi : q ≤ selectedAlpha A B hh hΔ t) :
    ∃ u ∈ Icc s t, selectedAlpha A B hh hΔ u = q := by
  have hc : ContinuousOn (selectedAlpha A B hh hΔ) (Icc s t) :=
    (selectedAlpha_continuousOn A B hh hΔ).mono (by
      intro x hx
      exact ⟨lt_of_lt_of_le hs.1 hx.1 |>.le,
        lt_of_le_of_lt hx.2 ht.2 |>.le⟩)
  obtain ⟨u, hu, he⟩ := (intermediate_value_Icc hst hc) ⟨hlo, hhi⟩
  exact ⟨u, hu, he⟩

/-- The facing extrema of two consecutive *actual* representative components
in increasing seam order. Their real boundary lifts are respectively the
terminal and root seam, not merely congruent angles. -/
theorem selectedRayHeightComponent_facing_of_mono (hΔ : Δ A B hh < 0)
    (β : ℝ) {m₁ m₂ : ℤ} (hm : m₂ = m₁ + 1)
    (hα : StrictMonoOn (selectedAlpha A B hh hΔ) (Icc (0 : ℝ) 1))
    {s t : ℝ} (hs : s ∈ selectedRayHeightComponent A B hh hΔ β m₁)
    (ht : t ∈ selectedRayHeightComponent A B hh hΔ β m₂) :
    ∃ b c : ℝ, s ≤ b ∧ b < c ∧ c ≤ t ∧
      b ∈ selectedRayHeightComponent A B hh hΔ β m₁ ∧
      c ∈ selectedRayHeightComponent A B hh hΔ β m₂ ∧
      selectedPointPolarLift A B hh hΔ (N A B) 1 b =
        β + 2 * Real.pi * (m₁ : ℝ) ∧
      selectedPointPolarLift A B hh hΔ 0 0 c =
        β + 2 * Real.pi * (m₂ : ℝ) ∧
      (∀ x ∈ selectedRayHeightComponent A B hh hΔ β m₁, x ≤ b) ∧
      (∀ y ∈ selectedRayHeightComponent A B hh hΔ β m₂, c ≤ y) := by
  have hst := selectedRayHeightComponent_order_of_mono A B hh hΔ β
    hα.monotoneOn (by omega : m₁ < m₂) hs ht
  rw [selectedRayHeightComponent_iff] at hs ht
  let q₁ := β + 2 * Real.pi * (m₁ : ℝ) - Δ A B hh
  let q₂ := β + 2 * Real.pi * (m₂ : ℝ)
  have hq : q₁ < q₂ := by
    have hlen := longitudinalLength_lt_two_pi A B hh
    have hpi := Real.pi_pos
    change -Δ A B hh < 2 * Real.pi at hlen
    have hm' : (m₂ : ℝ) = (m₁ : ℝ) + 1 := by exact_mod_cast hm
    dsimp [q₁, q₂]
    rw [hm']
    nlinarith
  have hsc : selectedAlpha A B hh hΔ s ≤ q₁ := by dsimp [q₁]; linarith [hs.2.1]
  have hct : q₁ ≤ selectedAlpha A B hh hΔ t := by
    dsimp [q₁]; linarith [ht.2.2]
  obtain ⟨b, hbspan, hbval⟩ := selectedAlpha_intermediate A B hh hΔ
    hs.1 ht.1 hst.le hsc hct
  have hsc' : selectedAlpha A B hh hΔ s ≤ q₂ := by linarith
  have hct' : q₂ ≤ selectedAlpha A B hh hΔ t := ht.2.2
  obtain ⟨c, hcspan, hcval⟩ := selectedAlpha_intermediate A B hh hΔ
    hs.1 ht.1 hst.le hsc' hct'
  have hbi : b ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_lt_of_le hs.1.1 hbspan.1, lt_of_le_of_lt hbspan.2 ht.1.2⟩
  have hci : c ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_lt_of_le hs.1.1 hcspan.1, lt_of_le_of_lt hcspan.2 ht.1.2⟩
  have hbc : b < c := by
    by_contra hn
    have hcb : c ≤ b := le_of_not_gt hn
    have hmono := hα.monotoneOn
      (show c ∈ Icc (0 : ℝ) 1 from ⟨hci.1.le, hci.2.le⟩)
      (show b ∈ Icc (0 : ℝ) 1 from ⟨hbi.1.le, hbi.2.le⟩) hcb
    linarith
  have hbmem : b ∈ selectedRayHeightComponent A B hh hΔ β m₁ := by
    rw [selectedRayHeightComponent_iff]
    dsimp [q₁] at hbval
    exact ⟨hbi, by linarith [hbval], by linarith [hbval]⟩
  have hcmem : c ∈ selectedRayHeightComponent A B hh hΔ β m₂ := by
    rw [selectedRayHeightComponent_iff]
    have hlen := longitudinalLength_lt_two_pi A B hh
    change -Δ A B hh < 2 * Real.pi at hlen
    exact ⟨hci, by linarith [hcval], by linarith [hcval]⟩
  refine ⟨b, c, hbspan.1, hbc, hcspan.2, hbmem, hcmem, ?_, hcval, ?_, ?_⟩
  · rw [selectedPointPolarLift_terminal A B hh hΔ ⟨hbi.1.le, hbi.2.le⟩]
    dsimp [q₁, selectedAlpha] at hbval
    linarith [hbval]
  · intro x hx
    have hx' := (selectedRayHeightComponent_iff A B hh hΔ β m₁ x).mp hx
    by_contra hn
    have hbxx := hα ⟨hbi.1.le, hbi.2.le⟩
      ⟨hx'.1.1.le, hx'.1.2.le⟩ (lt_of_not_ge hn)
    dsimp [q₁] at hbval
    linarith [hx'.2.1]
  · intro y hy
    have hy' := (selectedRayHeightComponent_iff A B hh hΔ β m₂ y).mp hy
    by_contra hn
    have hycc := hα ⟨hy'.1.1.le, hy'.1.2.le⟩
      ⟨hci.1.le, hci.2.le⟩ (lt_of_not_ge hn)
    linarith [hy'.2.2]

/-- In decreasing seam order the higher representative faces first: its root
seam precedes the lower representative's literal terminal copy. -/
theorem selectedRayHeightComponent_facing_of_anti (hΔ : Δ A B hh < 0)
    (β : ℝ) {m₁ m₂ : ℤ} (hm : m₂ = m₁ + 1)
    (hα : StrictAntiOn (selectedAlpha A B hh hΔ) (Icc (0 : ℝ) 1))
    {s t : ℝ} (hs : s ∈ selectedRayHeightComponent A B hh hΔ β m₂)
    (ht : t ∈ selectedRayHeightComponent A B hh hΔ β m₁) :
    ∃ b c : ℝ, s ≤ b ∧ b < c ∧ c ≤ t ∧
      b ∈ selectedRayHeightComponent A B hh hΔ β m₂ ∧
      c ∈ selectedRayHeightComponent A B hh hΔ β m₁ ∧
      selectedPointPolarLift A B hh hΔ 0 0 b =
        β + 2 * Real.pi * (m₂ : ℝ) ∧
      selectedPointPolarLift A B hh hΔ (N A B) 1 c =
        β + 2 * Real.pi * (m₁ : ℝ) ∧
      (∀ x ∈ selectedRayHeightComponent A B hh hΔ β m₂, x ≤ b) ∧
      (∀ y ∈ selectedRayHeightComponent A B hh hΔ β m₁, c ≤ y) := by
  have hst := selectedRayHeightComponent_order_of_anti A B hh hΔ β
    hα.antitoneOn (by omega : m₁ < m₂) ht hs
  rw [selectedRayHeightComponent_iff] at hs ht
  let q₁ := β + 2 * Real.pi * (m₁ : ℝ) - Δ A B hh
  let q₂ := β + 2 * Real.pi * (m₂ : ℝ)
  have hq : q₁ < q₂ := by
    have hlen := longitudinalLength_lt_two_pi A B hh
    change -Δ A B hh < 2 * Real.pi at hlen
    have hm' : (m₂ : ℝ) = (m₁ : ℝ) + 1 := by exact_mod_cast hm
    dsimp [q₁, q₂]
    rw [hm']
    nlinarith [Real.pi_pos]
  have hsc : q₂ ≤ selectedAlpha A B hh hΔ s := hs.2.2
  have hct : selectedAlpha A B hh hΔ t ≤ q₂ := by
    dsimp [q₂]; linarith [ht.2.1]
  obtain ⟨b, hbspan, hbval⟩ := (intermediate_value_Icc' hst.le
    ((selectedAlpha_continuousOn A B hh hΔ).mono (by
      intro x hx
      exact ⟨(lt_of_lt_of_le hs.1.1 hx.1).le,
        (lt_of_le_of_lt hx.2 ht.1.2).le⟩))) ⟨hct, hsc⟩
  have hsc' : q₁ ≤ selectedAlpha A B hh hΔ s := by linarith
  have hct' : selectedAlpha A B hh hΔ t ≤ q₁ := by
    dsimp [q₁]; linarith [ht.2.1]
  obtain ⟨c, hcspan, hcval⟩ := (intermediate_value_Icc' hst.le
    ((selectedAlpha_continuousOn A B hh hΔ).mono (by
      intro x hx
      exact ⟨(lt_of_lt_of_le hs.1.1 hx.1).le,
        (lt_of_le_of_lt hx.2 ht.1.2).le⟩))) ⟨hct', hsc'⟩
  have hbi : b ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_lt_of_le hs.1.1 hbspan.1, lt_of_le_of_lt hbspan.2 ht.1.2⟩
  have hci : c ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_lt_of_le hs.1.1 hcspan.1, lt_of_le_of_lt hcspan.2 ht.1.2⟩
  have hbc : b < c := by
    by_contra hn
    have hcb : c ≤ b := le_of_not_gt hn
    have hanti := hα.antitoneOn
      (show c ∈ Icc (0 : ℝ) 1 from ⟨hci.1.le, hci.2.le⟩)
      (show b ∈ Icc (0 : ℝ) 1 from ⟨hbi.1.le, hbi.2.le⟩) hcb
    linarith
  have hbmem : b ∈ selectedRayHeightComponent A B hh hΔ β m₂ := by
    rw [selectedRayHeightComponent_iff]
    exact ⟨hbi, by linarith [hbval], by linarith [hbval]⟩
  have hcmem : c ∈ selectedRayHeightComponent A B hh hΔ β m₁ := by
    rw [selectedRayHeightComponent_iff]
    dsimp [q₁] at hcval
    exact ⟨hci, by linarith [hcval], by linarith [hcval]⟩
  refine ⟨b, c, hbspan.1, hbc, hcspan.2, hbmem, hcmem, hbval, ?_, ?_, ?_⟩
  · rw [selectedPointPolarLift_terminal A B hh hΔ ⟨hci.1.le, hci.2.le⟩]
    dsimp [q₁, selectedAlpha] at hcval
    linarith [hcval]
  · intro x hx
    have hx' := (selectedRayHeightComponent_iff A B hh hΔ β m₂ x).mp hx
    by_contra hn
    have hbxx := hα ⟨hbi.1.le, hbi.2.le⟩
      ⟨hx'.1.1.le, hx'.1.2.le⟩ (lt_of_not_ge hn)
    linarith [hx'.2.2]
  · intro y hy
    have hy' := (selectedRayHeightComponent_iff A B hh hΔ β m₁ y).mp hy
    by_contra hn
    have hycc := hα ⟨hy'.1.1.le, hy'.1.2.le⟩
      ⟨hci.1.le, hci.2.le⟩ (lt_of_not_ge hn)
    dsimp [q₁] at hcval
    linarith [hy'.2.1]

/-- Source-selected inwardness gives the strict norm gap at the actual
terminal/root facing extrema; the terminal norm is the full-circuit copy. -/
theorem selectedRayHeightComponent_facing_radius_of_mono (hΔ : Δ A B hh < 0)
    (β : ℝ) {m₁ m₂ : ℤ} (hm : m₂ = m₁ + 1)
    (hα : StrictMonoOn (selectedAlpha A B hh hΔ) (Icc (0 : ℝ) 1))
    {s t : ℝ} (hs : s ∈ selectedRayHeightComponent A B hh hΔ β m₁)
    (ht : t ∈ selectedRayHeightComponent A B hh hΔ β m₂) :
    ∃ b c : ℝ, s ≤ b ∧ b < c ∧ c ≤ t ∧
      b ∈ selectedRayHeightComponent A B hh hΔ β m₁ ∧
      c ∈ selectedRayHeightComponent A B hh hΔ β m₂ ∧
      selectedPointPolarLift A B hh hΔ (N A B) 1 b =
        β + 2 * Real.pi * (m₁ : ℝ) ∧
      selectedPointPolarLift A B hh hΔ 0 0 c =
        β + 2 * Real.pi * (m₂ : ℝ) ∧
      ‖RadialOriginalSeam.selectedNegativeSeamCurve A B hh hΔ c -
        PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)‖ <
      ‖RadialOriginalSeam.selectedNegativeTerminalSeamCurve A B hh hΔ b -
        PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)‖ := by
  obtain ⟨b, c, hsb, hbc, hct, hb, hc, hbl, hcl, _, _⟩ :=
    selectedRayHeightComponent_facing_of_mono A B hh hΔ β hm hα hs ht
  refine ⟨b, c, hsb, hbc, hct, hb, hc, hbl, hcl, ?_⟩
  have hbi := (selectedRayHeightComponent_iff A B hh hΔ β m₁ b).mp hb |>.1
  have hci := (selectedRayHeightComponent_iff A B hh hΔ β m₂ c).mp hc |>.1
  have hin := RadialOriginalSeam.selectedNegativeSeamCurve_radiallyInward A B hh hΔ
    ⟨hbi.1.le, hbi.2.le⟩ ⟨hci.1.le, hci.2.le⟩ hbc
  simp only [Function.comp_apply, FixedBaselinePolarTrace.polarRadius_eq_norm] at hin
  rw [RadialOriginalSeam.selectedNegativeTerminalSeam_radius_eq A B hh hΔ b]
  exact hin

/-- The decreasing-angle facing pair has the reversed literal seam types,
while the selected source radius still decreases with physical height. -/
theorem selectedRayHeightComponent_facing_radius_of_anti (hΔ : Δ A B hh < 0)
    (β : ℝ) {m₁ m₂ : ℤ} (hm : m₂ = m₁ + 1)
    (hα : StrictAntiOn (selectedAlpha A B hh hΔ) (Icc (0 : ℝ) 1))
    {s t : ℝ} (hs : s ∈ selectedRayHeightComponent A B hh hΔ β m₂)
    (ht : t ∈ selectedRayHeightComponent A B hh hΔ β m₁) :
    ∃ b c : ℝ, s ≤ b ∧ b < c ∧ c ≤ t ∧
      b ∈ selectedRayHeightComponent A B hh hΔ β m₂ ∧
      c ∈ selectedRayHeightComponent A B hh hΔ β m₁ ∧
      selectedPointPolarLift A B hh hΔ 0 0 b =
        β + 2 * Real.pi * (m₂ : ℝ) ∧
      selectedPointPolarLift A B hh hΔ (N A B) 1 c =
        β + 2 * Real.pi * (m₁ : ℝ) ∧
      ‖RadialOriginalSeam.selectedNegativeTerminalSeamCurve A B hh hΔ c -
        PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)‖ <
      ‖RadialOriginalSeam.selectedNegativeSeamCurve A B hh hΔ b -
        PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)‖ := by
  obtain ⟨b, c, hsb, hbc, hct, hb, hc, hbl, hcl, _, _⟩ :=
    selectedRayHeightComponent_facing_of_anti A B hh hΔ β hm hα hs ht
  refine ⟨b, c, hsb, hbc, hct, hb, hc, hbl, hcl, ?_⟩
  have hbi := (selectedRayHeightComponent_iff A B hh hΔ β m₂ b).mp hb |>.1
  have hci := (selectedRayHeightComponent_iff A B hh hΔ β m₁ c).mp hc |>.1
  have hin := RadialOriginalSeam.selectedNegativeSeamCurve_radiallyInward A B hh hΔ
    ⟨hbi.1.le, hbi.2.le⟩ ⟨hci.1.le, hci.2.le⟩ hbc
  simp only [Function.comp_apply, FixedBaselinePolarTrace.polarRadius_eq_norm] at hin
  rw [RadialOriginalSeam.selectedNegativeTerminalSeam_radius_eq A B hh hΔ c]
  exact hin

/-- Actual heights from distinct realized components never identify the
selected source seam with its terminal full-circuit copy. This concerns seam
points, not arbitrary material points in the intervening panels. -/
theorem selectedRayHeightComponent_crossComponent_seam_allPairs_ne
    (hΔ : Δ A B hh < 0) (β : ℝ) {m₁ m₂ : ℤ} (hm : m₁ < m₂)
    {s t : ℝ} (hs : s ∈ selectedRayHeightComponent A B hh hΔ β m₁)
    (ht : t ∈ selectedRayHeightComponent A B hh hΔ β m₂) :
    RadialOriginalSeam.selectedNegativeSeamCurve A B hh hΔ s ≠
      RadialOriginalSeam.selectedNegativeTerminalSeamCurve A B hh hΔ t := by
  have hne : s ≠ t := by
    rcases selectedRayHeightComponent_order A B hh hΔ β hm hs ht with h | h
    · exact ne_of_lt h
    · exact ne_of_gt h
  have hsi := (selectedRayHeightComponent_iff A B hh hΔ β m₁ s).mp hs |>.1
  have hti := (selectedRayHeightComponent_iff A B hh hΔ β m₂ t).mp ht |>.1
  exact RadialOriginalSeam.selectedNegativeSeam_crossGap_allPairs_ne A B hh hΔ
    ⟨hsi.1.le, hsi.2.le⟩ ⟨hti.1.le, hti.2.le⟩ hne

/-- A source material hit at the specified *real* ray representative. -/
def SelectedMaterialHit (hΔ : Δ A B hh < 0) (β : ℝ) (m : ℤ)
    (i : ℕ) (s t : ℝ) : Prop :=
  i ≤ N A B ∧ s ∈ Icc (0 : ℝ) 1 ∧ t ∈ Ioo (0 : ℝ) 1 ∧
    selectedPointPolarLift A B hh hΔ i s t = β + 2 * Real.pi * (m : ℝ)

/-- In the actual finite real angular partition, the entry of any later
panel is at or clockwise from the exit of the earlier one. Equality requires
that the panels share a retained hinge. -/
theorem selectedPanel_entries_order (hΔ : Δ A B hh < 0)
    {i j : ℕ} (hij : i < j) (hj : j ≤ N A B)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    selectedPointPolarLift A B hh hΔ j 0 t ≤
      selectedPointPolarLift A B hh hΔ i 1 t ∧
    (i + 1 < j → selectedPointPolarLift A B hh hΔ j 0 t <
      selectedPointPolarLift A B hh hΔ i 1 t) := by
  have hiN : i < N A B := by omega
  have hbase : selectedPointPolarLift A B hh hΔ (i + 1) 0 t =
      selectedPointPolarLift A B hh hΔ i 1 t :=
    (selectedPointPolarLift_hinge A B hh hΔ hiN ⟨ht.1.le, ht.2.le⟩).symm
  have hchain : ∀ k, i + 1 ≤ k → k ≤ N A B →
      selectedPointPolarLift A B hh hΔ k 0 t ≤
        selectedPointPolarLift A B hh hΔ i 1 t := by
    intro k hik hk
    induction k, hik using Nat.le_induction with
    | base => exact hbase.le
    | succ k hik ih =>
        have hkN : k < N A B := by omega
        have hstep := selectedPointPolarLift_hinge A B hh hΔ hkN
          ⟨ht.1.le, ht.2.le⟩
        have hstrict := (selectedPointPolarLift_strictAnti A B hh hΔ
          (Nat.le_of_lt hkN) ht) (by norm_num : (0 : ℝ) ∈ Icc 0 1)
            (by norm_num : (1 : ℝ) ∈ Icc 0 1) (by norm_num : (0 : ℝ) < 1)
        rw [← hstep]
        exact le_of_lt (lt_of_lt_of_le hstrict (ih (by omega)))
  refine ⟨hchain j (by omega) hj, ?_⟩
  intro hfar
  have hprev : i + 1 ≤ j - 1 := by omega
  have hprevN : j - 1 < N A B := by omega
  have hbound := hchain (j - 1) hprev (Nat.le_of_lt hprevN)
  have hstep := selectedPointPolarLift_hinge A B hh hΔ hprevN
    ⟨ht.1.le, ht.2.le⟩
  have hstrict := (selectedPointPolarLift_strictAnti A B hh hΔ
    (Nat.le_of_lt hprevN) ht) (by norm_num : (0 : ℝ) ∈ Icc 0 1)
      (by norm_num : (1 : ℝ) ∈ Icc 0 1) (by norm_num : (0 : ℝ) < 1)
  have heq : j - 1 + 1 = j := by omega
  rw [heq] at hstep
  rw [← hstep]
  exact lt_of_lt_of_le hstrict hbound

/-- All source hits in one panel have a unique point at a fixed height, even
when a horizontal rim coefficient vanishes. -/
theorem selectedMaterialHit_samePanel_point (hΔ : Δ A B hh < 0)
    (β : ℝ) (m : ℤ) {i : ℕ} {s₁ s₂ t : ℝ}
    (h₁ : SelectedMaterialHit A B hh hΔ β m i s₁ t)
    (h₂ : SelectedMaterialHit A B hh hΔ β m i s₂ t) :
    (rootStrip A B hh (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point i s₁ t =
      (rootStrip A B hh (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point i s₂ t := by
  have hd₁ := selectedPointPolarLift_decomposition A B hh hΔ h₁.1 h₁.2.1
    ⟨h₁.2.2.1.1.le, h₁.2.2.1.2.le⟩
  have hd₂ := selectedPointPolarLift_decomposition A B hh hΔ h₂.1 h₂.2.1
    ⟨h₂.2.2.1.1.le, h₂.2.2.1.2.le⟩
  have he₁ : FixedBaselinePolarRayGeometry.RayHit
      (rootStrip A B hh (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ))
      (PhysicalMixedTurnSource.circuitPole A B hh
        (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ) (ne_of_lt hΔ))
      (β + 2 * Real.pi * (m : ℝ)) i s₁ t _ :=
    ⟨h₁.2.1, ⟨h₁.2.2.1.1.le, h₁.2.2.1.2.le⟩, hd₁.2, by simpa [h₁.2.2.2] using hd₁.1⟩
  have he₂ : FixedBaselinePolarRayGeometry.RayHit
      (rootStrip A B hh (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ))
      (PhysicalMixedTurnSource.circuitPole A B hh
        (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ) (ne_of_lt hΔ))
      (β + 2 * Real.pi * (m : ℝ)) i s₂ t _ :=
    ⟨h₂.2.1, ⟨h₂.2.2.1.1.le, h₂.2.2.1.2.le⟩, hd₂.2, by simpa [h₂.2.2.2] using hd₂.1⟩
  exact FixedBaselinePolarRayGeometry.ray_point_unique_at_height _ _
    (selectedRoot_radialSupport A B hh hΔ) h₁.1 he₁ he₂

/-- Fixed-height source hits with the same real lift name the same material
point. Different panels can share only their common hinge, not a face interior;
this does not assert disjointness of the closed developed panels. -/
theorem selectedMaterialHit_point_unique (hΔ : Δ A B hh < 0)
    (β : ℝ) (m : ℤ) {i j : ℕ} {s₁ s₂ t : ℝ}
    (h₁ : SelectedMaterialHit A B hh hΔ β m i s₁ t)
    (h₂ : SelectedMaterialHit A B hh hΔ β m j s₂ t) :
    (rootStrip A B hh (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point i s₁ t =
      (rootStrip A B hh (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point j s₂ t := by
  by_cases heq : i = j
  · subst j
    exact selectedMaterialHit_samePanel_point A B hh hΔ β m h₁ h₂
  · have ht := h₁.2.2.1
    have hfixed (a b : ℕ) (x y : ℝ)
        (ha : SelectedMaterialHit A B hh hΔ β m a x t)
        (hb : SelectedMaterialHit A B hh hΔ β m b y t)
        (hab : a < b) :
        (rootStrip A B hh (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point a x t =
          (rootStrip A B hh (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point b y t := by
      have horder := selectedPanel_entries_order A B hh hΔ hab hb.1 ht
      have hleft := (selectedPointPolarLift_strictAnti A B hh hΔ ha.1 ht).antitoneOn
        ha.2.1 (by norm_num : (1 : ℝ) ∈ Icc 0 1) ha.2.1.2
      have hright := (selectedPointPolarLift_strictAnti A B hh hΔ hb.1 ht).antitoneOn
        (by norm_num : (0 : ℝ) ∈ Icc 0 1) hb.2.1 hb.2.1.1
      have hmeet : selectedPointPolarLift A B hh hΔ a 1 t =
          selectedPointPolarLift A B hh hΔ b 0 t := by
        rw [ha.2.2.2] at hleft
        rw [hb.2.2.2] at hright
        exact le_antisymm (le_trans hleft hright) horder.1
      have hadj : b = a + 1 := by
        by_contra hn
        have hfar : a + 1 < b := by omega
        exact (ne_of_gt (horder.2 hfar)) hmeet
      have hx : x = 1 := by
        by_contra hn
        have hlt : x < 1 := lt_of_le_of_ne ha.2.1.2 hn
        have hs := (selectedPointPolarLift_strictAnti A B hh hΔ ha.1 ht)
          ha.2.1 (by norm_num : (1 : ℝ) ∈ Icc 0 1) hlt
        change selectedPointPolarLift A B hh hΔ a 1 t <
          selectedPointPolarLift A B hh hΔ a x t at hs
        rw [ha.2.2.2, hmeet, ← hb.2.2.2] at hs
        exact (not_lt_of_ge hright) hs
      have hy : y = 0 := by
        by_contra hn
        have hlt : (0 : ℝ) < y := lt_of_le_of_ne hb.2.1.1 (Ne.symm hn)
        have hs := (selectedPointPolarLift_strictAnti A B hh hΔ hb.1 ht)
          (by norm_num : (0 : ℝ) ∈ Icc 0 1) hb.2.1 hlt
        change selectedPointPolarLift A B hh hΔ b y t <
          selectedPointPolarLift A B hh hΔ b 0 t at hs
        rw [hb.2.2.2, ← hmeet, ← ha.2.2.2] at hs
        exact (not_lt_of_ge hleft) hs
      subst x
      subst y
      rw [hadj]
      exact selectedRoot_retainedHinge_point A B hh hΔ
        (lt_of_lt_of_le hab hb.1) t
    rcases lt_or_gt_of_ne heq with hij | hji
    · exact hfixed i j s₁ s₂ h₁ h₂ hij
    · exact (hfixed j i s₂ s₁ h₂ h₁ hji).symm

/-- The radius of the actual selected-root hit, defaulting to zero away from
the realized component. The witness is chosen from source material, not from a
glued table of eligible panels. -/
noncomputable def selectedComponentRadius (hΔ : Δ A B hh < 0)
    (β : ℝ) (m : ℤ) (t : ℝ) : ℝ :=
  if ht : t ∈ selectedRayHeightComponent A B hh hΔ β m then
    let i := Classical.choose ht.2
    let s := Classical.choose (Classical.choose_spec ht.2).2
    ‖(rootStrip A B hh
        (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point i s t -
      PhysicalMixedTurnSource.circuitPole A B hh
        (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ) (ne_of_lt hΔ)‖
  else 0

/-- Any actual material witness computes the chosen component radius; in
particular hinge names and singleton-height witnesses give the same radius. -/
theorem selectedComponentRadius_eq_hit (hΔ : Δ A B hh < 0)
    (β : ℝ) (m : ℤ) {i : ℕ} {s t : ℝ}
    (hit : SelectedMaterialHit A B hh hΔ β m i s t) :
    selectedComponentRadius A B hh hΔ β m t =
      ‖(rootStrip A B hh
        (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point i s t -
        PhysicalMixedTurnSource.circuitPole A B hh
          (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ) (ne_of_lt hΔ)‖ := by
  have ht : t ∈ selectedRayHeightComponent A B hh hΔ β m :=
    ⟨hit.2.2.1, i, hit.1, s, hit.2.1, hit.2.2.2⟩
  let j := Classical.choose ht.2
  let y := Classical.choose (Classical.choose_spec ht.2).2
  have hj : SelectedMaterialHit A B hh hΔ β m j y t :=
    ⟨(Classical.choose_spec ht.2).1,
      (Classical.choose_spec (Classical.choose_spec ht.2).2).1,
      ht.1, (Classical.choose_spec (Classical.choose_spec ht.2).2).2⟩
  have hp := selectedMaterialHit_point_unique A B hh hΔ β m hj hit
  simp only [selectedComponentRadius, dite_eq_ite, dif_pos ht]
  exact congrArg (fun p => ‖p - PhysicalMixedTurnSource.circuitPole A B hh
    (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ) (ne_of_lt hΔ)‖) hp

/-- Every realized component radius is positive, including singleton-height
components and hits at radial hinges. -/
theorem selectedComponentRadius_pos (hΔ : Δ A B hh < 0)
    (β : ℝ) (m : ℤ) {t : ℝ}
    (ht : t ∈ selectedRayHeightComponent A B hh hΔ β m) :
    0 < selectedComponentRadius A B hh hΔ β m t := by
  obtain ⟨i, hi, s, hs, he⟩ := ht.2
  have hit : SelectedMaterialHit A B hh hΔ β m i s t :=
    ⟨hi, hs, ht.1, he⟩
  rw [selectedComponentRadius_eq_hit A B hh hΔ β m hit]
  exact (selectedPointPolarLift_decomposition A B hh hΔ hi hs
    ⟨ht.1.1.le, ht.1.2.le⟩).2

/-- At an *actual* ray crossing of a retained hinge the two source names
have equal radius and both compute the same chosen component radius. -/
theorem selectedComponentRadius_hinge (hΔ : Δ A B hh < 0)
    (β : ℝ) (m : ℤ) {i : ℕ} (hi : i < N A B)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (he : selectedPointPolarLift A B hh hΔ i 1 t =
      β + 2 * Real.pi * (m : ℝ)) :
    selectedComponentRadius A B hh hΔ β m t =
        ‖(rootStrip A B hh
          (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point i 1 t -
          PhysicalMixedTurnSource.circuitPole A B hh
            (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ) (ne_of_lt hΔ)‖ ∧
    selectedComponentRadius A B hh hΔ β m t =
        ‖(rootStrip A B hh
          (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point (i + 1) 0 t -
          PhysicalMixedTurnSource.circuitPole A B hh
            (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ) (ne_of_lt hΔ)‖ := by
  have h₁ : SelectedMaterialHit A B hh hΔ β m i 1 t :=
    ⟨hi.le, by norm_num, ht, he⟩
  have h₂ : SelectedMaterialHit A B hh hΔ β m (i + 1) 0 t :=
    ⟨hi, by norm_num, ht,
      (selectedPointPolarLift_hinge A B hh hΔ hi
        ⟨ht.1.le, ht.2.le⟩).symm.trans he⟩
  exact ⟨selectedComponentRadius_eq_hit A B hh hΔ β m h₁,
    selectedComponentRadius_eq_hit A B hh hΔ β m h₂⟩

/-- Strict inwardness on any single actual physical panel; no artificial
positive-length assumption on its rim runs or eligible height interval. -/
theorem selectedComponentRadius_strict_samePanel (hΔ : Δ A B hh < 0)
    (β : ℝ) (m : ℤ) {i : ℕ} {s₁ s₂ t u : ℝ}
    (ht : SelectedMaterialHit A B hh hΔ β m i s₁ t)
    (hu : SelectedMaterialHit A B hh hΔ β m i s₂ u)
    (htu : t < u) :
    selectedComponentRadius A B hh hΔ β m u <
      selectedComponentRadius A B hh hΔ β m t := by
  let S := rootStrip A B hh
    (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)
  let O := PhysicalMixedTurnSource.circuitPole A B hh
    (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ) (ne_of_lt hΔ)
  have hd₁ := selectedPointPolarLift_decomposition A B hh hΔ ht.1 ht.2.1
    ⟨ht.2.2.1.1.le, ht.2.2.1.2.le⟩
  have hd₂ := selectedPointPolarLift_decomposition A B hh hΔ hu.1 hu.2.1
    ⟨hu.2.2.1.1.le, hu.2.2.1.2.le⟩
  have hit₁ : FixedBaselinePolarRayGeometry.RayHit S O
      (β + 2 * Real.pi * (m : ℝ)) i s₁ t ‖S.point i s₁ t - O‖ :=
    ⟨ht.2.1, ⟨ht.2.2.1.1.le, ht.2.2.1.2.le⟩,
      hd₁.2, by simpa only [ht.2.2.2] using hd₁.1⟩
  have hit₂ : FixedBaselinePolarRayGeometry.RayHit S O
      (β + 2 * Real.pi * (m : ℝ)) i s₂ u ‖S.point i s₂ u - O‖ :=
    ⟨hu.2.1, ⟨hu.2.2.1.1.le, hu.2.2.1.2.le⟩,
      hd₂.2, by simpa only [hu.2.2.2] using hd₂.1⟩
  rw [selectedComponentRadius_eq_hit A B hh hΔ β m hu,
    selectedComponentRadius_eq_hit A B hh hΔ β m ht]
  exact FixedBaselinePolarTrace.ray_radius_strictAnti S O
    (selectedRoot_radialSupport A B hh hΔ) ht.1 htu hit₁ hit₂

/-- The closed angular inequalities for one physical panel. Intersecting
this closed set with the open height interval is exactly the actual panel's
material hit set, including hinge and singleton transitions. -/
def selectedPanelHeightClosure (hΔ : Δ A B hh < 0)
    (β : ℝ) (m : ℤ) (i : ℕ) : Set ℝ :=
  {t | t ∈ Icc (0 : ℝ) 1 ∧
    selectedPointPolarLift A B hh hΔ i 1 t ≤ β + 2 * Real.pi * (m : ℝ) ∧
    β + 2 * Real.pi * (m : ℝ) ≤ selectedPointPolarLift A B hh hΔ i 0 t}

theorem selectedPanelHeightClosure_closed (hΔ : Δ A B hh < 0)
    (β : ℝ) (m : ℤ) {i : ℕ} (hi : i ≤ N A B) :
    IsClosed (selectedPanelHeightClosure A B hh hΔ β m i) := by
  have h₁ := selectedPointPolarLift_continuousOn_height A B hh hΔ hi
    (s := 1) (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  have h₀ := selectedPointPolarLift_continuousOn_height A B hh hΔ hi
    (s := 0) (by norm_num : (0 : ℝ) ∈ Icc 0 1)
  have hc₁ : IsClosed (Icc (0 : ℝ) 1 ∩
      (selectedPointPolarLift A B hh hΔ i 1) ⁻¹'
        Iic (β + 2 * Real.pi * (m : ℝ))) :=
    h₁.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hc₀ : IsClosed (Icc (0 : ℝ) 1 ∩
      (selectedPointPolarLift A B hh hΔ i 0) ⁻¹'
        Ici (β + 2 * Real.pi * (m : ℝ))) :=
    h₀.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  convert hc₁.inter hc₀ using 1 <;> ext t <;>
    simp [selectedPanelHeightClosure, and_left_comm, and_assoc]

theorem selectedPanelHeightClosure_iff (hΔ : Δ A B hh < 0)
    (β : ℝ) (m : ℤ) {i : ℕ} (hi : i ≤ N A B) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    t ∈ selectedPanelHeightClosure A B hh hΔ β m i ↔
      ∃ s, SelectedMaterialHit A B hh hΔ β m i s t := by
  have himage := selectedPointPolarLift_image_Icc A B hh hΔ hi ht
  rw [Set.ext_iff] at himage
  have he := himage (β + 2 * Real.pi * (m : ℝ))
  simp only [mem_image, mem_Icc] at he
  change (∃ s ∈ Icc (0 : ℝ) 1,
    selectedPointPolarLift A B hh hΔ i s t = β + 2 * Real.pi * (m : ℝ)) ↔ _ at he
  constructor
  · intro h
    obtain ⟨s, hs, heq⟩ := he.mpr ⟨h.2.1, h.2.2⟩
    exact ⟨s, hi, hs, ht, heq⟩
  · rintro ⟨s, hs⟩
    exact ⟨⟨ht.1.le, ht.2.le⟩, (he.mp ⟨s, hs.2.1, hs.2.2.2⟩).1,
      (he.mp ⟨s, hs.2.1, hs.2.2.2⟩).2⟩

/-- Continuous compatible formulas on a finite relatively closed cover glue
continuously even when the domain itself is an open interval. -/
theorem continuousOn_of_finite_closed_cover {I : Set ℝ} {f : ℝ → ℝ}
    {q : ℕ} (F : Fin q → Set ℝ) (hclosed : ∀ i, IsClosed (F i))
    (hcover : ∀ x ∈ I, ∃ i, x ∈ F i)
    (hcont : ∀ i, ContinuousOn f (I ∩ F i)) : ContinuousOn f I := by
  let G : Fin q → Set I := fun i => {x | (x : ℝ) ∈ F i}
  have hgclosed : ∀ i, IsClosed (G i) := by
    intro i
    exact (hclosed i).preimage continuous_subtype_val
  have hgcont : ∀ i, ContinuousOn (fun x : I => f x.1) (G i) := by
    intro i
    exact (hcont i).comp continuous_subtype_val.continuousOn (by
      intro x hx
      exact ⟨x.property, hx⟩)
  have huniv : (⋃ i, G i) = (Set.univ : Set I) := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    exact hcover x.1 x.property
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hc := (locallyFinite_of_finite G).continuousOn_iUnion hgclosed hgcont
  rw [huniv] at hc
  exact continuousOn_univ.mp hc

/-- Finite closed panel coverage turns strict order on each panel into
strict order immediately to the left of every point. Panels with singleton
height fibers cause no exceptional case. -/
theorem locally_left_of_finite_closed_cover {I : Set ℝ} {f : ℝ → ℝ}
    {q : ℕ} (F : Fin q → Set ℝ) (hclosed : ∀ i, IsClosed (F i))
    (hcover : ∀ x ∈ I, ∃ i, x ∈ F i)
    (hstrict : ∀ i, ∀ {x y}, x ∈ I → y ∈ I →
      x ∈ F i → y ∈ F i → x < y → f y < f x) :
    ∀ x ∈ I, ∃ ε : ℝ, 0 < ε ∧
      ∀ y ∈ I, x - ε < y → y < x → f x < f y := by
  intro x hx
  have hev : ∀ᶠ y in 𝓝 x, ∀ i : Fin q, y ∈ F i → x ∈ F i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hxi : x ∈ F i
    · exact Filter.Eventually.of_forall (fun y hy => hxi)
    · have ho : (F i)ᶜ ∈ 𝓝 x := (hclosed i).isOpen_compl.mem_nhds hxi
      filter_upwards [ho] with y hy hyF
      exact False.elim (hy hyF)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨ε, hε, ?_⟩
  intro y hy hnear hyx
  obtain ⟨i, hi⟩ := hcover y hy
  have hdist : dist y x < ε := by
    rw [Real.dist_eq]
    rw [abs_sub_comm]
    rw [abs_of_nonneg (sub_nonneg.mpr hyx.le)]
    linarith
  exact hstrict i hy hx hi (hball (Metric.mem_ball.mpr hdist) i hi) hyx

/-- Each active panel computes the radius by the fixed-ray affine Cramer
formula. This formula is defined even at parallel panels, which simply have
no material hits. -/
noncomputable def selectedPanelAffineRadius (hΔ : Δ A B hh < 0)
    (β : ℝ) (m : ℤ) (i : ℕ) (t : ℝ) : ℝ :=
  let S := rootStrip A B hh
    (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)
  let O := PhysicalMixedTurnSource.circuitPole A B hh
    (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ) (ne_of_lt hΔ)
  ((1 - t) * MixedTurnSafeCut.det (S.B i - O) (S.v i) +
    t * MixedTurnSafeCut.det (S.B i + S.d i - O) (S.v i)) /
      MixedTurnSafeCut.det (MixedTurnSafeCut.direction
        (β + 2 * Real.pi * (m : ℝ))) (S.v i)

theorem selectedPanelAffineRadius_continuous (hΔ : Δ A B hh < 0)
    (β : ℝ) (m : ℤ) (i : ℕ) :
    Continuous (selectedPanelAffineRadius A B hh hΔ β m i) := by
  unfold selectedPanelAffineRadius
  fun_prop

theorem selectedComponentRadius_eq_affine (hΔ : Δ A B hh < 0)
    (β : ℝ) (m : ℤ) {i : ℕ} {s t : ℝ}
    (hit : SelectedMaterialHit A B hh hΔ β m i s t) :
    selectedComponentRadius A B hh hΔ β m t =
      selectedPanelAffineRadius A B hh hΔ β m i t := by
  let S := rootStrip A B hh
    (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)
  let O := PhysicalMixedTurnSource.circuitPole A B hh
    (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ) (ne_of_lt hΔ)
  have hd := selectedPointPolarLift_decomposition A B hh hΔ hit.1 hit.2.1
    ⟨hit.2.2.1.1.le, hit.2.2.1.2.le⟩
  have rhit : FixedBaselinePolarRayGeometry.RayHit S O
      (β + 2 * Real.pi * (m : ℝ)) i s t ‖S.point i s t - O‖ :=
    ⟨hit.2.1, ⟨hit.2.2.1.1.le, hit.2.2.1.2.le⟩,
      hd.2, by simpa only [hit.2.2.2] using hd.1⟩
  rw [selectedComponentRadius_eq_hit A B hh hΔ β m hit]
  exact FixedBaselinePolarRayGeometry.ray_radius_eq S O
    (selectedRoot_radialSupport A B hh hΔ) hit.1 rhit

/-- A continuous function on an order-convex real set is strictly antitone if
its values strictly decrease immediately to the left of every point. The
compact maximum argument also covers open intervals and singleton sets. -/
theorem continuousOn_strictAntiOn_of_locally_left
    {I : Set ℝ} {f : ℝ → ℝ} (hconv : OrdConnected I)
    (hcont : ContinuousOn f I)
    (hloc : ∀ x ∈ I, ∃ ε : ℝ, 0 < ε ∧
      ∀ y ∈ I, x - ε < y → y < x → f x < f y) :
    StrictAntiOn f I := by
  intro t ht u hu htu
  have hseg : Icc t u ⊆ I := fun x hx => hconv.out ht hu hx
  obtain ⟨x, hx, hmax⟩ := (isCompact_Icc : IsCompact (Icc t u)).exists_isMaxOn
    ⟨t, left_mem_Icc.mpr htu.le⟩ (hcont.mono hseg)
  have hxt : x = t := by
    by_contra hne
    have htx : t < x := lt_of_le_of_ne hx.1 (Ne.symm hne)
    obtain ⟨ε, hε, hlocal⟩ := hloc x (hseg hx)
    let y := max t (x - ε / 2)
    have hyx : y < x := max_lt htx (by linarith)
    have hxy : x - ε < y := by dsimp [y]; have := le_max_right t (x - ε / 2); linarith
    have hy : y ∈ Icc t u := ⟨le_max_left _ _, (hyx.trans_le hx.2).le⟩
    exact (not_lt_of_ge (hmax hy)) (hlocal y (hseg hy) hxy hyx)
  subst x
  have hle : f u ≤ f t := hmax (right_mem_Icc.mpr htu.le)
  obtain ⟨ε, hε, hlocal⟩ := hloc u hu
  let y := max t (u - ε / 2)
  have hyu : y < u := max_lt htu (by linarith)
  have huy : u - ε < y := by dsimp [y]; have := le_max_right t (u - ε / 2); linarith
  have hy : y ∈ Icc t u := ⟨le_max_left _ _, hyu.le⟩
  have hstrict := hlocal y (hseg hy) huy hyu
  exact lt_of_lt_of_le hstrict (hmax hy)

/-- The actual source-chosen radius is continuous on its order-convex
component, by closed finite angular panel coverage and the affine formula on
each active fiber. -/
theorem selectedComponentRadius_continuousOn (hΔ : Δ A B hh < 0)
    (β : ℝ) (m : ℤ) :
    ContinuousOn (selectedComponentRadius A B hh hΔ β m)
      (selectedRayHeightComponent A B hh hΔ β m) := by
  let I := selectedRayHeightComponent A B hh hΔ β m
  let F : Fin (N A B + 1) → Set ℝ := fun i =>
    selectedPanelHeightClosure A B hh hΔ β m i.val
  have hclosed : ∀ i, IsClosed (F i) := fun i =>
    selectedPanelHeightClosure_closed A B hh hΔ β m (by omega)
  have hcover : ∀ x ∈ I, ∃ i, x ∈ F i := by
    intro x hx
    obtain ⟨i, hi, s, hs, he⟩ := hx.2
    refine ⟨⟨i, by omega⟩, ?_⟩
    exact (selectedPanelHeightClosure_iff A B hh hΔ β m hi hx.1).mpr
      ⟨s, hi, hs, hx.1, he⟩
  apply continuousOn_of_finite_closed_cover F hclosed hcover
  intro i
  apply (selectedPanelAffineRadius_continuous A B hh hΔ β m i.val).continuousOn.congr
  intro x hx
  obtain ⟨s, hs⟩ := (selectedPanelHeightClosure_iff A B hh hΔ β m
    (by omega : i.val ≤ N A B) hx.1.1).mp hx.2
  exact selectedComponentRadius_eq_affine A B hh hΔ β m hs

/-- Every actual component point has a left neighborhood whose earlier
heights have strictly larger radii. Finite closed-panel coverage
handles hinge, parallel, and singleton transitions without a glued table. -/
theorem selectedComponentRadius_locally_left (hΔ : Δ A B hh < 0)
    (β : ℝ) (m : ℤ) :
    ∀ x ∈ selectedRayHeightComponent A B hh hΔ β m,
      ∃ ε : ℝ, 0 < ε ∧
        ∀ y ∈ selectedRayHeightComponent A B hh hΔ β m,
          x - ε < y → y < x →
            selectedComponentRadius A B hh hΔ β m x <
              selectedComponentRadius A B hh hΔ β m y := by
  let I := selectedRayHeightComponent A B hh hΔ β m
  let F : Fin (N A B + 1) → Set ℝ := fun i =>
    selectedPanelHeightClosure A B hh hΔ β m i.val
  have hclosed : ∀ i, IsClosed (F i) := fun i =>
    selectedPanelHeightClosure_closed A B hh hΔ β m (by omega)
  have hcover : ∀ x ∈ I, ∃ i, x ∈ F i := by
    intro x hx
    obtain ⟨i, hi, s, hs, he⟩ := hx.2
    refine ⟨⟨i, by omega⟩, ?_⟩
    exact (selectedPanelHeightClosure_iff A B hh hΔ β m hi hx.1).mpr
      ⟨s, hi, hs, hx.1, he⟩
  apply locally_left_of_finite_closed_cover F hclosed hcover
  intro i x y hx hy hxi hyi hxy
  obtain ⟨s, hs⟩ := (selectedPanelHeightClosure_iff A B hh hΔ β m
    (by omega : i.val ≤ N A B) hx.1).mp hxi
  obtain ⟨r, hr⟩ := (selectedPanelHeightClosure_iff A B hh hΔ β m
    (by omega : i.val ≤ N A B) hy.1).mp hyi
  exact selectedComponentRadius_strict_samePanel A B hh hΔ β m hs hr hxy

/-- Strict inward radial order on the entire actual representative component,
including arbitrary changes of selected physical panels. -/
theorem selectedComponentRadius_strict (hΔ : Δ A B hh < 0)
    (β : ℝ) (m : ℤ) {t u : ℝ}
    (ht : t ∈ selectedRayHeightComponent A B hh hΔ β m)
    (hu : u ∈ selectedRayHeightComponent A B hh hΔ β m)
    (htu : t < u) :
    selectedComponentRadius A B hh hΔ β m u <
      selectedComponentRadius A B hh hΔ β m t := by
  apply continuousOn_strictAntiOn_of_locally_left
    (I := selectedRayHeightComponent A B hh hΔ β m)
    (f := selectedComponentRadius A B hh hΔ β m)
  · constructor
    intro x hx y hy z hz
    exact selectedRayHeightComponent_convex A B hh hΔ β m hx hy hz.1 hz.2
  · exact selectedComponentRadius_continuousOn A B hh hΔ β m
  · exact selectedComponentRadius_locally_left A B hh hΔ β m
  · exact ht
  · exact hu
  · exact htu

/-- The two literal facing seam copies compute the chosen physical radius,
not merely a radius on a baseline surrogate. -/
theorem selectedComponentRadius_root_seam (hΔ : Δ A B hh < 0)
    (β : ℝ) (m : ℤ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (he : selectedPointPolarLift A B hh hΔ 0 0 t =
      β + 2 * Real.pi * (m : ℝ)) :
    selectedComponentRadius A B hh hΔ β m t =
      ‖RadialOriginalSeam.selectedNegativeSeamCurve A B hh hΔ t -
        PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)‖ := by
  let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
  rw [selectedComponentRadius_eq_hit A B hh hΔ β m
    (show SelectedMaterialHit A B hh hΔ β m 0 0 t from
      ⟨Nat.zero_le _, by norm_num, ht, he⟩)]
  have hp := PhysicalMixedTurnSource.baselineAlignment_circuitPole
    A B hh k (ne_of_lt hΔ)
  have hs := selectedNegativeRoot_seam_alignment A B hh hΔ t
  rw [← hp, ← hs]
  have hn := congrArg norm ((PhysicalMixedTurnSource.baselineAlignment A B hh k).map_vsub
    ((rootStrip A B hh k).point 0 0 t)
    (PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_lt hΔ)))
  rw [(PhysicalMixedTurnSource.baselineAlignment A B hh k).linearIsometry.norm_map] at hn
  simpa only [vsub_eq_sub] using hn

/-- The actual terminal panel endpoint, including a wrapped panel, has the
radius of the literal full-circuit seam copy. -/
theorem selectedComponentRadius_terminal_seam (hΔ : Δ A B hh < 0)
    (β : ℝ) (m : ℤ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (he : selectedPointPolarLift A B hh hΔ (N A B) 1 t =
      β + 2 * Real.pi * (m : ℝ)) :
    selectedComponentRadius A B hh hΔ β m t =
      ‖RadialOriginalSeam.selectedNegativeTerminalSeamCurve A B hh hΔ t -
        PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)‖ := by
  let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
  rw [selectedComponentRadius_eq_hit A B hh hΔ β m
    (show SelectedMaterialHit A B hh hΔ β m (N A B) 1 t from
      ⟨le_refl _, by norm_num, ht, he⟩)]
  have hv := selectedRoot_virtualFinalHinge A B hh hΔ t
  have hp := PhysicalMixedTurnSource.baselineAlignment_circuitPole
    A B hh k (ne_of_lt hΔ)
  have hs := selectedNegativeRoot_terminal_alignment A B hh hΔ t
  rw [hv]
  rw [← hp, ← hs]
  have hn := congrArg norm ((PhysicalMixedTurnSource.baselineAlignment A B hh k).map_vsub
    (PhysicalMixedTurnSource.fullCircuit A B hh k ((rootStrip A B hh k).point 0 0 t))
    (PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_lt hΔ)))
  rw [(PhysicalMixedTurnSource.baselineAlignment A B hh k).linearIsometry.norm_map] at hn
  simpa only [vsub_eq_sub] using hn

/-- Arbitrary physical hits on consecutive real representatives have a
strict radius gap, in either possible seam-angle orientation. The comparison
passes through realized facing endpoints, then uses global component order. -/
theorem selectedComponentRadius_cross_strict (hΔ : Δ A B hh < 0)
    (β : ℝ) {m₁ m₂ : ℤ} (hm : m₁ < m₂)
    {t u : ℝ} (ht : t ∈ selectedRayHeightComponent A B hh hΔ β m₁)
    (hu : u ∈ selectedRayHeightComponent A B hh hΔ β m₂) :
    selectedComponentRadius A B hh hΔ β m₂ u <
        selectedComponentRadius A B hh hΔ β m₁ t ∨
      selectedComponentRadius A B hh hΔ β m₁ t <
        selectedComponentRadius A B hh hΔ β m₂ u := by
  have hnext := selectedRayHeightComponent_consecutive A B hh hΔ β hm
    ⟨t, ht⟩ ⟨u, hu⟩
  rcases selectedAlpha_det_trichotomy A B hh hΔ with hmono | hanti | hconst
  · obtain ⟨b, c, htb, hbc, hcu, hb, hc, hbe, hce, hgap⟩ :=
      selectedRayHeightComponent_facing_radius_of_mono A B hh hΔ β hnext hmono ht hu
    have hface : selectedComponentRadius A B hh hΔ β m₂ c <
        selectedComponentRadius A B hh hΔ β m₁ b := by
      rw [selectedComponentRadius_root_seam A B hh hΔ β m₂ hc.1 hce,
        selectedComponentRadius_terminal_seam A B hh hΔ β m₁ hb.1 hbe]
      exact hgap
    have hleft : selectedComponentRadius A B hh hΔ β m₁ b ≤
        selectedComponentRadius A B hh hΔ β m₁ t := by
      rcases htb.eq_or_lt with heq | hlt
      · rw [← heq]
      · exact (selectedComponentRadius_strict A B hh hΔ β m₁ ht hb hlt).le
    have hright : selectedComponentRadius A B hh hΔ β m₂ u ≤
        selectedComponentRadius A B hh hΔ β m₂ c := by
      rcases hcu.eq_or_lt with heq | hlt
      · rw [heq]
      · exact (selectedComponentRadius_strict A B hh hΔ β m₂ hc hu hlt).le
    exact Or.inl (lt_of_le_of_lt hright (lt_of_lt_of_le hface hleft))
  · obtain ⟨b, c, hub, hbc, hct, hb, hc, hbe, hce, hgap⟩ :=
      selectedRayHeightComponent_facing_radius_of_anti A B hh hΔ β hnext hanti hu ht
    have hface : selectedComponentRadius A B hh hΔ β m₁ c <
        selectedComponentRadius A B hh hΔ β m₂ b := by
      rw [selectedComponentRadius_terminal_seam A B hh hΔ β m₁ hc.1 hce,
        selectedComponentRadius_root_seam A B hh hΔ β m₂ hb.1 hbe]
      exact hgap
    have hleft : selectedComponentRadius A B hh hΔ β m₂ b ≤
        selectedComponentRadius A B hh hΔ β m₂ u := by
      rcases hub.eq_or_lt with heq | hlt
      · rw [← heq]
      · exact (selectedComponentRadius_strict A B hh hΔ β m₂ hu hb hlt).le
    have hright : selectedComponentRadius A B hh hΔ β m₁ t ≤
        selectedComponentRadius A B hh hΔ β m₁ c := by
      rcases hct.eq_or_lt with heq | hlt
      · rw [heq]
      · exact (selectedComponentRadius_strict A B hh hΔ β m₁ hc ht hlt).le
    exact Or.inr (lt_of_le_of_lt hright (lt_of_lt_of_le hface hleft))
  · have heq := selectedRayHeightComponent_constant_unique A B hh hΔ β
      (by
        intro x hx
        rw [hconst x ⟨hx.1.le, hx.2.le⟩,
          hconst (1 / 2) (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)])
      ⟨t, ht⟩ ⟨u, hu⟩
    omega

/-- No two physical material hits on a fixed positive planar ray can
identify in the development at different physical heights. This includes
all panels, singleton components, and both directions of the seam lift. -/
theorem selectedMaterialHit_point_ne_of_height_ne (hΔ : Δ A B hh < 0)
    (β : ℝ) {m₁ m₂ : ℤ} {i j : ℕ} {s₁ s₂ t u : ℝ}
    (h₁ : SelectedMaterialHit A B hh hΔ β m₁ i s₁ t)
    (h₂ : SelectedMaterialHit A B hh hΔ β m₂ j s₂ u)
    (htu : t ≠ u) :
    (rootStrip A B hh (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point i s₁ t ≠
      (rootStrip A B hh (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point j s₂ u := by
  have ht : t ∈ selectedRayHeightComponent A B hh hΔ β m₁ :=
    ⟨h₁.2.2.1, i, h₁.1, s₁, h₁.2.1, h₁.2.2.2⟩
  have hu : u ∈ selectedRayHeightComponent A B hh hΔ β m₂ :=
    ⟨h₂.2.2.1, j, h₂.1, s₂, h₂.2.1, h₂.2.2.2⟩
  have hr : selectedComponentRadius A B hh hΔ β m₁ t ≠
      selectedComponentRadius A B hh hΔ β m₂ u := by
    by_cases hm : m₁ = m₂
    · subst m₂
      rcases lt_or_gt_of_ne htu with hlt | hgt
      · exact ne_of_gt (selectedComponentRadius_strict A B hh hΔ β m₁ ht hu hlt)
      · exact ne_of_lt (selectedComponentRadius_strict A B hh hΔ β m₁ hu ht hgt)
    · rcases lt_or_gt_of_ne hm with hlt | hgt
      · rcases selectedComponentRadius_cross_strict A B hh hΔ β hlt ht hu with h | h
        · exact ne_of_gt h
        · exact ne_of_lt h
      · rcases selectedComponentRadius_cross_strict A B hh hΔ β hgt hu ht with h | h
        · exact ne_of_lt h
        · exact ne_of_gt h
  rw [selectedComponentRadius_eq_hit A B hh hΔ β m₁ h₁,
    selectedComponentRadius_eq_hit A B hh hΔ β m₂ h₂] at hr
  intro heq
  exact hr (congrArg (fun p => ‖p - PhysicalMixedTurnSource.circuitPole A B hh
    (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ) (ne_of_lt hΔ)‖) heq)

/-- At equal height, the real representative is unique (by the strict
sub-full-turn longitudinal window), and all panel names describe one point. -/
theorem selectedMaterialHit_sameHeight (hΔ : Δ A B hh < 0)
    (β : ℝ) {m₁ m₂ : ℤ} {i j : ℕ} {s₁ s₂ t : ℝ}
    (h₁ : SelectedMaterialHit A B hh hΔ β m₁ i s₁ t)
    (h₂ : SelectedMaterialHit A B hh hΔ β m₂ j s₂ t) :
    m₁ = m₂ ∧
      (rootStrip A B hh (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point i s₁ t =
        (rootStrip A B hh (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point j s₂ t := by
  have hm := selectedRayHeightComponent_sameHeight_unique A B hh hΔ β
    (show t ∈ selectedRayHeightComponent A B hh hΔ β m₁ from
      ⟨h₁.2.2.1, i, h₁.1, s₁, h₁.2.1, h₁.2.2.2⟩)
    (show t ∈ selectedRayHeightComponent A B hh hΔ β m₂ from
      ⟨h₂.2.2.1, j, h₂.1, s₂, h₂.2.1, h₂.2.2.2⟩)
  subst m₂
  exact ⟨rfl, selectedMaterialHit_point_unique A B hh hΔ β m₁ h₁ h₂⟩

/-- Two distinct face names at the same physical height and ray can meet
only at their common retained hinge; in particular two face-interior hits
cannot coincide. -/
theorem selectedMaterialHit_sameHeight_hinge (hΔ : Δ A B hh < 0)
    (β : ℝ) {m₁ m₂ : ℤ} {i j : ℕ} {s₁ s₂ t : ℝ}
    (h₁ : SelectedMaterialHit A B hh hΔ β m₁ i s₁ t)
    (h₂ : SelectedMaterialHit A B hh hΔ β m₂ j s₂ t) :
    i = j ∨ (j = i + 1 ∧ s₁ = 1 ∧ s₂ = 0) ∨
      (i = j + 1 ∧ s₂ = 1 ∧ s₁ = 0) := by
  have hm := (selectedMaterialHit_sameHeight A B hh hΔ β h₁ h₂).1
  subst m₂
  by_cases hij : i = j
  · exact Or.inl hij
  have hforward (a b : ℕ) (x y : ℝ)
      (ha : SelectedMaterialHit A B hh hΔ β m₁ a x t)
      (hb : SelectedMaterialHit A B hh hΔ β m₁ b y t)
      (hab : a < b) : b = a + 1 ∧ x = 1 ∧ y = 0 := by
    have horder := selectedPanel_entries_order A B hh hΔ hab hb.1 ha.2.2.1
    have hleft := (selectedPointPolarLift_strictAnti A B hh hΔ ha.1 ha.2.2.1).antitoneOn
      ha.2.1 (by norm_num : (1 : ℝ) ∈ Icc 0 1) ha.2.1.2
    have hright := (selectedPointPolarLift_strictAnti A B hh hΔ hb.1 hb.2.2.1).antitoneOn
      (by norm_num : (0 : ℝ) ∈ Icc 0 1) hb.2.1 hb.2.1.1
    have hmeet : selectedPointPolarLift A B hh hΔ a 1 t =
        selectedPointPolarLift A B hh hΔ b 0 t := by
      rw [ha.2.2.2] at hleft
      rw [hb.2.2.2] at hright
      exact le_antisymm (le_trans hleft hright) horder.1
    have hadj : b = a + 1 := by
      by_contra hn
      have hfar : a + 1 < b := by omega
      exact (ne_of_gt (horder.2 hfar)) hmeet
    have hx : x = 1 := by
      by_contra hn
      have hlt : x < 1 := lt_of_le_of_ne ha.2.1.2 hn
      have hs := (selectedPointPolarLift_strictAnti A B hh hΔ ha.1 ha.2.2.1)
        ha.2.1 (by norm_num : (1 : ℝ) ∈ Icc 0 1) hlt
      change selectedPointPolarLift A B hh hΔ a 1 t <
        selectedPointPolarLift A B hh hΔ a x t at hs
      rw [ha.2.2.2, hmeet, ← hb.2.2.2] at hs
      exact (not_lt_of_ge hright) hs
    have hy : y = 0 := by
      by_contra hn
      have hlt : (0 : ℝ) < y := lt_of_le_of_ne hb.2.1.1 (Ne.symm hn)
      have hs := (selectedPointPolarLift_strictAnti A B hh hΔ hb.1 hb.2.2.1)
        (by norm_num : (0 : ℝ) ∈ Icc 0 1) hb.2.1 hlt
      change selectedPointPolarLift A B hh hΔ b y t <
        selectedPointPolarLift A B hh hΔ b 0 t at hs
      rw [hb.2.2.2, ← hmeet, ← ha.2.2.2] at hs
      exact (not_lt_of_ge hleft) hs
    exact ⟨hadj, hx, hy⟩
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact Or.inr (Or.inl (hforward i j s₁ s₂ h₁ h₂ hlt))
  · exact Or.inr (Or.inr (hforward j i s₂ s₁ h₂ h₁ hgt))

/-- Collision classification for arbitrary physical hits on one ray: equal
height, one real representative, and either one face or a shared hinge. -/
theorem selectedMaterialHit_collision_classification (hΔ : Δ A B hh < 0)
    (β : ℝ) {m₁ m₂ : ℤ} {i j : ℕ} {s₁ s₂ t u : ℝ}
    (h₁ : SelectedMaterialHit A B hh hΔ β m₁ i s₁ t)
    (h₂ : SelectedMaterialHit A B hh hΔ β m₂ j s₂ u)
    (heq : (rootStrip A B hh (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point i s₁ t =
      (rootStrip A B hh (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point j s₂ u) :
    t = u ∧ m₁ = m₂ ∧
      (i = j ∨ (j = i + 1 ∧ s₁ = 1 ∧ s₂ = 0) ∨
        (i = j + 1 ∧ s₂ = 1 ∧ s₁ = 0)) := by
  have htu : t = u := by
    by_contra hn
    exact (selectedMaterialHit_point_ne_of_height_ne A B hh hΔ β h₁ h₂ hn) heq
  subst u
  exact ⟨rfl, (selectedMaterialHit_sameHeight A B hh hΔ β h₁ h₂).1,
    selectedMaterialHit_sameHeight_hinge A B hh hΔ β h₁ h₂⟩

/-- Face-interior hits in distinct faces are disjoint, without a seam-order
or positive-height-gap hypothesis. -/
theorem selectedMaterialHit_distinct_faceInteriors_ne (hΔ : Δ A B hh < 0)
    (β : ℝ) {m₁ m₂ : ℤ} {i j : ℕ} {s₁ s₂ t u : ℝ}
    (h₁ : SelectedMaterialHit A B hh hΔ β m₁ i s₁ t)
    (h₂ : SelectedMaterialHit A B hh hΔ β m₂ j s₂ u)
    (hi : i ≠ j) (hs₁ : s₁ ∈ Ioo (0 : ℝ) 1)
    (hs₂ : s₂ ∈ Ioo (0 : ℝ) 1) :
    (rootStrip A B hh (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point i s₁ t ≠
      (rootStrip A B hh (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point j s₂ u := by
  intro heq
  obtain ⟨_, _, hfaces⟩ := selectedMaterialHit_collision_classification A B hh hΔ β h₁ h₂ heq
  rcases hfaces with heq | hforward | hbackward
  · exact hi heq
  · exact (ne_of_lt hs₁.2) hforward.2.1
  · exact (ne_of_lt hs₂.2) hbackward.2.1

#print axioms selectedComponentRadius_strict
#check selectedMaterialHit_point_ne_of_height_ne
#print axioms selectedMaterialHit_point_ne_of_height_ne
#print axioms selectedComponentRadius_cross_strict
#print axioms selectedMaterialHit_sameHeight
#print axioms selectedMaterialHit_sameHeight_hinge
#print axioms selectedMaterialHit_collision_classification
#print axioms selectedMaterialHit_distinct_faceInteriors_ne
#print axioms selectedComponentRadius_continuousOn
#print axioms selectedComponentRadius_locally_left
#print axioms continuousOn_strictAntiOn_of_locally_left
#check selectedRayHeightComponent_crossComponent_seam_allPairs_ne
#check selectedMaterialHit_point_unique
#check selectedComponentRadius_strict_samePanel
#print axioms selectedComponentRadius_strict_samePanel
#print axioms selectedComponentRadius_hinge
#print axioms selectedComponentRadius_pos
#check selectedComponentRadius_eq_hit
#print axioms selectedComponentRadius_eq_hit
#print axioms selectedMaterialHit_point_unique
#print axioms selectedRayHeightComponent_crossComponent_seam_allPairs_ne
#check selectedRayHeightComponent_facing_radius_of_mono
#check selectedRayHeightComponent_facing_radius_of_anti
#print axioms selectedRayHeightComponent_facing_radius_of_mono
#print axioms selectedRayHeightComponent_facing_radius_of_anti
#check selectedRayHeightComponent_facing_of_mono
#check selectedRayHeightComponent_facing_of_anti
#print axioms selectedRayHeightComponent_facing_of_mono
#print axioms selectedRayHeightComponent_facing_of_anti

-- Source-level uses of both seam-angle orders and of the zero-variation case.
example (hΔ : Δ A B hh < 0) (β : ℝ)
    (hα : MonotoneOn (selectedAlpha A B hh hΔ) (Icc (0 : ℝ) 1))
    {m₁ m₂ : ℤ} (hm : m₁ < m₂) {t u : ℝ}
    (ht : t ∈ selectedRayHeightComponent A B hh hΔ β m₁)
    (hu : u ∈ selectedRayHeightComponent A B hh hΔ β m₂) : t < u :=
  selectedRayHeightComponent_order_of_mono A B hh hΔ β hα hm ht hu

example (hΔ : Δ A B hh < 0) (β : ℝ)
    (hα : AntitoneOn (selectedAlpha A B hh hΔ) (Icc (0 : ℝ) 1))
    {m₁ m₂ : ℤ} (hm : m₁ < m₂) {t u : ℝ}
    (ht : t ∈ selectedRayHeightComponent A B hh hΔ β m₁)
    (hu : u ∈ selectedRayHeightComponent A B hh hΔ β m₂) : u < t :=
  selectedRayHeightComponent_order_of_anti A B hh hΔ β hα hm ht hu

example (hΔ : Δ A B hh < 0) (β : ℝ)
    (hα : ∀ t ∈ Ioo (0 : ℝ) 1,
      selectedAlpha A B hh hΔ t = selectedAlpha A B hh hΔ (1 / 2))
    {m₁ m₂ : ℤ}
    (h₁ : (selectedRayHeightComponent A B hh hΔ β m₁).Nonempty)
    (h₂ : (selectedRayHeightComponent A B hh hΔ β m₂).Nonempty) : m₁ = m₂ :=
  selectedRayHeightComponent_constant_unique A B hh hΔ β hα h₁ h₂

#check selectedAlpha_det_trichotomy
#check selectedAlpha_strictMono_of_det_pos
#check selectedAlpha_strictAnti_of_det_neg
#check selectedRayHeightComponent_order_of_det_pos
#check selectedRayHeightComponent_order_of_det_neg
#print axioms selectedAlpha_strictMono_of_det_pos
#print axioms selectedAlpha_strictAnti_of_det_neg
#print axioms selectedRayHeightComponent_order_of_det_pos
#print axioms selectedRayHeightComponent_order_of_det_neg
#check selectedRayHeightComponent_convex
#check selectedRayHeightComponent_relativelyClosed
#check selectedRayHeightComponent_order
#print axioms selectedAlpha_det_trichotomy
#print axioms selectedRayHeightComponent_convex
#print axioms selectedRayHeightComponent_relativelyClosed
#print axioms selectedRayHeightComponent_order
#check selectedRayHeightComponent_convex_of_mono
#check selectedRayHeightComponent_convex_of_anti
#check selectedRayHeightComponent_sameHeight_unique
#check selectedRayHeightComponent_constant_unique
#print axioms selectedRayHeightComponent_sameHeight_unique
#print axioms selectedRayHeightComponent_convex_of_mono
#print axioms selectedRayHeightComponent_convex_of_anti
#print axioms selectedRayHeightComponent_constant_unique
#check selectedRayHeightComponent_iff
#check selectedRayHeightComponent_iff_positiveRay
#check selectedAlpha_continuousOn
#check selectedRayHeightComponent_no_three
#check selectedRayHeightComponent_consecutive
#check selectedRayHeightComponent_order_of_mono
#check selectedRayHeightComponent_order_of_anti
#print axioms selectedRayHeightComponent_iff
#print axioms selectedRayHeightComponent_iff_positiveRay
#print axioms selectedAlpha_continuousOn
#print axioms selectedRayHeightComponent_no_three
#print axioms selectedRayHeightComponent_consecutive
#print axioms selectedRayHeightComponent_order_of_mono
#print axioms selectedRayHeightComponent_order_of_anti
#check selectedPointPolarLift
#check selectedPointPolarLift_decomposition
#check selectedPointPolarLift_mem_window
#check selectedRoot_retainedHinge_point
#check selectedPointPolarLift_hinge
#check selectedRoot_virtualFinalHinge
#check selectedPointPolarLift_terminal
#check selectedLongitudinalLiftSet_eq_Icc
#print axioms selectedPointPolarLift_decomposition
#print axioms selectedPointPolarLift_mem_window
#print axioms selectedRoot_retainedHinge_point
#print axioms selectedPointPolarLift_hinge
#print axioms selectedRoot_virtualFinalHinge
#print axioms selectedPointPolarLift_terminal
#print axioms selectedLongitudinalLiftSet_eq_Icc

end
end SelectedNegativeRootPolar
