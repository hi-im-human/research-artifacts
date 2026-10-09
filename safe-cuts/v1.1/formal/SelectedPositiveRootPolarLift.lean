import SelectedNegativeRootPolarLift
import SelectedRootInteriorWitness

open Set
open scoped BigOperators Classical NNReal
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CommonSupportMerge OriginalFacetCertificates NormalFanSplice MaximalSupportCells
open CyclicCutOrders EuclideanPrismatoidCoordinates PolyhedralInputBridge
open TrimmedFacetWitnesses BandGeometryAssembly FiniteWitnessClosure SingleCutRecovery
open CutSurfaceQuotient MixedTurnSafeCut PolygonSetReconstruction ConvexPolygonTurning
open FixedBaselinePolarRayGeometry SelectedNegativeRootPolar

namespace SelectedPositiveRootPolarLift
noncomputable section
set_option maxHeartbeats 8000000

variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

abbrev Plane := MixedTurnSafeCut.Plane
private abbrev N := PhysicalMixedTurnSource.MechanismN A B
private abbrev Δ := PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh)

/-- The selector is a physical cyclic root, with no trimming-dependent index. -/
noncomputable def positiveRoot (hΔ : 0 < Δ A B hh) : Fin (N A B + 1) :=
  (RadialOriginalSeam.selectedPositiveSeam A B hh hΔ).index

noncomputable def normalizedStrip (hΔ : 0 < Δ A B hh) :
    RadialExtremalSafety.TriangularRadialStrip (N A B) :=
  (rootStrip A B hh (positiveRoot A B hh hΔ)).reflectSwap

noncomputable def normalizedPole (hΔ : 0 < Δ A B hh) : Plane :=
  RadialExtremalSafety.reflectPlane
    (PhysicalMixedTurnSource.circuitPole A B hh (positiveRoot A B hh hΔ)
      (ne_of_gt hΔ))

/-- Pointwise normalization keeps panel and longitudinal coordinates and reverses height. -/
theorem normalized_point (hΔ : 0 < Δ A B hh)
    (i : ℕ) (s t : ℝ) :
    (normalizedStrip A B hh hΔ).point i s (1 - t) =
      RadialExtremalSafety.reflectPlane
        ((rootStrip A B hh (positiveRoot A B hh hΔ)).point i s t) := by
  simp only [normalizedStrip,
    RadialExtremalSafety.TriangularRadialStrip.reflectSwap_point]
  congr 1 <;> ring

/-- An arbitrary root's positive RF support includes wrapped panels.  The
wrapped case is transported by the affine full circuit fixing the true pole. -/
theorem root_positive_support (hΔ : 0 < Δ A B hh)
    (k : Fin (N A B + 1)) :
    (rootStrip A B hh k).PositiveRadialSupport
      (PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_gt hΔ)) := by
  intro i hi
  let O := PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ)
  let H := PhysicalMixedTurnSource.fullCircuit A B hh 0
  let R := PhysicalMixedTurnSource.planeRotation (Δ A B hh)
  have hbase : 0 < MixedTurnSafeCut.det
        (PhysicalMixedTurnSource.developedLower A B hh 0 (k.val + i) - O)
        (PhysicalMixedTurnSource.developedForward A B hh 0 (k.val + i)) ∧
      0 < MixedTurnSafeCut.det
        (PhysicalMixedTurnSource.developedUpper A B hh 0 (k.val + i) - O)
        (PhysicalMixedTurnSource.developedForward A B hh 0 (k.val + i)) := by
    by_cases hfirst : k.val + i < N A B + 1
    · have hk := PhysicalMixedTurnSource.baseline_physical_positive_RF A B hh hΔ
        (⟨k.val + i, hfirst⟩ : Fin (N A B + 1))
      exact ⟨hk.1, hk.2⟩
    · let j := k.val + i - (N A B + 1)
      have hj : j < N A B + 1 := by
        have hk := k.isLt
        change i ≤ PhysicalMixedTurnSource.MechanismN A B at hi
        change k.val < PhysicalMixedTurnSource.MechanismN A B + 1 at hk
        change k.val + i - (PhysicalMixedTurnSource.MechanismN A B + 1) <
          PhysicalMixedTurnSource.MechanismN A B + 1
        omega
      have heq : k.val + i = N A B + 1 + j := by
        dsimp [j]
        omega
      have hshift : PhysicalMixedTurnSource.developedForward A B hh 0
          (N A B + 1 + j) =
          R (PhysicalMixedTurnSource.developedForward A B hh 0 j) := by
        rw [PhysicalMixedTurnSource.developedForward,
          PhysicalMixedTurnSource.developedForward,
          PhysicalMixedTurnSource.baseline_familyHeading_full_add,
          PhysicalMixedTurnSource.planeRotation_comp]
      have hp : H O = O :=
        PhysicalMixedTurnSource.circuitPole_fixed A B hh 0 (ne_of_gt hΔ)
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
      have hk := PhysicalMixedTurnSource.baseline_physical_positive_RF A B hh hΔ
        (⟨j, hj⟩ : Fin (N A B + 1))
      rw [heq, PhysicalMixedTurnSource.baseline_developedLower_fullCircuit,
        PhysicalMixedTurnSource.baseline_developedUpper_fullCircuit, hshift]
      exact ⟨hdet _ ▸ hk.1, hdet _ ▸ hk.2⟩
  have htransport (Y : Plane) : MixedTurnSafeCut.det
      (PhysicalMixedTurnSource.baselineAlignment A B hh k Y - O)
      (PhysicalMixedTurnSource.developedForward A B hh 0 (k.val + i)) =
      MixedTurnSafeCut.det
        (Y - PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_gt hΔ))
        (PhysicalMixedTurnSource.developedForward A B hh k i) := by
    dsimp only [O]
    rw [← PhysicalMixedTurnSource.baselineAlignment_circuitPole A B hh k (ne_of_gt hΔ),
      ← PhysicalMixedTurnSource.baselineAlignment_developedForward A B hh k i]
    exact PhysicalMixedTurnSource.baselineAlignment_det A B hh k _ _ _
  have hl := htransport (PhysicalMixedTurnSource.developedLower A B hh k i)
  have hu := htransport (PhysicalMixedTurnSource.developedUpper A B hh k i)
  rw [PhysicalMixedTurnSource.baselineAlignment_developedLower] at hl
  rw [PhysicalMixedTurnSource.baselineAlignment_developedUpper] at hu
  have hresult := And.intro (hl ▸ hbase.1) (hu ▸ hbase.2)
  simpa only [rootStrip, add_sub_cancel] using hresult

/-- Strict negative support on every normalized source panel, even beyond the
baseline's first-sheet terminal index. -/
theorem normalized_radialSupport (hΔ : 0 < Δ A B hh) :
    (normalizedStrip A B hh hΔ).RadialSupport
      (normalizedPole A B hh hΔ) :=
  RadialExtremalSafety.TriangularRadialStrip.reflectSwap_radialSupport
    (root_positive_support A B hh hΔ (positiveRoot A B hh hΔ))

/-- Reflection reverses the actual real heading, not just its angle class. -/
noncomputable def normalizedHeading (hΔ : 0 < Δ A B hh) (i : ℕ) : ℝ :=
  -rootHeading A B hh (positiveRoot A B hh hΔ) i

theorem normalizedHeading_terminal (hΔ : 0 < Δ A B hh) :
    normalizedHeading A B hh hΔ (N A B + 1) = -Δ A B hh := by
  simp only [normalizedHeading, rootHeading_terminal]

theorem normalizedHeading_terminal_neg (hΔ : 0 < Δ A B hh) :
    normalizedHeading A B hh hΔ (N A B + 1) < 0 := by
  rw [normalizedHeading_terminal]
  linarith

/-- The normalized forward ray has the reflected real heading exactly. -/
theorem normalizedForward_eq_direction (hΔ : 0 < Δ A B hh) (i : ℕ) :
    (normalizedStrip A B hh hΔ).v i =
      MixedTurnSafeCut.direction (normalizedHeading A B hh hΔ i) := by
  change RadialExtremalSafety.reflectPlane
      (PhysicalMixedTurnSource.developedForward A B hh (positiveRoot A B hh hΔ) i) =
    MixedTurnSafeCut.direction (-rootHeading A B hh (positiveRoot A B hh hΔ) i)
  rw [SelectedNegativeRootPolar.rootForward_eq_direction A B hh
    (positiveRoot A B hh hΔ) i]
  ext j
  fin_cases j <;> simp [RadialExtremalSafety.reflectPlane,
    MixedTurnSafeCut.direction, Real.cos_neg, Real.sin_neg]

/-- Actual real polar branch computed at the normalized physical point. -/
noncomputable def pointPolarLift (hΔ : 0 < Δ A B hh)
    (i : ℕ) (s t : ℝ) : ℝ :=
  normalizedHeading A B hh hΔ i + Complex.arg
    (panelRelativeComplex (normalizedHeading A B hh hΔ i)
      ((normalizedStrip A B hh hΔ).point i s t - normalizedPole A B hh hΔ))

/-- Radial support places every point strictly inside its physical heading window. -/
theorem pointPolarLift_window (hΔ : 0 < Δ A B hh)
    {i : ℕ} (hi : i ≤ N A B) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    normalizedHeading A B hh hΔ i < pointPolarLift A B hh hΔ i s t ∧
    pointPolarLift A B hh hΔ i s t <
      normalizedHeading A B hh hΔ i + Real.pi := by
  let S := normalizedStrip A B hh hΔ
  let O := normalizedPole A B hh hΔ
  let θ := normalizedHeading A B hh hΔ i
  let w := panelRelativeComplex θ (S.point i s t - O)
  have hsupp := RadialExtremalSafety.TriangularRadialStrip.support_point
    (normalized_radialSupport A B hh hΔ) hi hs ht
  have him : 0 < w.im := by
    rw [show w.im = MixedTurnSafeCut.det
      (MixedTurnSafeCut.direction θ) (S.point i s t - O) by
        simp [w, panelRelativeComplex_im]]
    rw [← normalizedForward_eq_direction A B hh hΔ i]
    have hanti : MixedTurnSafeCut.det (S.v i) (S.point i s t - O) =
      -MixedTurnSafeCut.det (S.point i s t - O) (S.v i) := by
        simp [MixedTurnSafeCut.det]; ring
    rw [hanti]
    exact neg_pos.mpr hsupp
  have harg0 : 0 < Complex.arg w := by
    have hnonneg : 0 ≤ Complex.arg w := Complex.arg_nonneg_iff.2 him.le
    exact lt_of_le_of_ne hnonneg (by
      intro he
      have hz := Complex.arg_eq_zero_iff.mp he.symm
      linarith [hz.2])
  have hargpi : Complex.arg w < Real.pi :=
    Complex.arg_lt_pi_iff.2 (Or.inr (ne_of_gt him))
  simpa [pointPolarLift, S, O, θ, w] using ⟨harg0, hargpi⟩

/-- Algebraic polar reconstruction independent of the sign of the original
source defect.  Its nonzero radius is certified by normalized radial support. -/
theorem pointPolarLift_decomposition (hΔ : 0 < Δ A B hh)
    {i : ℕ} (hi : i ≤ N A B) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    let z := (normalizedStrip A B hh hΔ).point i s t - normalizedPole A B hh hΔ
    z = ‖z‖ • MixedTurnSafeCut.direction (pointPolarLift A B hh hΔ i s t) ∧
      0 < ‖z‖ := by
  let S := normalizedStrip A B hh hΔ
  let O := normalizedPole A B hh hΔ
  let z := S.point i s t - O
  let θ := normalizedHeading A B hh hΔ i
  let w := panelRelativeComplex θ z
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr
    (RadialExtremalSafety.TriangularRadialStrip.point_ne_pole
      (normalized_radialSupport A B hh hΔ) hi hs ht))
  have hnorm : ‖w‖ = ‖z‖ := by
    simp only [Complex.norm_def, Complex.normSq_apply, w, panelRelativeComplex,
      EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
    congr 1
    calc
      _ = (Real.cos θ ^ 2 + Real.sin θ ^ 2) *
          (z 0 ^ 2 + z 1 ^ 2) := by ring
      _ = _ := by rw [add_comm, Real.sin_sq_add_cos_sq, one_mul]
  have hcos := Complex.norm_mul_cos_arg w
  have hsin := Complex.norm_mul_sin_arg w
  change ‖w‖ * Real.cos (Complex.arg w) = w.re at hcos
  change ‖w‖ * Real.sin (Complex.arg w) = w.im at hsin
  refine ⟨?_, hpos⟩
  change z = ‖z‖ • MixedTurnSafeCut.direction (θ + Complex.arg w)
  rw [← hnorm]
  ext j
  fin_cases j
  · change z 0 = ‖w‖ * Real.cos (θ + Complex.arg w)
    rw [Real.cos_add]
    calc
      z 0 = Real.cos θ * w.re - Real.sin θ * w.im := by
        dsimp [w, panelRelativeComplex]
        symm
        calc
          _ = (Real.cos θ ^ 2 + Real.sin θ ^ 2) * z 0 := by ring
          _ = z 0 := by rw [add_comm, Real.sin_sq_add_cos_sq, one_mul]
      _ = _ := by rw [← hcos, ← hsin]; ring
  · change z 1 = ‖w‖ * Real.sin (θ + Complex.arg w)
    rw [Real.sin_add]
    calc
      z 1 = Real.sin θ * w.re + Real.cos θ * w.im := by
        dsimp [w, panelRelativeComplex]
        symm
        calc
          _ = (Real.cos θ ^ 2 + Real.sin θ ^ 2) * z 1 := by ring
          _ = z 1 := by rw [add_comm, Real.sin_sq_add_cos_sq, one_mul]
      _ = _ := by rw [← hcos, ← hsin]; ring

/-- Neighboring normalized panels have the same point and the same real
polar lift at their physical retained hinge, without quotient jumps. -/
theorem pointPolarLift_hinge (hΔ : 0 < Δ A B hh)
    {i : ℕ} (hi : i < N A B) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    pointPolarLift A B hh hΔ i 1 t =
      pointPolarLift A B hh hΔ (i + 1) 0 t := by
  let S := normalizedStrip A B hh hΔ
  let O := normalizedPole A B hh hΔ
  let x := S.point i 1 t
  have hx : x = S.point (i + 1) 0 t := by
    dsimp [x]
    exact FixedBaselinePolarTrace.point_exit_eq_next_entry S hi t
  have hdec₁ := (pointPolarLift_decomposition A B hh hΔ (i := i) (by omega)
    (s := (1 : ℝ)) (t := t) (by norm_num) ht).1
  have hdec₂ := (pointPolarLift_decomposition A B hh hΔ (i := i + 1) (by omega)
    (s := (0 : ℝ)) (t := t) (by norm_num) ht).1
  change x - O = ‖x - O‖ • MixedTurnSafeCut.direction
    (pointPolarLift A B hh hΔ i 1 t) at hdec₁
  change S.point (i + 1) 0 t - O = ‖S.point (i + 1) 0 t - O‖ •
    MixedTurnSafeCut.direction (pointPolarLift A B hh hΔ (i + 1) 0 t) at hdec₂
  rw [← hx] at hdec₂
  have hr := (pointPolarLift_decomposition A B hh hΔ (i := i) (by omega)
    (s := (1 : ℝ)) (t := t) (by norm_num) ht).2
  have hdir : MixedTurnSafeCut.direction (pointPolarLift A B hh hΔ i 1 t) =
      MixedTurnSafeCut.direction (pointPolarLift A B hh hΔ (i + 1) 0 t) := by
    apply smul_right_injective Plane (ne_of_gt hr)
    exact hdec₁.symm.trans hdec₂
  have hang := angle_eq_mod_two_pi_of_direction_eq hdir
  obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hang.symm
  have hw₁ := pointPolarLift_window A B hh hΔ (i := i) (by omega)
    (s := (1 : ℝ)) (t := t) (by norm_num) ht
  have hw₂ := pointPolarLift_window A B hh hΔ (i := i + 1) (by omega)
    (s := (0 : ℝ)) (t := t) (by norm_num) ht
  have hqabs := PhysicalMixedTurnSource.abs_intrinsicQ_lt_middleExteriorTurn
    A B hh (PhysicalMixedTurnSource.familySource A B (positiveRoot A B hh hΔ) (i + 1))
  have hqpi := PhysicalMixedTurnSource.middleExteriorTurn_lt_pi A B
    (PhysicalMixedTurnSource.familySource A B (positiveRoot A B hh hΔ) (i + 1))
  have hq : |normalizedHeading A B hh hΔ (i + 1) -
      normalizedHeading A B hh hΔ i| < Real.pi := by
    have hstep := PhysicalMixedTurnSource.familyHeading_succ A B hh
      (positiveRoot A B hh hΔ) i
    dsimp [normalizedHeading, rootHeading]
    rw [show -PhysicalMixedTurnSource.familyHeading A B hh
        (positiveRoot A B hh hΔ) (i + 1) -
      -PhysicalMixedTurnSource.familyHeading A B hh (positiveRoot A B hh hΔ) i =
      -(PhysicalMixedTurnSource.familyHeading A B hh (positiveRoot A B hh hΔ) (i + 1) -
        PhysicalMixedTurnSource.familyHeading A B hh (positiveRoot A B hh hΔ) i) by ring,
      abs_neg, hstep]
    exact hqabs.trans hqpi
  have hdiff : -2 * Real.pi <
      pointPolarLift A B hh hΔ (i + 1) 0 t - pointPolarLift A B hh hΔ i 1 t ∧
      pointPolarLift A B hh hΔ (i + 1) 0 t - pointPolarLift A B hh hΔ i 1 t <
        2 * Real.pi := by
    rw [abs_lt] at hq
    constructor <;> linarith
  have hm0 : m = 0 := by
    by_contra hm0
    rcases lt_or_gt_of_ne hm0 with hmneg | hmpos
    · have hle : m ≤ -1 := by omega
      have hle' : (m : ℝ) ≤ -1 := by exact_mod_cast hle
      nlinarith [Real.pi_pos]
    · have hge : (1 : ℤ) ≤ m := by omega
      have hge' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hge
      nlinarith [Real.pi_pos]
  rw [hm0] at hm
  norm_num at hm
  linarith

/-- At interior normalized height, each physical panel has strictly decreasing
real polar angle as the longitudinal coordinate increases. -/
theorem pointPolarLift_strictAnti (hΔ : 0 < Δ A B hh)
    {i : ℕ} (hi : i ≤ N A B) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    StrictAntiOn (fun s => pointPolarLift A B hh hΔ i s t) (Icc (0 : ℝ) 1) := by
  intro s₁ hs₁ s₂ hs₂ hslt
  let S := normalizedStrip A B hh hΔ
  let O := normalizedPole A B hh hΔ
  let z₁ := S.point i s₁ t - O
  let z₂ := S.point i s₂ t - O
  let φ₁ := pointPolarLift A B hh hΔ i s₁ t
  let φ₂ := pointPolarLift A B hh hΔ i s₂ t
  have hsum : 0 < S.lowerCoeff i + S.upperCoeff i := by
    simpa [S, normalizedStrip, RadialExtremalSafety.TriangularRadialStrip.reflectSwap,
      rootStrip, add_comm] using
      PhysicalMixedTurnSource.lowerRunCoeff_add_upperRunCoeff_pos A B hh
        (PhysicalMixedTurnSource.familySource A B (positiveRoot A B hh hΔ) i)
  have hρ : 0 < (1 - t) * S.lowerCoeff i + t * S.upperCoeff i := by
    have hl := S.lowerCoeff_nonneg i hi
    have hu := S.upperCoeff_nonneg i hi
    by_cases hz : S.upperCoeff i = 0
    · have hp : 0 < S.lowerCoeff i := by linarith
      exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht.2) hp)
        (mul_nonneg ht.1.le hu)
    · have hp : 0 < S.upperCoeff i := lt_of_le_of_ne hu (Ne.symm hz)
      exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2.le) hl)
        (mul_pos ht.1 hp)
  have hstep : z₂ = z₁ + ((s₂ - s₁) *
      ((1 - t) * S.lowerCoeff i + t * S.upperCoeff i)) • S.v i := by
    dsimp [z₁, z₂]
    simp only [RadialExtremalSafety.TriangularRadialStrip.point]
    module
  have hsupport := RadialExtremalSafety.TriangularRadialStrip.support_point
    (normalized_radialSupport A B hh hΔ) hi hs₁ ⟨ht.1.le, ht.2.le⟩
  have hc : 0 < (s₂ - s₁) *
      ((1 - t) * S.lowerCoeff i + t * S.upperCoeff i) :=
    mul_pos (sub_pos.mpr hslt) hρ
  have hdetneg : MixedTurnSafeCut.det z₁ z₂ < 0 := by
    rw [hstep]
    have he : MixedTurnSafeCut.det z₁
        (z₁ + ((s₂ - s₁) *
          ((1 - t) * S.lowerCoeff i + t * S.upperCoeff i)) • S.v i) =
        ((s₂ - s₁) * ((1 - t) * S.lowerCoeff i + t * S.upperCoeff i)) *
          MixedTurnSafeCut.det z₁ (S.v i) := by
      simp [MixedTurnSafeCut.det]
      ring
    rw [he]
    exact mul_neg_of_pos_of_neg hc hsupport
  have hd₁ := pointPolarLift_decomposition A B hh hΔ hi hs₁ ⟨ht.1.le, ht.2.le⟩
  have hd₂ := pointPolarLift_decomposition A B hh hΔ hi hs₂ ⟨ht.1.le, ht.2.le⟩
  change z₁ = ‖z₁‖ • MixedTurnSafeCut.direction φ₁ ∧ 0 < ‖z₁‖ at hd₁
  change z₂ = ‖z₂‖ • MixedTurnSafeCut.direction φ₂ ∧ 0 < ‖z₂‖ at hd₂
  have hw₁ := pointPolarLift_window A B hh hΔ hi hs₁ ⟨ht.1.le, ht.2.le⟩
  have hw₂ := pointPolarLift_window A B hh hΔ hi hs₂ ⟨ht.1.le, ht.2.le⟩
  by_contra hnot
  have hφle : φ₁ ≤ φ₂ := le_of_not_gt hnot
  have hδ0 : 0 ≤ φ₂ - φ₁ := sub_nonneg.mpr hφle
  have hδπ : φ₂ - φ₁ ≤ Real.pi := by
    dsimp [φ₁, φ₂] at *
    linarith
  have hsin : 0 ≤ Real.sin (φ₂ - φ₁) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hδ0 hδπ
  have hdetdir : MixedTurnSafeCut.det
      (MixedTurnSafeCut.direction φ₁) (MixedTurnSafeCut.direction φ₂) =
      Real.sin (φ₂ - φ₁) := by
    simp [MixedTurnSafeCut.det, MixedTurnSafeCut.direction, Real.sin_sub]
    ring
  rw [hd₁.1, hd₂.1, RadialExtremalSafety.det_smul_left,
    RadialExtremalSafety.det_smul_right, hdetdir] at hdetneg
  have : 0 ≤ ‖z₁‖ * (‖z₂‖ * Real.sin (φ₂ - φ₁)) :=
    mul_nonneg hd₁.2.le (mul_nonneg hd₂.2.le hsin)
  linarith

/-- Exact real polar interval at each normalized interior height. -/
theorem pointPolarLift_image_Icc (hΔ : 0 < Δ A B hh)
    {i : ℕ} (hi : i ≤ N A B) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (fun s => pointPolarLift A B hh hΔ i s t) '' Icc (0 : ℝ) 1 =
      Icc (pointPolarLift A B hh hΔ i 1 t)
        (pointPolarLift A B hh hΔ i 0 t) := by
  let f : ℝ → ℝ := fun s => pointPolarLift A B hh hΔ i s t
  have hanti : StrictAntiOn f (Icc (0 : ℝ) 1) :=
    pointPolarLift_strictAnti A B hh hΔ hi ht
  let w : ℝ → ℂ := fun s =>
    panelRelativeComplex (normalizedHeading A B hh hΔ i)
      ((normalizedStrip A B hh hΔ).point i s t - normalizedPole A B hh hΔ)
  have hre : Continuous (fun s => (w s).re) := by
    dsimp [w, panelRelativeComplex,
      RadialExtremalSafety.TriangularRadialStrip.point]
    fun_prop
  have him : Continuous (fun s => (w s).im) := by
    dsimp [w, panelRelativeComplex,
      RadialExtremalSafety.TriangularRadialStrip.point]
    fun_prop
  have hwcont : Continuous w := by
    have hc : Continuous (fun s => ((w s).re : ℂ) + ((w s).im : ℂ) * Complex.I) :=
      (Complex.continuous_ofReal.comp hre).add
        ((Complex.continuous_ofReal.comp him).mul continuous_const)
    convert hc using 1
    funext s
    apply Complex.ext <;> simp
  have hfcont : ContinuousOn f (Icc (0 : ℝ) 1) := by
    intro s hs
    have himpos : 0 < (w s).im := by
      have hsupport := RadialExtremalSafety.TriangularRadialStrip.support_point
        (normalized_radialSupport A B hh hΔ) hi hs ⟨ht.1.le, ht.2.le⟩
      rw [show (w s).im = MixedTurnSafeCut.det
        (MixedTurnSafeCut.direction (normalizedHeading A B hh hΔ i))
        ((normalizedStrip A B hh hΔ).point i s t - normalizedPole A B hh hΔ) by
          simp [w, panelRelativeComplex_im]]
      rw [← normalizedForward_eq_direction A B hh hΔ i]
      have hanti : MixedTurnSafeCut.det
          ((normalizedStrip A B hh hΔ).v i)
          ((normalizedStrip A B hh hΔ).point i s t - normalizedPole A B hh hΔ) =
        -MixedTurnSafeCut.det
          ((normalizedStrip A B hh hΔ).point i s t - normalizedPole A B hh hΔ)
          ((normalizedStrip A B hh hΔ).v i) := by
            simp [MixedTurnSafeCut.det]; ring
      rw [hanti]
      exact neg_pos.mpr hsupport
    have hslit : w s ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt himpos))
    have harg : ContinuousAt (fun r => (w r).arg) s :=
      (Complex.continuousAt_arg hslit).comp hwcont.continuousAt
    exact (continuousAt_const.add harg).continuousWithinAt
  apply Set.Subset.antisymm
  · rintro φ ⟨s, hs, rfl⟩
    exact ⟨hanti.antitoneOn hs (by norm_num) hs.2,
      hanti.antitoneOn (by norm_num) hs hs.1⟩
  · exact intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num) hfcont

/-- The last normalized physical hinge is the conjugated affine full-circuit
copy of the root entry at the same normalized height. -/
theorem normalized_virtualFinalHinge (hΔ : 0 < Δ A B hh) (t : ℝ) :
    (normalizedStrip A B hh hΔ).point (N A B) 1 t =
      RadialExtremalSafety.reflectPlane
        (PhysicalMixedTurnSource.fullCircuit A B hh (positiveRoot A B hh hΔ)
          (RadialExtremalSafety.reflectPlane
            ((normalizedStrip A B hh hΔ).point 0 0 t))) := by
  let k := positiveRoot A B hh hΔ
  let T := PhysicalMixedTurnSource.baselineAlignment A B hh k
  have hroot : (rootStrip A B hh k).point (N A B) 1 (1 - t) =
      PhysicalMixedTurnSource.fullCircuit A B hh k
        ((rootStrip A B hh k).point 0 0 (1 - t)) := by
    apply T.injective
    rw [rootStrip_alignment, PhysicalMixedTurnSource.baselineAlignment_fullCircuit,
      rootStrip_alignment]
    have hjoin : (baselineStrip A B hh).point (k.val + N A B) 1 (1 - t) =
        (baselineStrip A B hh).point (k.val + N A B + 1) 0 (1 - t) := by
      rw [baselineStrip_point_one, retainedHinge_eq_next_entry,
        baselineStrip_point_zero]
    rw [hjoin, show k.val + N A B + 1 = N A B + 1 + k.val by omega,
      baselineStrip_point_full_add]
    simp
  have hlast := normalized_point A B hh hΔ (N A B) 1 (1 - t)
  have hfirst := normalized_point A B hh hΔ 0 0 (1 - t)
  have ht : 1 - (1 - t) = t := by ring
  rw [ht] at hlast hfirst
  rw [hlast, hfirst, hroot, RadialExtremalSafety.reflectPlane_reflectPlane]

/-- Exact real polar seam sweep: normalization changes the physical full turn
to `-Δ`, rather than merely its class modulo `2π`. -/
theorem pointPolarLift_terminal (hΔ : 0 < Δ A B hh)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    pointPolarLift A B hh hΔ (N A B) 1 t =
      pointPolarLift A B hh hΔ 0 0 t - Δ A B hh := by
  let S := normalizedStrip A B hh hΔ
  let O := normalizedPole A B hh hΔ
  let φ := pointPolarLift A B hh hΔ (N A B) 1 t
  let ψ := pointPolarLift A B hh hΔ 0 0 t
  let R := PhysicalMixedTurnSource.planeRotation (-Δ A B hh)
  let k := positiveRoot A B hh hΔ
  have hcopy : S.point (N A B) 1 t - O = R (S.point 0 0 t - O) := by
    rw [normalized_virtualFinalHinge A B hh hΔ t]
    have hr (Y : Plane) :
        PhysicalMixedTurnSource.fullCircuit A B hh k Y -
          PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_gt hΔ) =
        PhysicalMixedTurnSource.planeRotation (Δ A B hh)
          (Y - PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_gt hΔ)) := by
      conv_lhs => rw [← PhysicalMixedTurnSource.circuitPole_fixed A B hh k (ne_of_gt hΔ)]
      rw [PhysicalMixedTurnSource.fullCircuit_apply,
        PhysicalMixedTurnSource.fullCircuit_apply, map_sub]
      abel
    change RadialExtremalSafety.reflectPlane
        (PhysicalMixedTurnSource.fullCircuit A B hh k
          (RadialExtremalSafety.reflectPlane (S.point 0 0 t))) -
      RadialExtremalSafety.reflectPlane
        (PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_gt hΔ)) = _
    rw [← RadialExtremalSafety.reflectPlane_sub, hr]
    have hreflect (z : Plane) :
        RadialExtremalSafety.reflectPlane
          (PhysicalMixedTurnSource.planeRotation (Δ A B hh) z) =
        R (RadialExtremalSafety.reflectPlane z) := by
      ext j
      fin_cases j <;> simp [R, PhysicalMixedTurnSource.planeRotation,
        PhysicalMixedTurnSource.planeRotationLinear,
        RadialExtremalSafety.reflectPlane, Real.cos_neg, Real.sin_neg] <;> ring
    rw [hreflect, RadialExtremalSafety.reflectPlane_sub,
      RadialExtremalSafety.reflectPlane_reflectPlane]
    rfl
  have hd₁ := pointPolarLift_decomposition A B hh hΔ (i := N A B) (le_refl _)
    (s := (1 : ℝ)) (t := t) (by norm_num) ht
  have hd₂ := pointPolarLift_decomposition A B hh hΔ (i := 0) (by omega)
    (s := (0 : ℝ)) (t := t) (by norm_num) ht
  change S.point (N A B) 1 t - O =
      ‖S.point (N A B) 1 t - O‖ • MixedTurnSafeCut.direction φ ∧
      0 < ‖S.point (N A B) 1 t - O‖ at hd₁
  change S.point 0 0 t - O = ‖S.point 0 0 t - O‖ •
      MixedTurnSafeCut.direction ψ ∧ 0 < ‖S.point 0 0 t - O‖ at hd₂
  have hnorm : ‖S.point (N A B) 1 t - O‖ = ‖S.point 0 0 t - O‖ := by
    rw [hcopy]
    exact (PhysicalMixedTurnSource.planeRotation _).norm_map _
  have hdir : MixedTurnSafeCut.direction φ =
      MixedTurnSafeCut.direction (ψ - Δ A B hh) := by
    have heq : ‖S.point (N A B) 1 t - O‖ • MixedTurnSafeCut.direction φ =
        ‖S.point (N A B) 1 t - O‖ •
          MixedTurnSafeCut.direction (ψ - Δ A B hh) := by
      calc
        _ = S.point (N A B) 1 t - O := hd₁.1.symm
        _ = R (S.point 0 0 t - O) := hcopy
        _ = ‖S.point 0 0 t - O‖ • MixedTurnSafeCut.direction (-Δ A B hh + ψ) := by
          conv_lhs => rw [hd₂.1, map_smul,
            PhysicalMixedTurnSource.planeRotation_direction]
        _ = _ := by rw [hnorm]; congr 1; ring
    exact (smul_right_injective Plane (ne_of_gt hd₁.2)) heq
  have hang := angle_eq_mod_two_pi_of_direction_eq hdir
  obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hang.symm
  have hw₁ := pointPolarLift_window A B hh hΔ (i := N A B) (le_refl _)
    (s := (1 : ℝ)) (t := t) (by norm_num) ht
  have hw₂ := pointPolarLift_window A B hh hΔ (i := 0) (by omega)
    (s := (0 : ℝ)) (t := t) (by norm_num) ht
  have hstep := PhysicalMixedTurnSource.familyHeading_succ A B hh k (N A B)
  have hqabs := PhysicalMixedTurnSource.abs_intrinsicQ_lt_middleExteriorTurn
    A B hh (PhysicalMixedTurnSource.familySource A B k (N A B + 1))
  have hqpi := PhysicalMixedTurnSource.middleExteriorTurn_lt_pi A B
    (PhysicalMixedTurnSource.familySource A B k (N A B + 1))
  have hq : |normalizedHeading A B hh hΔ (N A B) + Δ A B hh| < Real.pi := by
    have hterm := rootHeading_terminal A B hh k
    dsimp [normalizedHeading, rootHeading] at *
    rw [show -PhysicalMixedTurnSource.familyHeading A B hh k (N A B) + Δ A B hh =
        PhysicalMixedTurnSource.familyHeading A B hh k (N A B + 1) -
          PhysicalMixedTurnSource.familyHeading A B hh k (N A B) by rw [hterm]; ring,
      hstep]
    exact hqabs.trans hqpi
  have hdiff : -2 * Real.pi < (ψ - Δ A B hh) - φ ∧
      (ψ - Δ A B hh) - φ < 2 * Real.pi := by
    rw [abs_lt] at hq
    have hzero : normalizedHeading A B hh hΔ 0 = 0 := by
      simp [normalizedHeading, rootHeading,
        PhysicalMixedTurnSource.familyHeading_zero]
    rw [hzero] at hw₂
    constructor <;> linarith
  have hm0 : m = 0 := by
    by_contra hm0
    rcases lt_or_gt_of_ne hm0 with hmneg | hmpos
    · have hle : m ≤ -1 := by omega
      have hle' : (m : ℝ) ≤ -1 := by exact_mod_cast hle
      nlinarith [Real.pi_pos]
    · have hge : (1 : ℤ) ≤ m := by omega
      have hge' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hge
      nlinarith [Real.pi_pos]
  rw [hm0] at hm
  norm_num at hm
  linarith

/-- Actual real polar angles occupied by the normalized selected-root strip. -/
def longitudinalLiftSet (hΔ : 0 < Δ A B hh) (t : ℝ) : Set ℝ :=
  {φ | ∃ i ≤ N A B, ∃ s ∈ Icc (0 : ℝ) 1,
    φ = pointPolarLift A B hh hΔ i s t}

/-- Every normalized interior-height slice fills the exact real interval
`[entry angle - Δ, entry angle]`, including all wrapped physical panels. -/
theorem longitudinalLiftSet_eq_Icc (hΔ : 0 < Δ A B hh)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    longitudinalLiftSet A B hh hΔ t =
      Icc (pointPolarLift A B hh hΔ 0 0 t - Δ A B hh)
        (pointPolarLift A B hh hΔ 0 0 t) := by
  let lo : ℕ → ℝ := fun i => pointPolarLift A B hh hΔ i 1 t
  let hi : ℕ → ℝ := fun i => pointPolarLift A B hh hΔ i 0 t
  have horder : ∀ i ≤ N A B, lo i ≤ hi i := by
    intro i hiN
    exact (pointPolarLift_strictAnti A B hh hΔ hiN ht).antitoneOn
      (by norm_num) (by norm_num) (by norm_num)
  have hchain : ∀ i < N A B, hi (i + 1) = lo i := by
    intro i hiN
    exact (pointPolarLift_hinge A B hh hΔ hiN
      ⟨ht.1.le, ht.2.le⟩).symm
  have hterminal := pointPolarLift_terminal A B hh hΔ
    ⟨ht.1.le, ht.2.le⟩
  change lo (N A B) = hi 0 - Δ A B hh at hterminal
  rw [← hterminal]
  ext φ
  constructor
  · rintro ⟨i, hiN, s, hs, rfl⟩
    have hlocal : pointPolarLift A B hh hΔ i s t ∈ Icc (lo i) (hi i) := by
      rw [← pointPolarLift_image_Icc A B hh hΔ hiN ht]
      exact ⟨s, hs, rfl⟩
    exact Icc_subset_Icc_of_chain horder hchain hiN hlocal
  · intro hφ
    obtain ⟨i, hiN, hlocal⟩ := exists_mem_Icc_of_chain horder hchain hφ
    rw [← pointPolarLift_image_Icc A B hh hΔ hiN ht] at hlocal
    obtain ⟨s, hs, rfl⟩ := hlocal
    exact ⟨i, hiN, s, hs, rfl⟩

/-- The real root-seam argument of the reflected, rim-swapped source. -/
def alpha (hΔ : 0 < Δ A B hh) (t : ℝ) : ℝ :=
  pointPolarLift A B hh hΔ 0 0 t

/-- Only actual material hits count as ray representatives. -/
def rayHeightComponent (hΔ : 0 < Δ A B hh) (β : ℝ) (m : ℤ) : Set ℝ :=
  {t | t ∈ Ioo (0 : ℝ) 1 ∧
    ∃ i ≤ N A B, ∃ s ∈ Icc (0 : ℝ) 1,
      pointPolarLift A B hh hΔ i s t = β + 2 * Real.pi * (m : ℝ)}

theorem rayHeightComponent_iff (hΔ : 0 < Δ A B hh) (β : ℝ) (m : ℤ) (t : ℝ) :
    t ∈ rayHeightComponent A B hh hΔ β m ↔
      t ∈ Ioo (0 : ℝ) 1 ∧
      alpha A B hh hΔ t - Δ A B hh ≤ β + 2 * Real.pi * (m : ℝ) ∧
      β + 2 * Real.pi * (m : ℝ) ≤ alpha A B hh hΔ t := by
  constructor
  · rintro ⟨ht, i, hi, s, hs, he⟩
    have hw : β + 2 * Real.pi * (m : ℝ) ∈ longitudinalLiftSet A B hh hΔ t :=
      ⟨i, hi, s, hs, he.symm⟩
    rw [longitudinalLiftSet_eq_Icc A B hh hΔ ht] at hw
    exact ⟨ht, hw.1, hw.2⟩
  · rintro ⟨ht, hlo, hhi⟩
    have hw : β + 2 * Real.pi * (m : ℝ) ∈ longitudinalLiftSet A B hh hΔ t := by
      rw [longitudinalLiftSet_eq_Icc A B hh hΔ ht]
      exact ⟨hlo, hhi⟩
    obtain ⟨i, hi, s, hs, he⟩ := hw
    exact ⟨ht, i, hi, s, hs, he.symm⟩

/-- Membership includes a strictly positive radius at the actual normalized point. -/
theorem rayHeightComponent_iff_positiveRay
    (hΔ : 0 < Δ A B hh) (β : ℝ) (m : ℤ) (t : ℝ) :
    t ∈ rayHeightComponent A B hh hΔ β m ↔
      t ∈ Ioo (0 : ℝ) 1 ∧
      ∃ i ≤ N A B, ∃ s ∈ Icc (0 : ℝ) 1,
        pointPolarLift A B hh hΔ i s t = β + 2 * Real.pi * (m : ℝ) ∧
        ∃ r : ℝ, 0 < r ∧
          (normalizedStrip A B hh hΔ).point i s t - normalizedPole A B hh hΔ =
            r • MixedTurnSafeCut.direction (β + 2 * Real.pi * (m : ℝ)) := by
  constructor
  · rintro ⟨ht, i, hi, s, hs, he⟩
    obtain ⟨hd, hp⟩ := pointPolarLift_decomposition A B hh hΔ hi hs
      ⟨ht.1.le, ht.2.le⟩
    refine ⟨ht, i, hi, s, hs, he, _, hp, ?_⟩
    simpa only [he] using hd
  · rintro ⟨ht, i, hi, s, hs, he, r, hr, hp⟩
    exact ⟨ht, i, hi, s, hs, he⟩

/-- No three different turns of one physical ray can meet the strip. -/
theorem rayHeightComponent_no_three (hΔ : 0 < Δ A B hh)
    (β : ℝ) {m₁ m₂ m₃ : ℤ} (h₁₂ : m₁ < m₂) (h₂₃ : m₂ < m₃)
    (h₁ : (rayHeightComponent A B hh hΔ β m₁).Nonempty)
    (h₃ : (rayHeightComponent A B hh hΔ β m₃).Nonempty) : False := by
  obtain ⟨t₁, ht₁⟩ := h₁
  obtain ⟨t₃, ht₃⟩ := h₃
  rw [rayHeightComponent_iff] at ht₁ ht₃
  have ha₁ := pointPolarLift_window A B hh hΔ (i := 0) (by omega)
    (s := (0 : ℝ)) (t := t₁) (by norm_num) ⟨ht₁.1.1.le, ht₁.1.2.le⟩
  have ha₃ := pointPolarLift_window A B hh hΔ (i := 0) (by omega)
    (s := (0 : ℝ)) (t := t₃) (by norm_num) ⟨ht₃.1.1.le, ht₃.1.2.le⟩
  have hgap : m₁ + 2 ≤ m₃ := by omega
  have hgap' : (m₁ : ℝ) + 2 ≤ (m₃ : ℝ) := by exact_mod_cast hgap
  have hlen := PhysicalMixedTurnSource.abs_intrinsicDelta_lt_two_pi A B hh
  rw [abs_of_nonneg hΔ.le] at hlen
  have hpi := Real.pi_pos
  dsimp [alpha] at *
  nlinarith [ht₁.2.1, ht₃.2.2, ha₁.2, ha₃.1]

theorem rayHeightComponent_consecutive (hΔ : 0 < Δ A B hh)
    (β : ℝ) {m₁ m₂ : ℤ} (h₁₂ : m₁ < m₂)
    (h₁ : (rayHeightComponent A B hh hΔ β m₁).Nonempty)
    (h₂ : (rayHeightComponent A B hh hΔ β m₂).Nonempty) :
    m₂ = m₁ + 1 := by
  by_contra hn
  exact rayHeightComponent_no_three A B hh hΔ β
    (show m₁ < m₁ + 1 by omega) (show m₁ + 1 < m₂ by omega) h₁ h₂

theorem rayHeightComponent_sameHeight_unique (hΔ : 0 < Δ A B hh)
    (β : ℝ) {m₁ m₂ : ℤ} {t : ℝ}
    (h₁ : t ∈ rayHeightComponent A B hh hΔ β m₁)
    (h₂ : t ∈ rayHeightComponent A B hh hΔ β m₂) : m₁ = m₂ := by
  rw [rayHeightComponent_iff] at h₁ h₂
  by_contra hn
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · have hc : (m₁ : ℝ) + 1 ≤ (m₂ : ℝ) := by
      exact_mod_cast (show m₁ + 1 ≤ m₂ by omega)
    have hL := PhysicalMixedTurnSource.abs_intrinsicDelta_lt_two_pi A B hh
    rw [abs_of_nonneg hΔ.le] at hL
    nlinarith [h₁.2.1, h₂.2.2, Real.pi_pos]
  · have hc : (m₂ : ℝ) + 1 ≤ (m₁ : ℝ) := by
      exact_mod_cast (show m₂ + 1 ≤ m₁ by omega)
    have hL := PhysicalMixedTurnSource.abs_intrinsicDelta_lt_two_pi A B hh
    rw [abs_of_nonneg hΔ.le] at hL
    nlinarith [h₂.2.1, h₁.2.2, Real.pi_pos]

/-- The normalized seam stays in one strict heading half-plane. -/
theorem alpha_mem_window (hΔ : 0 < Δ A B hh)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    normalizedHeading A B hh hΔ 0 < alpha A B hh hΔ t ∧
      alpha A B hh hΔ t < normalizedHeading A B hh hΔ 0 + Real.pi :=
  pointPolarLift_window A B hh hΔ (by omega) (by norm_num) ht

private theorem alpha_seam_det (hΔ : 0 < Δ A B hh) (s t : ℝ) :
    let S := normalizedStrip A B hh hΔ
    let O := normalizedPole A B hh hΔ
    MixedTurnSafeCut.det (S.point 0 0 s - O) (S.point 0 0 t - O) =
      (t - s) * MixedTurnSafeCut.det (S.B 0 - O) (S.d 0) := by
  dsimp
  simp only [RadialExtremalSafety.TriangularRadialStrip.point, zero_mul,
    zero_smul, add_zero]
  simp [MixedTurnSafeCut.det]
  ring

private theorem alpha_det_sign (hΔ : 0 < Δ A B hh)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    let S := normalizedStrip A B hh hΔ
    let O := normalizedPole A B hh hΔ
    (0 < MixedTurnSafeCut.det (S.point 0 0 s - O) (S.point 0 0 t - O) ↔
      alpha A B hh hΔ s < alpha A B hh hΔ t) ∧
    (MixedTurnSafeCut.det (S.point 0 0 s - O) (S.point 0 0 t - O) = 0 ↔
      alpha A B hh hΔ s = alpha A B hh hΔ t) := by
  let S := normalizedStrip A B hh hΔ
  let O := normalizedPole A B hh hΔ
  let z (r : ℝ) := S.point 0 0 r - O
  let a (r : ℝ) := alpha A B hh hΔ r
  have hds := pointPolarLift_decomposition A B hh hΔ
    (i := 0) (by omega) (by norm_num : (0 : ℝ) ∈ Icc 0 1) hs
  have hdt := pointPolarLift_decomposition A B hh hΔ
    (i := 0) (by omega) (by norm_num : (0 : ℝ) ∈ Icc 0 1) ht
  change z s = ‖z s‖ • MixedTurnSafeCut.direction (a s) ∧ 0 < ‖z s‖ at hds
  change z t = ‖z t‖ • MixedTurnSafeCut.direction (a t) ∧ 0 < ‖z t‖ at hdt
  have hwS := alpha_mem_window A B hh hΔ hs
  have hwT := alpha_mem_window A B hh hΔ ht
  change normalizedHeading A B hh hΔ 0 < a s ∧
    a s < normalizedHeading A B hh hΔ 0 + Real.pi at hwS
  change normalizedHeading A B hh hΔ 0 < a t ∧
    a t < normalizedHeading A B hh hΔ 0 + Real.pi at hwT
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
      exact mul_pos (mul_pos hds.2 hdt.2)
        (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hp) hhigh)
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

theorem alpha_det_trichotomy (hΔ : 0 < Δ A B hh) :
    StrictMonoOn (alpha A B hh hΔ) (Icc (0 : ℝ) 1) ∨
    StrictAntiOn (alpha A B hh hΔ) (Icc (0 : ℝ) 1) ∨
    ∀ t ∈ Icc (0 : ℝ) 1, alpha A B hh hΔ t = alpha A B hh hΔ 0 := by
  let S := normalizedStrip A B hh hΔ
  let O := normalizedPole A B hh hΔ
  let D := MixedTurnSafeCut.det (S.B 0 - O) (S.d 0)
  rcases lt_trichotomy 0 D with hp | hz | hn
  · left
    intro s hs t ht hst
    have he := (alpha_det_sign A B hh hΔ hs ht).1
    rw [alpha_seam_det] at he
    exact he.mp (mul_pos (sub_pos.mpr hst) hp)
  · right; right
    intro t ht
    have he := (alpha_det_sign A B hh hΔ ht
      (show (0 : ℝ) ∈ Icc 0 1 by norm_num)).2
    apply he.mp
    rw [alpha_seam_det]
    exact mul_eq_zero_of_right _ hz.symm
  · right; left
    intro s hs t ht hst
    have he := (alpha_det_sign A B hh hΔ ht hs).1
    rw [alpha_seam_det] at he
    exact he.mp (mul_pos_of_neg_of_neg (sub_neg.mpr hst) hn)

/-- The shorter-than-a-turn window separates distinct actual representatives. -/
private theorem component_alpha_sep (hΔ : 0 < Δ A B hh) (β : ℝ)
    {m₁ m₂ : ℤ} (hm : m₁ < m₂) {t u : ℝ}
    (ht : t ∈ rayHeightComponent A B hh hΔ β m₁)
    (hu : u ∈ rayHeightComponent A B hh hΔ β m₂) :
    alpha A B hh hΔ t < alpha A B hh hΔ u := by
  rw [rayHeightComponent_iff] at ht hu
  have hc : (m₁ : ℝ) + 1 ≤ (m₂ : ℝ) := by
    exact_mod_cast (show m₁ + 1 ≤ m₂ by omega)
  have hL := PhysicalMixedTurnSource.abs_intrinsicDelta_lt_two_pi A B hh
  rw [abs_of_nonneg hΔ.le] at hL
  nlinarith [ht.2.1, hu.2.2, Real.pi_pos]

theorem rayHeightComponent_order_of_mono (hΔ : 0 < Δ A B hh)
    (β : ℝ) (hα : MonotoneOn (alpha A B hh hΔ) (Icc (0 : ℝ) 1))
    {m₁ m₂ : ℤ} (hm : m₁ < m₂)
    {t u : ℝ} (ht : t ∈ rayHeightComponent A B hh hΔ β m₁)
    (hu : u ∈ rayHeightComponent A B hh hΔ β m₂) : t < u := by
  have hs := component_alpha_sep A B hh hΔ β hm ht hu
  have ht' := (rayHeightComponent_iff A B hh hΔ β m₁ t).mp ht
  have hu' := (rayHeightComponent_iff A B hh hΔ β m₂ u).mp hu
  by_contra hn
  exact (not_le_of_gt hs) (hα ⟨hu'.1.1.le, hu'.1.2.le⟩
    ⟨ht'.1.1.le, ht'.1.2.le⟩ (le_of_not_gt hn))

theorem rayHeightComponent_order_of_anti (hΔ : 0 < Δ A B hh)
    (β : ℝ) (hα : AntitoneOn (alpha A B hh hΔ) (Icc (0 : ℝ) 1))
    {m₁ m₂ : ℤ} (hm : m₁ < m₂)
    {t u : ℝ} (ht : t ∈ rayHeightComponent A B hh hΔ β m₁)
    (hu : u ∈ rayHeightComponent A B hh hΔ β m₂) : u < t := by
  have hs := component_alpha_sep A B hh hΔ β hm ht hu
  have ht' := (rayHeightComponent_iff A B hh hΔ β m₁ t).mp ht
  have hu' := (rayHeightComponent_iff A B hh hΔ β m₂ u).mp hu
  by_contra hn
  exact (not_le_of_gt hs) (hα ⟨ht'.1.1.le, ht'.1.2.le⟩
    ⟨hu'.1.1.le, hu'.1.2.le⟩ (le_of_not_gt hn))

theorem rayHeightComponent_convex_of_mono (hΔ : 0 < Δ A B hh)
    (β : ℝ) (m : ℤ)
    (hα : MonotoneOn (alpha A B hh hΔ) (Icc (0 : ℝ) 1))
    {s t u : ℝ} (hs : s ∈ rayHeightComponent A B hh hΔ β m)
    (hu : u ∈ rayHeightComponent A B hh hΔ β m)
    (hst : s ≤ t) (htu : t ≤ u) :
    t ∈ rayHeightComponent A B hh hΔ β m := by
  rw [rayHeightComponent_iff] at hs hu ⊢
  refine ⟨⟨lt_of_lt_of_le hs.1.1 hst, lt_of_le_of_lt htu hu.1.2⟩, ?_, ?_⟩
  · have h := hα ⟨(hs.1.1.trans_le hst).le, (htu.trans hu.1.2.le)⟩
      ⟨hu.1.1.le, hu.1.2.le⟩ htu
    linarith [hu.2.1]
  · have h := hα ⟨hs.1.1.le, hs.1.2.le⟩
      ⟨(hs.1.1.trans_le hst).le, (htu.trans hu.1.2.le)⟩ hst
    linarith [hs.2.2]

theorem rayHeightComponent_convex_of_anti (hΔ : 0 < Δ A B hh)
    (β : ℝ) (m : ℤ)
    (hα : AntitoneOn (alpha A B hh hΔ) (Icc (0 : ℝ) 1))
    {s t u : ℝ} (hs : s ∈ rayHeightComponent A B hh hΔ β m)
    (hu : u ∈ rayHeightComponent A B hh hΔ β m)
    (hst : s ≤ t) (htu : t ≤ u) :
    t ∈ rayHeightComponent A B hh hΔ β m := by
  rw [rayHeightComponent_iff] at hs hu ⊢
  refine ⟨⟨lt_of_lt_of_le hs.1.1 hst, lt_of_le_of_lt htu hu.1.2⟩, ?_, ?_⟩
  · have h := hα ⟨hs.1.1.le, hs.1.2.le⟩
      ⟨(hs.1.1.trans_le hst).le, (htu.trans hu.1.2.le)⟩ hst
    linarith [hs.2.1]
  · have h := hα ⟨(hs.1.1.trans_le hst).le, (htu.trans hu.1.2.le)⟩
      ⟨hu.1.1.le, hu.1.2.le⟩ htu
    linarith [hu.2.2]

theorem rayHeightComponent_convex (hΔ : 0 < Δ A B hh)
    (β : ℝ) (m : ℤ) {s t u : ℝ}
    (hs : s ∈ rayHeightComponent A B hh hΔ β m)
    (hu : u ∈ rayHeightComponent A B hh hΔ β m)
    (hst : s ≤ t) (htu : t ≤ u) :
    t ∈ rayHeightComponent A B hh hΔ β m := by
  rcases alpha_det_trichotomy A B hh hΔ with hinc | hdec | hconst
  · exact rayHeightComponent_convex_of_mono A B hh hΔ β m
      hinc.monotoneOn hs hu hst htu
  · exact rayHeightComponent_convex_of_anti A B hh hΔ β m
      hdec.antitoneOn hs hu hst htu
  · apply rayHeightComponent_convex_of_mono A B hh hΔ β m
    · intro x hx y hy hxy
      rw [hconst x hx, hconst y hy]
    · exact hs
    · exact hu
    · exact hst
    · exact htu

/-- A hit uses the physical normalized point, not a filtered panel list. -/
def MaterialHit (hΔ : 0 < Δ A B hh) (β : ℝ) (m : ℤ)
    (i : ℕ) (s t : ℝ) : Prop :=
  i ≤ N A B ∧ s ∈ Icc (0 : ℝ) 1 ∧ t ∈ Ioo (0 : ℝ) 1 ∧
    pointPolarLift A B hh hΔ i s t = β + 2 * Real.pi * (m : ℝ)

/-- Later panels' entries cannot overtake earlier panels' exits. -/
theorem panel_entries_order (hΔ : 0 < Δ A B hh)
    {i j : ℕ} (hij : i < j) (hj : j ≤ N A B)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    pointPolarLift A B hh hΔ j 0 t ≤ pointPolarLift A B hh hΔ i 1 t ∧
    (i + 1 < j → pointPolarLift A B hh hΔ j 0 t <
      pointPolarLift A B hh hΔ i 1 t) := by
  have hiN : i < N A B := by omega
  have hbase : pointPolarLift A B hh hΔ (i + 1) 0 t =
      pointPolarLift A B hh hΔ i 1 t :=
    (pointPolarLift_hinge A B hh hΔ hiN ⟨ht.1.le, ht.2.le⟩).symm
  have hchain : ∀ k, i + 1 ≤ k → k ≤ N A B →
      pointPolarLift A B hh hΔ k 0 t ≤
        pointPolarLift A B hh hΔ i 1 t := by
    intro k hik hk
    induction k, hik using Nat.le_induction with
    | base => exact hbase.le
    | succ k hik ih =>
        have hkN : k < N A B := by omega
        have hstep := pointPolarLift_hinge A B hh hΔ hkN
          ⟨ht.1.le, ht.2.le⟩
        have hstrict := (pointPolarLift_strictAnti A B hh hΔ
          (Nat.le_of_lt hkN) ht) (by norm_num : (0 : ℝ) ∈ Icc 0 1)
            (by norm_num : (1 : ℝ) ∈ Icc 0 1) (by norm_num : (0 : ℝ) < 1)
        rw [← hstep]
        exact le_of_lt (lt_of_lt_of_le hstrict (ih (by omega)))
  refine ⟨hchain j (by omega) hj, ?_⟩
  intro hfar
  have hprev : i + 1 ≤ j - 1 := by omega
  have hprevN : j - 1 < N A B := by omega
  have hbound := hchain (j - 1) hprev (Nat.le_of_lt hprevN)
  have hstep := pointPolarLift_hinge A B hh hΔ hprevN
    ⟨ht.1.le, ht.2.le⟩
  have hstrict := (pointPolarLift_strictAnti A B hh hΔ
    (Nat.le_of_lt hprevN) ht) (by norm_num : (0 : ℝ) ∈ Icc 0 1)
      (by norm_num : (1 : ℝ) ∈ Icc 0 1) (by norm_num : (0 : ℝ) < 1)
  have heq : j - 1 + 1 = j := by omega
  rw [heq] at hstep
  rw [← hstep]
  exact lt_of_lt_of_le hstrict hbound

theorem materialHit_samePanel_point (hΔ : 0 < Δ A B hh)
    (β : ℝ) (m : ℤ) {i : ℕ} {s₁ s₂ t : ℝ}
    (h₁ : MaterialHit A B hh hΔ β m i s₁ t)
    (h₂ : MaterialHit A B hh hΔ β m i s₂ t) :
    (normalizedStrip A B hh hΔ).point i s₁ t =
      (normalizedStrip A B hh hΔ).point i s₂ t := by
  let S := normalizedStrip A B hh hΔ
  let O := normalizedPole A B hh hΔ
  have hd₁ := pointPolarLift_decomposition A B hh hΔ h₁.1 h₁.2.1
    ⟨h₁.2.2.1.1.le, h₁.2.2.1.2.le⟩
  have hd₂ := pointPolarLift_decomposition A B hh hΔ h₂.1 h₂.2.1
    ⟨h₂.2.2.1.1.le, h₂.2.2.1.2.le⟩
  have he₁ : FixedBaselinePolarRayGeometry.RayHit S O
      (β + 2 * Real.pi * (m : ℝ)) i s₁ t _ :=
    ⟨h₁.2.1, ⟨h₁.2.2.1.1.le, h₁.2.2.1.2.le⟩,
      hd₁.2, by simpa [h₁.2.2.2] using hd₁.1⟩
  have he₂ : FixedBaselinePolarRayGeometry.RayHit S O
      (β + 2 * Real.pi * (m : ℝ)) i s₂ t _ :=
    ⟨h₂.2.1, ⟨h₂.2.2.1.1.le, h₂.2.2.1.2.le⟩,
      hd₂.2, by simpa [h₂.2.2.2] using hd₂.1⟩
  exact FixedBaselinePolarRayGeometry.ray_point_unique_at_height S O
    (normalized_radialSupport A B hh hΔ) h₁.1 he₁ he₂

theorem materialHit_point_unique (hΔ : 0 < Δ A B hh)
    (β : ℝ) (m : ℤ) {i j : ℕ} {s₁ s₂ t : ℝ}
    (h₁ : MaterialHit A B hh hΔ β m i s₁ t)
    (h₂ : MaterialHit A B hh hΔ β m j s₂ t) :
    (normalizedStrip A B hh hΔ).point i s₁ t =
      (normalizedStrip A B hh hΔ).point j s₂ t := by
  by_cases heq : i = j
  · subst j
    exact materialHit_samePanel_point A B hh hΔ β m h₁ h₂
  · have ht := h₁.2.2.1
    have hfixed (a b : ℕ) (x y : ℝ)
        (ha : MaterialHit A B hh hΔ β m a x t)
        (hb : MaterialHit A B hh hΔ β m b y t)
        (hab : a < b) :
        (normalizedStrip A B hh hΔ).point a x t =
          (normalizedStrip A B hh hΔ).point b y t := by
      have horder := panel_entries_order A B hh hΔ hab hb.1 ht
      have hleft := (pointPolarLift_strictAnti A B hh hΔ ha.1 ht).antitoneOn
        ha.2.1 (by norm_num : (1 : ℝ) ∈ Icc 0 1) ha.2.1.2
      have hright := (pointPolarLift_strictAnti A B hh hΔ hb.1 ht).antitoneOn
        (by norm_num : (0 : ℝ) ∈ Icc 0 1) hb.2.1 hb.2.1.1
      have hmeet : pointPolarLift A B hh hΔ a 1 t =
          pointPolarLift A B hh hΔ b 0 t := by
        rw [ha.2.2.2] at hleft
        rw [hb.2.2.2] at hright
        exact le_antisymm (le_trans hleft hright) horder.1
      have hadj : b = a + 1 := by
        by_contra hn
        exact (ne_of_gt (horder.2 (by omega))) hmeet
      have hx : x = 1 := by
        by_contra hn
        have hlt : x < 1 := lt_of_le_of_ne ha.2.1.2 hn
        have hs := (pointPolarLift_strictAnti A B hh hΔ ha.1 ht)
          ha.2.1 (by norm_num : (1 : ℝ) ∈ Icc 0 1) hlt
        change pointPolarLift A B hh hΔ a 1 t <
          pointPolarLift A B hh hΔ a x t at hs
        rw [ha.2.2.2, hmeet, ← hb.2.2.2] at hs
        exact (not_lt_of_ge hright) hs
      have hy : y = 0 := by
        by_contra hn
        have hlt : (0 : ℝ) < y := lt_of_le_of_ne hb.2.1.1 (Ne.symm hn)
        have hs := (pointPolarLift_strictAnti A B hh hΔ hb.1 ht)
          (by norm_num : (0 : ℝ) ∈ Icc 0 1) hb.2.1 hlt
        change pointPolarLift A B hh hΔ b y t <
          pointPolarLift A B hh hΔ b 0 t at hs
        rw [hb.2.2.2, ← hmeet, ← ha.2.2.2] at hs
        exact (not_lt_of_ge hleft) hs
      subst x
      subst y
      rw [hadj]
      exact FixedBaselinePolarTrace.point_exit_eq_next_entry
        (normalizedStrip A B hh hΔ) (lt_of_lt_of_le hab hb.1) t
    rcases lt_or_gt_of_ne heq with hij | hji
    · exact hfixed i j s₁ s₂ h₁ h₂ hij
    · exact (hfixed j i s₂ s₁ h₂ h₁ hji).symm

/-- The source-chosen radius is independent of the hit's panel name. -/
noncomputable def componentRadius (hΔ : 0 < Δ A B hh)
    (β : ℝ) (m : ℤ) (t : ℝ) : ℝ :=
  if ht : t ∈ rayHeightComponent A B hh hΔ β m then
    let i := Classical.choose ht.2
    let s := Classical.choose (Classical.choose_spec ht.2).2
    ‖(normalizedStrip A B hh hΔ).point i s t - normalizedPole A B hh hΔ‖
  else 0

theorem componentRadius_eq_hit (hΔ : 0 < Δ A B hh)
    (β : ℝ) (m : ℤ) {i : ℕ} {s t : ℝ}
    (hit : MaterialHit A B hh hΔ β m i s t) :
    componentRadius A B hh hΔ β m t =
      ‖(normalizedStrip A B hh hΔ).point i s t - normalizedPole A B hh hΔ‖ := by
  have ht : t ∈ rayHeightComponent A B hh hΔ β m :=
    ⟨hit.2.2.1, i, hit.1, s, hit.2.1, hit.2.2.2⟩
  let j := Classical.choose ht.2
  let y := Classical.choose (Classical.choose_spec ht.2).2
  have hj : MaterialHit A B hh hΔ β m j y t :=
    ⟨(Classical.choose_spec ht.2).1,
      (Classical.choose_spec (Classical.choose_spec ht.2).2).1,
      ht.1, (Classical.choose_spec (Classical.choose_spec ht.2).2).2⟩
  have hp := materialHit_point_unique A B hh hΔ β m hj hit
  simp only [componentRadius, dite_eq_ite, dif_pos ht]
  exact congrArg (fun p => ‖p - normalizedPole A B hh hΔ‖) hp

theorem componentRadius_pos (hΔ : 0 < Δ A B hh)
    (β : ℝ) (m : ℤ) {t : ℝ}
    (ht : t ∈ rayHeightComponent A B hh hΔ β m) :
    0 < componentRadius A B hh hΔ β m t := by
  obtain ⟨i, hi, s, hs, he⟩ := ht.2
  rw [componentRadius_eq_hit A B hh hΔ β m ⟨hi, hs, ht.1, he⟩]
  exact (pointPolarLift_decomposition A B hh hΔ hi hs
    ⟨ht.1.1.le, ht.1.2.le⟩).2

theorem componentRadius_strict_samePanel (hΔ : 0 < Δ A B hh)
    (β : ℝ) (m : ℤ) {i : ℕ} {s₁ s₂ t u : ℝ}
    (ht : MaterialHit A B hh hΔ β m i s₁ t)
    (hu : MaterialHit A B hh hΔ β m i s₂ u)
    (htu : t < u) :
    componentRadius A B hh hΔ β m u <
      componentRadius A B hh hΔ β m t := by
  let S := normalizedStrip A B hh hΔ
  let O := normalizedPole A B hh hΔ
  have hd₁ := pointPolarLift_decomposition A B hh hΔ ht.1 ht.2.1
    ⟨ht.2.2.1.1.le, ht.2.2.1.2.le⟩
  have hd₂ := pointPolarLift_decomposition A B hh hΔ hu.1 hu.2.1
    ⟨hu.2.2.1.1.le, hu.2.2.1.2.le⟩
  have hit₁ : FixedBaselinePolarRayGeometry.RayHit S O
      (β + 2 * Real.pi * (m : ℝ)) i s₁ t ‖S.point i s₁ t - O‖ :=
    ⟨ht.2.1, ⟨ht.2.2.1.1.le, ht.2.2.1.2.le⟩,
      hd₁.2, by simpa only [ht.2.2.2] using hd₁.1⟩
  have hit₂ : FixedBaselinePolarRayGeometry.RayHit S O
      (β + 2 * Real.pi * (m : ℝ)) i s₂ u ‖S.point i s₂ u - O‖ :=
    ⟨hu.2.1, ⟨hu.2.2.1.1.le, hu.2.2.1.2.le⟩,
      hd₂.2, by simpa only [hu.2.2.2] using hd₂.1⟩
  rw [componentRadius_eq_hit A B hh hΔ β m hu,
    componentRadius_eq_hit A B hh hΔ β m ht]
  exact FixedBaselinePolarTrace.ray_radius_strictAnti S O
    (normalized_radialSupport A B hh hΔ) ht.1 htu hit₁ hit₂

theorem materialHit_sameHeight (hΔ : 0 < Δ A B hh)
    (β : ℝ) {m₁ m₂ : ℤ} {i j : ℕ} {s₁ s₂ t : ℝ}
    (h₁ : MaterialHit A B hh hΔ β m₁ i s₁ t)
    (h₂ : MaterialHit A B hh hΔ β m₂ j s₂ t) :
    m₁ = m₂ ∧
      (normalizedStrip A B hh hΔ).point i s₁ t =
        (normalizedStrip A B hh hΔ).point j s₂ t := by
  have hm := rayHeightComponent_sameHeight_unique A B hh hΔ β
    (show t ∈ rayHeightComponent A B hh hΔ β m₁ from
      ⟨h₁.2.2.1, i, h₁.1, s₁, h₁.2.1, h₁.2.2.2⟩)
    (show t ∈ rayHeightComponent A B hh hΔ β m₂ from
      ⟨h₂.2.2.1, j, h₂.1, s₂, h₂.2.1, h₂.2.2.2⟩)
  subst m₂
  exact ⟨rfl, materialHit_point_unique A B hh hΔ β m₁ h₁ h₂⟩

theorem materialHit_sameHeight_hinge (hΔ : 0 < Δ A B hh)
    (β : ℝ) {m₁ m₂ : ℤ} {i j : ℕ} {s₁ s₂ t : ℝ}
    (h₁ : MaterialHit A B hh hΔ β m₁ i s₁ t)
    (h₂ : MaterialHit A B hh hΔ β m₂ j s₂ t) :
    i = j ∨ (j = i + 1 ∧ s₁ = 1 ∧ s₂ = 0) ∨
      (i = j + 1 ∧ s₂ = 1 ∧ s₁ = 0) := by
  have hm := (materialHit_sameHeight A B hh hΔ β h₁ h₂).1
  subst m₂
  by_cases hij : i = j
  · exact Or.inl hij
  have hforward (a b : ℕ) (x y : ℝ)
      (ha : MaterialHit A B hh hΔ β m₁ a x t)
      (hb : MaterialHit A B hh hΔ β m₁ b y t)
      (hab : a < b) : b = a + 1 ∧ x = 1 ∧ y = 0 := by
    have horder := panel_entries_order A B hh hΔ hab hb.1 ha.2.2.1
    have hleft := (pointPolarLift_strictAnti A B hh hΔ ha.1 ha.2.2.1).antitoneOn
      ha.2.1 (by norm_num : (1 : ℝ) ∈ Icc 0 1) ha.2.1.2
    have hright := (pointPolarLift_strictAnti A B hh hΔ hb.1 hb.2.2.1).antitoneOn
      (by norm_num : (0 : ℝ) ∈ Icc 0 1) hb.2.1 hb.2.1.1
    have hmeet : pointPolarLift A B hh hΔ a 1 t =
        pointPolarLift A B hh hΔ b 0 t := by
      rw [ha.2.2.2] at hleft
      rw [hb.2.2.2] at hright
      exact le_antisymm (le_trans hleft hright) horder.1
    have hadj : b = a + 1 := by
      by_contra hn
      exact (ne_of_gt (horder.2 (by omega))) hmeet
    have hx : x = 1 := by
      by_contra hn
      have hlt : x < 1 := lt_of_le_of_ne ha.2.1.2 hn
      have hs := (pointPolarLift_strictAnti A B hh hΔ ha.1 ha.2.2.1)
        ha.2.1 (by norm_num : (1 : ℝ) ∈ Icc 0 1) hlt
      change pointPolarLift A B hh hΔ a 1 t <
        pointPolarLift A B hh hΔ a x t at hs
      rw [ha.2.2.2, hmeet, ← hb.2.2.2] at hs
      exact (not_lt_of_ge hright) hs
    have hy : y = 0 := by
      by_contra hn
      have hlt : (0 : ℝ) < y := lt_of_le_of_ne hb.2.1.1 (Ne.symm hn)
      have hs := (pointPolarLift_strictAnti A B hh hΔ hb.1 ha.2.2.1)
        (by norm_num : (0 : ℝ) ∈ Icc 0 1) hb.2.1 hlt
      change pointPolarLift A B hh hΔ b y t <
        pointPolarLift A B hh hΔ b 0 t at hs
      rw [hb.2.2.2, ← hmeet, ← ha.2.2.2] at hs
      exact (not_lt_of_ge hleft) hs
    exact ⟨hadj, hx, hy⟩
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact Or.inr (Or.inl (hforward i j s₁ s₂ h₁ h₂ hlt))
  · exact Or.inr (Or.inr (hforward j i s₂ s₁ h₂ h₁ hgt))

/-- Fixed normalized material coordinates vary continuously in height. -/
theorem pointPolarLift_continuousOn_height (hΔ : 0 < Δ A B hh)
    {i : ℕ} (hi : i ≤ N A B) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (pointPolarLift A B hh hΔ i s) (Icc (0 : ℝ) 1) := by
  let S := normalizedStrip A B hh hΔ
  let O := normalizedPole A B hh hΔ
  let θ := normalizedHeading A B hh hΔ i
  let w : ℝ → ℂ := fun t => panelRelativeComplex θ (S.point i s t - O)
  have hre : Continuous (fun t => (w t).re) := by
    dsimp [w, panelRelativeComplex, RadialExtremalSafety.TriangularRadialStrip.point]
    fun_prop
  have him : Continuous (fun t => (w t).im) := by
    dsimp [w, panelRelativeComplex, RadialExtremalSafety.TriangularRadialStrip.point]
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
      (normalized_radialSupport A B hh hΔ) hi hs ht
    apply Complex.mem_slitPlane_iff.mpr
    right
    have hanti : MixedTurnSafeCut.det (S.v i) (S.point i s t - O) =
        -MixedTurnSafeCut.det (S.point i s t - O) (S.v i) := by
      simp [MixedTurnSafeCut.det]; ring
    have himpos : 0 < (w t).im := by
      rw [show (w t).im = MixedTurnSafeCut.det
        (MixedTurnSafeCut.direction θ) (S.point i s t - O) by
          simp [w, panelRelativeComplex_im]]
      rw [← normalizedForward_eq_direction A B hh hΔ i]
      change 0 < MixedTurnSafeCut.det (S.v i) _
      rw [hanti]
      exact neg_pos.mpr hsupport
    exact ne_of_gt himpos
  have harg : ContinuousAt (fun r => (w r).arg) t :=
    (Complex.continuousAt_arg hslit).comp hwcont.continuousAt
  exact (continuousAt_const.add harg).continuousWithinAt

/-- Closed angular eligibility for one actual normalized panel. -/
def panelHeightClosure (hΔ : 0 < Δ A B hh)
    (β : ℝ) (m : ℤ) (i : ℕ) : Set ℝ :=
  {t | t ∈ Icc (0 : ℝ) 1 ∧
    pointPolarLift A B hh hΔ i 1 t ≤ β + 2 * Real.pi * (m : ℝ) ∧
    β + 2 * Real.pi * (m : ℝ) ≤ pointPolarLift A B hh hΔ i 0 t}

theorem panelHeightClosure_closed (hΔ : 0 < Δ A B hh)
    (β : ℝ) (m : ℤ) {i : ℕ} (hi : i ≤ N A B) :
    IsClosed (panelHeightClosure A B hh hΔ β m i) := by
  have h₁ := pointPolarLift_continuousOn_height A B hh hΔ hi
    (s := 1) (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  have h₀ := pointPolarLift_continuousOn_height A B hh hΔ hi
    (s := 0) (by norm_num : (0 : ℝ) ∈ Icc 0 1)
  have hc₁ : IsClosed (Icc (0 : ℝ) 1 ∩
      (pointPolarLift A B hh hΔ i 1) ⁻¹'
        Iic (β + 2 * Real.pi * (m : ℝ))) :=
    h₁.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hc₀ : IsClosed (Icc (0 : ℝ) 1 ∩
      (pointPolarLift A B hh hΔ i 0) ⁻¹'
        Ici (β + 2 * Real.pi * (m : ℝ))) :=
    h₀.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  convert hc₁.inter hc₀ using 1 <;> ext t <;>
    simp [panelHeightClosure, and_left_comm, and_assoc]

theorem panelHeightClosure_iff (hΔ : 0 < Δ A B hh)
    (β : ℝ) (m : ℤ) {i : ℕ} (hi : i ≤ N A B) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    t ∈ panelHeightClosure A B hh hΔ β m i ↔
      ∃ s, MaterialHit A B hh hΔ β m i s t := by
  have himage := pointPolarLift_image_Icc A B hh hΔ hi ht
  rw [Set.ext_iff] at himage
  have he := himage (β + 2 * Real.pi * (m : ℝ))
  simp only [mem_image, mem_Icc] at he
  change (∃ s ∈ Icc (0 : ℝ) 1,
    pointPolarLift A B hh hΔ i s t = β + 2 * Real.pi * (m : ℝ)) ↔ _ at he
  constructor
  · intro h
    obtain ⟨s, hs, heq⟩ := he.mpr ⟨h.2.1, h.2.2⟩
    exact ⟨s, hi, hs, ht, heq⟩
  · rintro ⟨s, hs⟩
    exact ⟨⟨ht.1.le, ht.2.le⟩, (he.mp ⟨s, hs.2.1, hs.2.2.2⟩).1,
      (he.mp ⟨s, hs.2.1, hs.2.2.2⟩).2⟩

/-- The Cramer radius is affine in physical normalized height. -/
noncomputable def panelAffineRadius (hΔ : 0 < Δ A B hh)
    (β : ℝ) (m : ℤ) (i : ℕ) (t : ℝ) : ℝ :=
  let S := normalizedStrip A B hh hΔ
  let O := normalizedPole A B hh hΔ
  ((1 - t) * MixedTurnSafeCut.det (S.B i - O) (S.v i) +
    t * MixedTurnSafeCut.det (S.B i + S.d i - O) (S.v i)) /
      MixedTurnSafeCut.det (MixedTurnSafeCut.direction
        (β + 2 * Real.pi * (m : ℝ))) (S.v i)

theorem panelAffineRadius_continuous (hΔ : 0 < Δ A B hh)
    (β : ℝ) (m : ℤ) (i : ℕ) :
    Continuous (panelAffineRadius A B hh hΔ β m i) := by
  unfold panelAffineRadius
  fun_prop

theorem componentRadius_eq_affine (hΔ : 0 < Δ A B hh)
    (β : ℝ) (m : ℤ) {i : ℕ} {s t : ℝ}
    (hit : MaterialHit A B hh hΔ β m i s t) :
    componentRadius A B hh hΔ β m t = panelAffineRadius A B hh hΔ β m i t := by
  let S := normalizedStrip A B hh hΔ
  let O := normalizedPole A B hh hΔ
  have hd := pointPolarLift_decomposition A B hh hΔ hit.1 hit.2.1
    ⟨hit.2.2.1.1.le, hit.2.2.1.2.le⟩
  have rhit : FixedBaselinePolarRayGeometry.RayHit S O
      (β + 2 * Real.pi * (m : ℝ)) i s t ‖S.point i s t - O‖ :=
    ⟨hit.2.1, ⟨hit.2.2.1.1.le, hit.2.2.1.2.le⟩,
      hd.2, by simpa only [hit.2.2.2] using hd.1⟩
  rw [componentRadius_eq_hit A B hh hΔ β m hit]
  exact FixedBaselinePolarRayGeometry.ray_radius_eq S O
    (normalized_radialSupport A B hh hΔ) hit.1 rhit

theorem componentRadius_continuousOn (hΔ : 0 < Δ A B hh)
    (β : ℝ) (m : ℤ) :
    ContinuousOn (componentRadius A B hh hΔ β m)
      (rayHeightComponent A B hh hΔ β m) := by
  let I := rayHeightComponent A B hh hΔ β m
  let F : Fin (N A B + 1) → Set ℝ := fun i => panelHeightClosure A B hh hΔ β m i.val
  have hclosed : ∀ i, IsClosed (F i) := fun i =>
    panelHeightClosure_closed A B hh hΔ β m (by omega)
  have hcover : ∀ x ∈ I, ∃ i, x ∈ F i := by
    intro x hx
    obtain ⟨i, hi, s, hs, he⟩ := hx.2
    refine ⟨⟨i, by omega⟩, ?_⟩
    exact (panelHeightClosure_iff A B hh hΔ β m hi hx.1).mpr
      ⟨s, hi, hs, hx.1, he⟩
  apply continuousOn_of_finite_closed_cover F hclosed hcover
  intro i
  apply (panelAffineRadius_continuous A B hh hΔ β m i.val).continuousOn.congr
  intro x hx
  obtain ⟨s, hs⟩ := (panelHeightClosure_iff A B hh hΔ β m
    (by omega : i.val ≤ N A B) hx.1.1).mp hx.2
  exact componentRadius_eq_affine A B hh hΔ β m hs

theorem componentRadius_locally_left (hΔ : 0 < Δ A B hh)
    (β : ℝ) (m : ℤ) :
    ∀ x ∈ rayHeightComponent A B hh hΔ β m,
      ∃ ε : ℝ, 0 < ε ∧
        ∀ y ∈ rayHeightComponent A B hh hΔ β m,
          x - ε < y → y < x →
            componentRadius A B hh hΔ β m x < componentRadius A B hh hΔ β m y := by
  let I := rayHeightComponent A B hh hΔ β m
  let F : Fin (N A B + 1) → Set ℝ := fun i => panelHeightClosure A B hh hΔ β m i.val
  have hclosed : ∀ i, IsClosed (F i) := fun i =>
    panelHeightClosure_closed A B hh hΔ β m (by omega)
  have hcover : ∀ x ∈ I, ∃ i, x ∈ F i := by
    intro x hx
    obtain ⟨i, hi, s, hs, he⟩ := hx.2
    refine ⟨⟨i, by omega⟩, ?_⟩
    exact (panelHeightClosure_iff A B hh hΔ β m hi hx.1).mpr
      ⟨s, hi, hs, hx.1, he⟩
  apply locally_left_of_finite_closed_cover F hclosed hcover
  intro i x y hx hy hxi hyi hxy
  obtain ⟨s, hs⟩ := (panelHeightClosure_iff A B hh hΔ β m
    (by omega : i.val ≤ N A B) hx.1).mp hxi
  obtain ⟨r, hr⟩ := (panelHeightClosure_iff A B hh hΔ β m
    (by omega : i.val ≤ N A B) hy.1).mp hyi
  exact componentRadius_strict_samePanel A B hh hΔ β m hs hr hxy

/-- Strict radial inwardness across all finite actual panel transitions. -/
theorem componentRadius_strict (hΔ : 0 < Δ A B hh)
    (β : ℝ) (m : ℤ) {t u : ℝ}
    (ht : t ∈ rayHeightComponent A B hh hΔ β m)
    (hu : u ∈ rayHeightComponent A B hh hΔ β m)
    (htu : t < u) :
    componentRadius A B hh hΔ β m u < componentRadius A B hh hΔ β m t := by
  apply continuousOn_strictAntiOn_of_locally_left
    (I := rayHeightComponent A B hh hΔ β m)
    (f := componentRadius A B hh hΔ β m)
  · constructor
    intro x hx y hy z hz
    exact rayHeightComponent_convex A B hh hΔ β m hx hy hz.1 hz.2
  · exact componentRadius_continuousOn A B hh hΔ β m
  · exact componentRadius_locally_left A B hh hΔ β m
  · exact ht
  · exact hu
  · exact htu

theorem rayHeightComponent_constant_unique (hΔ : 0 < Δ A B hh)
    (β : ℝ) (hα : ∀ t ∈ Ioo (0 : ℝ) 1,
      alpha A B hh hΔ t = alpha A B hh hΔ (1 / 2))
    {m₁ m₂ : ℤ}
    (h₁ : (rayHeightComponent A B hh hΔ β m₁).Nonempty)
    (h₂ : (rayHeightComponent A B hh hΔ β m₂).Nonempty) : m₁ = m₂ := by
  obtain ⟨t₁, ht₁⟩ := h₁
  obtain ⟨t₂, ht₂⟩ := h₂
  rw [rayHeightComponent_iff] at ht₁ ht₂
  by_contra hn
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · have hc : (m₁ : ℝ) + 1 ≤ (m₂ : ℝ) := by
      exact_mod_cast (show m₁ + 1 ≤ m₂ by omega)
    have hL := PhysicalMixedTurnSource.abs_intrinsicDelta_lt_two_pi A B hh
    rw [abs_of_nonneg hΔ.le] at hL
    rw [hα t₁ ht₁.1] at ht₁
    rw [hα t₂ ht₂.1] at ht₂
    nlinarith [ht₁.2.1, ht₂.2.2, Real.pi_pos]
  · have hc : (m₂ : ℝ) + 1 ≤ (m₁ : ℝ) := by
      exact_mod_cast (show m₂ + 1 ≤ m₁ by omega)
    have hL := PhysicalMixedTurnSource.abs_intrinsicDelta_lt_two_pi A B hh
    rw [abs_of_nonneg hΔ.le] at hL
    rw [hα t₁ ht₁.1] at ht₁
    rw [hα t₂ ht₂.1] at ht₂
    nlinarith [ht₂.2.1, ht₁.2.2, Real.pi_pos]

theorem rayHeightComponent_order (hΔ : 0 < Δ A B hh)
    (β : ℝ) {m₁ m₂ : ℤ} (hm : m₁ < m₂)
    {t u : ℝ} (ht : t ∈ rayHeightComponent A B hh hΔ β m₁)
    (hu : u ∈ rayHeightComponent A B hh hΔ β m₂) : t < u ∨ u < t := by
  rcases alpha_det_trichotomy A B hh hΔ with hinc | hdec | hconst
  · exact Or.inl (rayHeightComponent_order_of_mono A B hh hΔ β
      hinc.monotoneOn hm ht hu)
  · exact Or.inr (rayHeightComponent_order_of_anti A B hh hΔ β
      hdec.antitoneOn hm ht hu)
  · have hsame := rayHeightComponent_constant_unique A B hh hΔ β
      (by
        intro x hx
        rw [hconst x ⟨hx.1.le, hx.2.le⟩,
          hconst (1 / 2) (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)])
      ⟨t, ht⟩ ⟨u, hu⟩
    omega

theorem rayHeightComponent_relativelyClosed (hΔ : 0 < Δ A B hh)
    (β : ℝ) (m : ℤ) :
    ∃ F : Set ℝ, IsClosed F ∧
      rayHeightComponent A B hh hΔ β m = Ioo (0 : ℝ) 1 ∩ F := by
  let c := β + 2 * Real.pi * (m : ℝ)
  let F := Icc (0 : ℝ) 1 ∩
    (alpha A B hh hΔ) ⁻¹' Icc c (c + Δ A B hh)
  have hcont : ContinuousOn (alpha A B hh hΔ) (Icc (0 : ℝ) 1) :=
    pointPolarLift_continuousOn_height A B hh hΔ (by omega) (by norm_num)
  refine ⟨F, hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Icc, ?_⟩
  ext t
  rw [rayHeightComponent_iff]
  simp only [F, mem_inter_iff, mem_preimage, mem_Icc, mem_Ioo]
  constructor
  · rintro ⟨ht, hlo, hhi⟩
    exact ⟨ht, ⟨ht.1.le, ht.2.le⟩, hhi, by linarith⟩
  · rintro ⟨ht, hclosed, hhi, hlo⟩
    exact ⟨ht, by linarith, hhi⟩

/-- The chosen root seam radius is the selected positive normalized seam radius,
with the height reversal and the root-to-baseline isometry both explicit. -/
theorem normalized_root_seam_radius (hΔ : 0 < Δ A B hh) (t : ℝ) :
    ‖(normalizedStrip A B hh hΔ).point 0 0 t - normalizedPole A B hh hΔ‖ =
      ‖RadialOriginalSeam.selectedPositiveNormalizedSeamCurve A B hh hΔ t -
        RadialExtremalSafety.reflectPlane
          (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ))‖ := by
  let k := positiveRoot A B hh hΔ
  let T := PhysicalMixedTurnSource.baselineAlignment A B hh k
  have hs : T ((rootStrip A B hh k).point 0 0 (1 - t)) =
      PhysicalMixedTurnSource.developedLower A B hh 0 k.val +
        (1 - t) • RadialOriginalSeam.sourceHinge A B hh k := by
    rw [rootStrip_alignment]
    simp [RadialExtremalSafety.TriangularRadialStrip.point,
      FixedBaselinePolarRayGeometry.baselineStrip,
      RadialOriginalSeam.sourceHinge]
  have hp := PhysicalMixedTurnSource.baselineAlignment_circuitPole A B hh k
    (ne_of_gt hΔ)
  have hn := congrArg norm (T.map_vsub
    ((rootStrip A B hh k).point 0 0 (1 - t))
    (PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_gt hΔ)))
  rw [T.linearIsometry.norm_map, hs, hp] at hn
  have ht : 1 - (1 - t) = t := by ring
  rw [← ht, normalized_point, normalizedPole,
    ← RadialExtremalSafety.reflectPlane_sub,
    RadialExtremalSafety.reflectPlane_norm,
    RadialOriginalSeam.selectedPositiveNormalizedSeamCurve_eq_source]
  rw [← RadialExtremalSafety.reflectPlane_sub,
    RadialExtremalSafety.reflectPlane_norm]
  rw [show 1 - (1 - (1 - t)) = 1 - t by ring]
  simpa only [k, positiveRoot, vsub_eq_sub] using hn

/-- The terminal copy has the same source seam radius at each height. -/
theorem normalized_terminal_seam_radius (hΔ : 0 < Δ A B hh) (t : ℝ) :
    ‖(normalizedStrip A B hh hΔ).point (N A B) 1 t -
        normalizedPole A B hh hΔ‖ =
      ‖(normalizedStrip A B hh hΔ).point 0 0 t - normalizedPole A B hh hΔ‖ := by
  let S := normalizedStrip A B hh hΔ
  let O := normalizedPole A B hh hΔ
  let R := PhysicalMixedTurnSource.planeRotation (-Δ A B hh)
  have hc : S.point (N A B) 1 t - O = R (S.point 0 0 t - O) := by
    rw [normalized_virtualFinalHinge A B hh hΔ t]
    change RadialExtremalSafety.reflectPlane
        (PhysicalMixedTurnSource.fullCircuit A B hh (positiveRoot A B hh hΔ)
          (RadialExtremalSafety.reflectPlane (S.point 0 0 t))) - O = _
    have hfix := PhysicalMixedTurnSource.circuitPole_fixed A B hh
      (positiveRoot A B hh hΔ) (ne_of_gt hΔ)
    change PhysicalMixedTurnSource.fullCircuit A B hh
      (positiveRoot A B hh hΔ)
      (PhysicalMixedTurnSource.circuitPole A B hh
        (positiveRoot A B hh hΔ) (ne_of_gt hΔ)) = _ at hfix
    rw [show O = RadialExtremalSafety.reflectPlane
      (PhysicalMixedTurnSource.circuitPole A B hh
        (positiveRoot A B hh hΔ) (ne_of_gt hΔ)) from rfl,
      ← RadialExtremalSafety.reflectPlane_sub]
    conv_lhs => rw [← hfix]
    rw [PhysicalMixedTurnSource.fullCircuit_apply,
      PhysicalMixedTurnSource.fullCircuit_apply]
    have hsub : ∀ x y : Plane,
        PhysicalMixedTurnSource.planeRotation (Δ A B hh) x +
          PhysicalMixedTurnSource.directTranslation A B hh
            (positiveRoot A B hh hΔ) (N A B + 1) -
          (PhysicalMixedTurnSource.planeRotation (Δ A B hh) y +
            PhysicalMixedTurnSource.directTranslation A B hh
              (positiveRoot A B hh hΔ) (N A B + 1)) =
          PhysicalMixedTurnSource.planeRotation (Δ A B hh) (x - y) := by
      intro x y
      rw [map_sub]
      abel
    rw [hsub]
    have hreflect (z : Plane) :
        RadialExtremalSafety.reflectPlane
          (PhysicalMixedTurnSource.planeRotation (Δ A B hh) z) =
        R (RadialExtremalSafety.reflectPlane z) := by
      ext j
      fin_cases j <;> simp [R, PhysicalMixedTurnSource.planeRotation,
        PhysicalMixedTurnSource.planeRotationLinear,
        RadialExtremalSafety.reflectPlane, Real.cos_neg, Real.sin_neg] <;> ring
    rw [hreflect, RadialExtremalSafety.reflectPlane_sub,
      RadialExtremalSafety.reflectPlane_reflectPlane]
  rw [hc]
  exact R.norm_map _

theorem normalized_root_seam_inward (hΔ : 0 < Δ A B hh)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hst : s < t) :
    ‖(normalizedStrip A B hh hΔ).point 0 0 t - normalizedPole A B hh hΔ‖ <
      ‖(normalizedStrip A B hh hΔ).point 0 0 s - normalizedPole A B hh hΔ‖ := by
  rw [normalized_root_seam_radius A B hh hΔ t,
    normalized_root_seam_radius A B hh hΔ s]
  have hin := RadialOriginalSeam.selectedPositiveNormalizedSeamCurve_radiallyInward
    A B hh hΔ hs ht hst
  simpa only [Function.comp_apply, FixedBaselinePolarTrace.polarRadius_eq_norm] using hin

/-- Intermediate seam levels are attained at physical heights, not inferred
from a putative no-gap panel list. -/
private theorem alpha_intermediate (hΔ : 0 < Δ A B hh)
    {s t q : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hst : s ≤ t) (hlo : alpha A B hh hΔ s ≤ q)
    (hhi : q ≤ alpha A B hh hΔ t) :
    ∃ u ∈ Icc s t, alpha A B hh hΔ u = q := by
  have hc : ContinuousOn (alpha A B hh hΔ) (Icc s t) :=
    (pointPolarLift_continuousOn_height A B hh hΔ (by omega) (by norm_num)).mono (by
      intro x hx
      exact ⟨(lt_of_lt_of_le hs.1 hx.1).le,
        (lt_of_le_of_lt hx.2 ht.2).le⟩)
  obtain ⟨u, hu, he⟩ := (intermediate_value_Icc hst hc) ⟨hlo, hhi⟩
  exact ⟨u, hu, he⟩

/-- Actual facing terminal/root hits in the increasing seam case. -/
theorem facing_of_mono (hΔ : 0 < Δ A B hh)
    (β : ℝ) {m₁ m₂ : ℤ} (hm : m₂ = m₁ + 1)
    (hα : StrictMonoOn (alpha A B hh hΔ) (Icc (0 : ℝ) 1))
    {s t : ℝ} (hs : s ∈ rayHeightComponent A B hh hΔ β m₁)
    (ht : t ∈ rayHeightComponent A B hh hΔ β m₂) :
    ∃ b c : ℝ, s ≤ b ∧ b < c ∧ c ≤ t ∧
      b ∈ rayHeightComponent A B hh hΔ β m₁ ∧
      c ∈ rayHeightComponent A B hh hΔ β m₂ ∧
      pointPolarLift A B hh hΔ (N A B) 1 b =
        β + 2 * Real.pi * (m₁ : ℝ) ∧
      pointPolarLift A B hh hΔ 0 0 c =
        β + 2 * Real.pi * (m₂ : ℝ) ∧
      componentRadius A B hh hΔ β m₂ c < componentRadius A B hh hΔ β m₁ b := by
  have hst := rayHeightComponent_order_of_mono A B hh hΔ β
    hα.monotoneOn (by omega : m₁ < m₂) hs ht
  rw [rayHeightComponent_iff] at hs ht
  let q₁ := β + 2 * Real.pi * (m₁ : ℝ) + Δ A B hh
  let q₂ := β + 2 * Real.pi * (m₂ : ℝ)
  have hq : q₁ < q₂ := by
    have hlen := PhysicalMixedTurnSource.abs_intrinsicDelta_lt_two_pi A B hh
    rw [abs_of_nonneg hΔ.le] at hlen
    have hm' : (m₂ : ℝ) = (m₁ : ℝ) + 1 := by exact_mod_cast hm
    dsimp [q₁, q₂]
    rw [hm']
    nlinarith [Real.pi_pos]
  have hsc : alpha A B hh hΔ s ≤ q₁ := by dsimp [q₁]; linarith [hs.2.1]
  have hct : q₁ ≤ alpha A B hh hΔ t := by
    dsimp [q₁]; linarith [ht.2.2]
  obtain ⟨b, hbspan, hbval⟩ := alpha_intermediate A B hh hΔ
    hs.1 ht.1 hst.le hsc hct
  have hsc' : alpha A B hh hΔ s ≤ q₂ := by linarith
  have hct' : q₂ ≤ alpha A B hh hΔ t := ht.2.2
  obtain ⟨c, hcspan, hcval⟩ := alpha_intermediate A B hh hΔ
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
  have hbmem : b ∈ rayHeightComponent A B hh hΔ β m₁ := by
    rw [rayHeightComponent_iff]
    exact ⟨hbi, by dsimp [q₁] at hbval; linarith, by linarith [hbval]⟩
  have hcmem : c ∈ rayHeightComponent A B hh hΔ β m₂ := by
    rw [rayHeightComponent_iff]
    exact ⟨hci, by linarith [hcval], by linarith [hcval]⟩
  have hbe : pointPolarLift A B hh hΔ (N A B) 1 b =
      β + 2 * Real.pi * (m₁ : ℝ) := by
    rw [pointPolarLift_terminal A B hh hΔ ⟨hbi.1.le, hbi.2.le⟩]
    dsimp [q₁, alpha] at hbval
    linarith
  have hgap := normalized_root_seam_inward A B hh hΔ
    ⟨hbi.1.le, hbi.2.le⟩ ⟨hci.1.le, hci.2.le⟩ hbc
  rw [← normalized_terminal_seam_radius A B hh hΔ b] at hgap
  rw [← componentRadius_eq_hit A B hh hΔ β m₂
      (show MaterialHit A B hh hΔ β m₂ 0 0 c from
        ⟨by omega, by norm_num, hci, hcval⟩),
    ← componentRadius_eq_hit A B hh hΔ β m₁
      (show MaterialHit A B hh hΔ β m₁ (N A B) 1 b from
        ⟨le_refl _, by norm_num, hbi, hbe⟩)] at hgap
  exact ⟨b, c, hbspan.1, hbc, hcspan.2, hbmem, hcmem, hbe, hcval, hgap⟩

/-- Reversed seam order: root then terminal are the actual facing hits. -/
theorem facing_of_anti (hΔ : 0 < Δ A B hh)
    (β : ℝ) {m₁ m₂ : ℤ} (hm : m₂ = m₁ + 1)
    (hα : StrictAntiOn (alpha A B hh hΔ) (Icc (0 : ℝ) 1))
    {s t : ℝ} (hs : s ∈ rayHeightComponent A B hh hΔ β m₂)
    (ht : t ∈ rayHeightComponent A B hh hΔ β m₁) :
    ∃ b c : ℝ, s ≤ b ∧ b < c ∧ c ≤ t ∧
      b ∈ rayHeightComponent A B hh hΔ β m₂ ∧
      c ∈ rayHeightComponent A B hh hΔ β m₁ ∧
      pointPolarLift A B hh hΔ 0 0 b =
        β + 2 * Real.pi * (m₂ : ℝ) ∧
      pointPolarLift A B hh hΔ (N A B) 1 c =
        β + 2 * Real.pi * (m₁ : ℝ) ∧
      componentRadius A B hh hΔ β m₁ c < componentRadius A B hh hΔ β m₂ b := by
  have hst := rayHeightComponent_order_of_anti A B hh hΔ β
    hα.antitoneOn (by omega : m₁ < m₂) ht hs
  rw [rayHeightComponent_iff] at hs ht
  let q₁ := β + 2 * Real.pi * (m₁ : ℝ) + Δ A B hh
  let q₂ := β + 2 * Real.pi * (m₂ : ℝ)
  have hq : q₁ < q₂ := by
    have hlen := PhysicalMixedTurnSource.abs_intrinsicDelta_lt_two_pi A B hh
    rw [abs_of_nonneg hΔ.le] at hlen
    have hm' : (m₂ : ℝ) = (m₁ : ℝ) + 1 := by exact_mod_cast hm
    dsimp [q₁, q₂]
    rw [hm']
    nlinarith [Real.pi_pos]
  have hsc : q₂ ≤ alpha A B hh hΔ s := hs.2.2
  have hct : alpha A B hh hΔ t ≤ q₂ := by
    dsimp [q₂]; linarith [ht.2.1]
  have hc : ContinuousOn (alpha A B hh hΔ) (Icc s t) :=
    (pointPolarLift_continuousOn_height A B hh hΔ (by omega) (by norm_num)).mono (by
      intro x hx
      exact ⟨(lt_of_lt_of_le hs.1.1 hx.1).le,
        (lt_of_le_of_lt hx.2 ht.1.2).le⟩)
  obtain ⟨b, hbspan, hbval⟩ := (intermediate_value_Icc' hst.le hc) ⟨hct, hsc⟩
  have hsc' : q₁ ≤ alpha A B hh hΔ s := by linarith
  have hct' : alpha A B hh hΔ t ≤ q₁ := by
    dsimp [q₁]; linarith [ht.2.1]
  obtain ⟨c, hcspan, hcval⟩ := (intermediate_value_Icc' hst.le hc) ⟨hct', hsc'⟩
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
  have hbmem : b ∈ rayHeightComponent A B hh hΔ β m₂ := by
    rw [rayHeightComponent_iff]
    exact ⟨hbi, by linarith [hbval], by linarith [hbval]⟩
  have hcmem : c ∈ rayHeightComponent A B hh hΔ β m₁ := by
    rw [rayHeightComponent_iff]
    exact ⟨hci, by dsimp [q₁] at hcval; linarith, by linarith [hcval]⟩
  have hce : pointPolarLift A B hh hΔ (N A B) 1 c =
      β + 2 * Real.pi * (m₁ : ℝ) := by
    rw [pointPolarLift_terminal A B hh hΔ ⟨hci.1.le, hci.2.le⟩]
    dsimp [q₁, alpha] at hcval
    linarith
  have hgap := normalized_root_seam_inward A B hh hΔ
    ⟨hbi.1.le, hbi.2.le⟩ ⟨hci.1.le, hci.2.le⟩ hbc
  rw [← normalized_terminal_seam_radius A B hh hΔ c] at hgap
  rw [← componentRadius_eq_hit A B hh hΔ β m₁
      (show MaterialHit A B hh hΔ β m₁ (N A B) 1 c from
        ⟨le_refl _, by norm_num, hci, hce⟩),
    ← componentRadius_eq_hit A B hh hΔ β m₂
      (show MaterialHit A B hh hΔ β m₂ 0 0 b from
        ⟨by omega, by norm_num, hbi, hbval⟩)] at hgap
  exact ⟨b, c, hbspan.1, hbc, hcspan.2, hbmem, hcmem, hbval, hce, hgap⟩

/-- Distinct actual representatives have disjoint radial ranges, using the
literal facing seam hits and strict order within each component. -/
theorem componentRadius_cross_strict (hΔ : 0 < Δ A B hh)
    (β : ℝ) {m₁ m₂ : ℤ} (hm : m₁ < m₂)
    {t u : ℝ} (ht : t ∈ rayHeightComponent A B hh hΔ β m₁)
    (hu : u ∈ rayHeightComponent A B hh hΔ β m₂) :
    componentRadius A B hh hΔ β m₂ u < componentRadius A B hh hΔ β m₁ t ∨
      componentRadius A B hh hΔ β m₁ t < componentRadius A B hh hΔ β m₂ u := by
  have hnext := rayHeightComponent_consecutive A B hh hΔ β hm ⟨t, ht⟩ ⟨u, hu⟩
  rcases alpha_det_trichotomy A B hh hΔ with hmono | hanti | hconst
  · obtain ⟨b, c, htb, hbc, hcu, hb, hc, hbe, hce, hgap⟩ :=
      facing_of_mono A B hh hΔ β hnext hmono ht hu
    have hleft : componentRadius A B hh hΔ β m₁ b ≤
        componentRadius A B hh hΔ β m₁ t := by
      rcases htb.eq_or_lt with heq | hlt
      · rw [← heq]
      · exact (componentRadius_strict A B hh hΔ β m₁ ht hb hlt).le
    have hright : componentRadius A B hh hΔ β m₂ u ≤
        componentRadius A B hh hΔ β m₂ c := by
      rcases hcu.eq_or_lt with heq | hlt
      · rw [heq]
      · exact (componentRadius_strict A B hh hΔ β m₂ hc hu hlt).le
    exact Or.inl (lt_of_le_of_lt hright (lt_of_lt_of_le hgap hleft))
  · obtain ⟨b, c, hub, hbc, hct, hb, hc, hbe, hce, hgap⟩ :=
      facing_of_anti A B hh hΔ β hnext hanti hu ht
    have hleft : componentRadius A B hh hΔ β m₂ b ≤
        componentRadius A B hh hΔ β m₂ u := by
      rcases hub.eq_or_lt with heq | hlt
      · rw [← heq]
      · exact (componentRadius_strict A B hh hΔ β m₂ hu hb hlt).le
    have hright : componentRadius A B hh hΔ β m₁ t ≤
        componentRadius A B hh hΔ β m₁ c := by
      rcases hct.eq_or_lt with heq | hlt
      · rw [heq]
      · exact (componentRadius_strict A B hh hΔ β m₁ hc ht hlt).le
    exact Or.inr (lt_of_le_of_lt hright (lt_of_lt_of_le hgap hleft))
  · have heq := rayHeightComponent_constant_unique A B hh hΔ β
      (by
        intro x hx
        rw [hconst x ⟨hx.1.le, hx.2.le⟩,
          hconst (1 / 2) (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)])
      ⟨t, ht⟩ ⟨u, hu⟩
    omega

/-- Arbitrary material hits of the same positive physical ray at different
normalized heights cannot be coincident, even on different panels. -/
theorem materialHit_point_ne_of_height_ne (hΔ : 0 < Δ A B hh)
    (β : ℝ) {m₁ m₂ : ℤ} {i j : ℕ} {s₁ s₂ t u : ℝ}
    (h₁ : MaterialHit A B hh hΔ β m₁ i s₁ t)
    (h₂ : MaterialHit A B hh hΔ β m₂ j s₂ u)
    (htu : t ≠ u) :
    (normalizedStrip A B hh hΔ).point i s₁ t ≠
      (normalizedStrip A B hh hΔ).point j s₂ u := by
  let O := normalizedPole A B hh hΔ
  have ht : t ∈ rayHeightComponent A B hh hΔ β m₁ :=
    ⟨h₁.2.2.1, i, h₁.1, s₁, h₁.2.1, h₁.2.2.2⟩
  have hu : u ∈ rayHeightComponent A B hh hΔ β m₂ :=
    ⟨h₂.2.2.1, j, h₂.1, s₂, h₂.2.1, h₂.2.2.2⟩
  have hr₁ := componentRadius_eq_hit A B hh hΔ β m₁ h₁
  have hr₂ := componentRadius_eq_hit A B hh hΔ β m₂ h₂
  intro heq
  have hre : componentRadius A B hh hΔ β m₁ t =
      componentRadius A B hh hΔ β m₂ u := by
    rw [hr₁, hr₂, heq]
  by_cases hm : m₁ = m₂
  · subst m₂
    rcases lt_or_gt_of_ne htu with hlt | hgt
    · exact (ne_of_gt (componentRadius_strict A B hh hΔ β m₁ ht hu hlt)) hre
    · exact (ne_of_gt (componentRadius_strict A B hh hΔ β m₁ hu ht hgt)) hre.symm
  · rcases lt_or_gt_of_ne hm with hlt | hgt
    · rcases componentRadius_cross_strict A B hh hΔ β hlt ht hu with h | h
      · exact (ne_of_gt h) hre
      · exact (ne_of_gt h) hre.symm
    · rcases componentRadius_cross_strict A B hh hΔ β hgt hu ht with h | h
      · exact (ne_of_gt h) hre.symm
      · exact (ne_of_gt h) hre

theorem materialHit_collision_classification (hΔ : 0 < Δ A B hh)
    (β : ℝ) {m₁ m₂ : ℤ} {i j : ℕ} {s₁ s₂ t u : ℝ}
    (h₁ : MaterialHit A B hh hΔ β m₁ i s₁ t)
    (h₂ : MaterialHit A B hh hΔ β m₂ j s₂ u)
    (heq : (normalizedStrip A B hh hΔ).point i s₁ t =
      (normalizedStrip A B hh hΔ).point j s₂ u) :
    t = u ∧ m₁ = m₂ ∧
      (i = j ∨ (j = i + 1 ∧ s₁ = 1 ∧ s₂ = 0) ∨
        (i = j + 1 ∧ s₂ = 1 ∧ s₁ = 0)) := by
  have htu : t = u := by
    by_contra hn
    exact (materialHit_point_ne_of_height_ne A B hh hΔ β h₁ h₂ hn) heq
  subst u
  exact ⟨rfl, (materialHit_sameHeight A B hh hΔ β h₁ h₂).1,
    materialHit_sameHeight_hinge A B hh hΔ β h₁ h₂⟩

theorem materialHit_distinct_faceInteriors_ne (hΔ : 0 < Δ A B hh)
    (β : ℝ) {m₁ m₂ : ℤ} {i j : ℕ} {s₁ s₂ t u : ℝ}
    (h₁ : MaterialHit A B hh hΔ β m₁ i s₁ t)
    (h₂ : MaterialHit A B hh hΔ β m₂ j s₂ u)
    (hi : i ≠ j) (hs₁ : s₁ ∈ Ioo (0 : ℝ) 1)
    (hs₂ : s₂ ∈ Ioo (0 : ℝ) 1) :
    (normalizedStrip A B hh hΔ).point i s₁ t ≠
      (normalizedStrip A B hh hΔ).point j s₂ u := by
  intro heq
  obtain ⟨_, _, hfaces⟩ := materialHit_collision_classification A B hh hΔ β h₁ h₂ heq
  rcases hfaces with heq | hforward | hbackward
  · exact hi heq
  · exact (ne_of_lt hs₁.2) hforward.2.1
  · exact (ne_of_lt hs₂.2) hbackward.2.1

/-- The normalized source seam cannot meet the full-circuit terminal seam
at different actual heights of distinct representatives. -/
theorem crossComponent_seam_allPairs_ne (hΔ : 0 < Δ A B hh)
    (β : ℝ) {m₁ m₂ : ℤ} (hm : m₁ < m₂)
    {s t : ℝ} (hs : s ∈ rayHeightComponent A B hh hΔ β m₁)
    (ht : t ∈ rayHeightComponent A B hh hΔ β m₂) :
    (normalizedStrip A B hh hΔ).point 0 0 s ≠
      (normalizedStrip A B hh hΔ).point (N A B) 1 t := by
  have hne : s ≠ t := by
    rcases rayHeightComponent_order A B hh hΔ β hm hs ht with h | h
    · exact ne_of_lt h
    · exact ne_of_gt h
  have hsi := (rayHeightComponent_iff A B hh hΔ β m₁ s).mp hs |>.1
  have hti := (rayHeightComponent_iff A B hh hΔ β m₂ t).mp ht |>.1
  intro heq
  have hr := congrArg (fun p => ‖p - normalizedPole A B hh hΔ‖) heq
  rw [normalized_terminal_seam_radius A B hh hΔ t] at hr
  rcases lt_or_gt_of_ne hne with h | h
  · exact (ne_of_gt (normalized_root_seam_inward A B hh hΔ
      ⟨hsi.1.le, hsi.2.le⟩ ⟨hti.1.le, hti.2.le⟩ h)) hr
  · exact (ne_of_gt (normalized_root_seam_inward A B hh hΔ
      ⟨hti.1.le, hti.2.le⟩ ⟨hsi.1.le, hsi.2.le⟩ h)) hr.symm

/-- Reflection is injective, and normalization reverses height without
changing either panel or longitudinal coordinates. -/
theorem normalized_point_eq_iff_source (hΔ : 0 < Δ A B hh)
    (i j : ℕ) (s₁ s₂ t u : ℝ) :
    (normalizedStrip A B hh hΔ).point i s₁ (1 - t) =
      (normalizedStrip A B hh hΔ).point j s₂ (1 - u) ↔
    (rootStrip A B hh (positiveRoot A B hh hΔ)).point i s₁ t =
      (rootStrip A B hh (positiveRoot A B hh hΔ)).point j s₂ u := by
  rw [normalized_point A B hh hΔ i s₁ t,
    normalized_point A B hh hΔ j s₂ u]
  constructor
  · intro heq
    have h := congrArg RadialExtremalSafety.reflectPlane heq
    simpa only [RadialExtremalSafety.reflectPlane_reflectPlane] using h
  · exact congrArg RadialExtremalSafety.reflectPlane

end
end SelectedPositiveRootPolarLift
