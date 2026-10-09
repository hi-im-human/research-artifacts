import FixedBaselinePolarTrace

open Set
open scoped BigOperators Classical NNReal
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CommonSupportMerge OriginalFacetCertificates NormalFanSplice MaximalSupportCells
open CyclicCutOrders EuclideanPrismatoidCoordinates PolyhedralInputBridge
open TrimmedFacetWitnesses BandGeometryAssembly FiniteWitnessClosure SingleCutRecovery
open CutSurfaceQuotient MixedTurnSafeCut PolygonSetReconstruction ConvexPolygonTurning

namespace RadialOriginalSeam
noncomputable section
set_option maxHeartbeats 8000000

abbrev Plane := MixedTurnSafeCut.Plane

section Coefficients

/-- The vector from the pole to an original upper seam endpoint. -/
def upperVector (O U : Plane) : Plane := U - O

/-- The point at retained upper height `1 - δ`, written from the original upper
endpoint.  This formula remains valid when either horizontal rim run vanishes. -/
def retainedUpperVector (O U G : Plane) (δ : ℝ) : Plane :=
  upperVector O U - δ • G

/-- Exact coefficient triple for the squared retained-upper radius. -/
def radiusCoeff0 (O U : Plane) : ℝ := ‖upperVector O U‖ ^ 2

def radiusCoeff1 (O U G : Plane) : ℝ := -2 * inner ℝ (upperVector O U) G

def radiusCoeff2 (G : Plane) : ℝ := ‖G‖ ^ 2

/-- No asymptotic remainder is hidden in the selector: retained squared radius
is literally a quadratic polynomial in trim depth. -/
theorem retainedUpper_normSq (O U G : Plane) (δ : ℝ) :
    ‖retainedUpperVector O U G δ‖ ^ 2 =
      radiusCoeff0 O U + δ * radiusCoeff1 O U G +
        δ ^ 2 * radiusCoeff2 G := by
  rw [retainedUpperVector, sub_eq_add_neg,
    RadialExtremalSafety.norm_sq_add]
  simp only [inner_neg_right, inner_smul_right, norm_neg, norm_smul,
    Real.norm_eq_abs, radiusCoeff0, radiusCoeff1, radiusCoeff2]
  rw [mul_pow, sq_abs]
  ring

/-- A finite family has one trim-independent member maximizing the exact
retained-upper quadratic at every sufficiently small positive depth.  Equal
coefficient triples are intentionally permitted. -/
theorem exists_fixed_eventual_retainedUpper_max
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (O : Plane) (U G : ι → Plane) :
    ∃ k ε, 0 < ε ∧ ∀ i δ, 0 < δ → δ < ε →
      ‖retainedUpperVector O (U i) (G i) δ‖ ^ 2 ≤
        ‖retainedUpperVector O (U k) (G k) δ‖ ^ 2 := by
  let c₀ : ι → ℝ := fun i => radiusCoeff0 O (U i)
  let c₁ : ι → ℝ := fun i => radiusCoeff1 O (U i) (G i)
  let c₂ : ι → ℝ := fun i => radiusCoeff2 (G i)
  obtain ⟨k, ε, hε, hk⟩ :=
    RadialExtremalSafety.exists_eventual_quadratic_max c₀ c₁ c₂
  refine ⟨k, ε, hε, ?_⟩
  intro i δ hδ hδε
  have h := hk i δ hδ hδε
  rw [retainedUpper_normSq, retainedUpper_normSq]
  exact h

/-- Data returned by the fixed finite selector.  It stores only its computed
index and threshold; the correctness theorem is proved below, not supplied by a
caller. -/
structure FixedRetainedUpperChoice (ι : Type*) where
  index : ι
  threshold : ℝ

noncomputable def fixedRetainedUpperChoice
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (O : Plane) (U G : ι → Plane) : FixedRetainedUpperChoice ι :=
  let w := Classical.choose (exists_fixed_eventual_retainedUpper_max O U G)
  ⟨w, Classical.choose (Classical.choose_spec
    (exists_fixed_eventual_retainedUpper_max O U G))⟩

theorem fixedRetainedUpperChoice_spec
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (O : Plane) (U G : ι → Plane) :
    0 < (fixedRetainedUpperChoice O U G).threshold ∧
      ∀ i δ, 0 < δ → δ < (fixedRetainedUpperChoice O U G).threshold →
        ‖retainedUpperVector O (U i) (G i) δ‖ ^ 2 ≤
          ‖retainedUpperVector O
            (U (fixedRetainedUpperChoice O U G).index)
            (G (fixedRetainedUpperChoice O U G).index) δ‖ ^ 2 := by
  exact Classical.choose_spec (Classical.choose_spec
    (exists_fixed_eventual_retainedUpper_max O U G))

/-- The weak endpoint derivative, together with the physical nonzero hinge, is
exactly enough for strict distance decrease.  No strict endpoint dot inequality
is required. -/
theorem radiallyInward_of_weak_endpoint
    {O U G : Plane} (hG : G ≠ 0)
    (hUG : inner ℝ (U - O) G ≤ 0) :
    FixedBaselinePolarTrace.RadiallyInward O
      (fun t => O + RadialExtremalSafety.hingePoint (U - O) G t) := by
  intro s hs t ht hst
  change ‖FixedBaselinePolarTrace.planeComplex
      ((O + RadialExtremalSafety.hingePoint (U - O) G t) - O)‖ <
    ‖FixedBaselinePolarTrace.planeComplex
      ((O + RadialExtremalSafety.hingePoint (U - O) G s) - O)‖
  have hsq := RadialExtremalSafety.hinge_normSq_strictAntiOn hG hUG hs ht hst
  have hnorm (x : Plane) : ‖FixedBaselinePolarTrace.planeComplex x‖ = ‖x‖ := by
    simp only [FixedBaselinePolarTrace.planeComplex, Complex.norm_def,
      Complex.normSq_apply, EuclideanSpace.norm_eq, Fin.sum_univ_two,
      Real.norm_eq_abs, sq_abs]
    congr 1
    ring
  rw [hnorm, hnorm]
  simp only [add_sub_cancel_left]
  have hnt := norm_nonneg (RadialExtremalSafety.hingePoint (U - O) G t)
  have hns := norm_nonneg (RadialExtremalSafety.hingePoint (U - O) G s)
  nlinarith

/-- The complete local maximum-radius argument, including ties.  The two
neighbor comparisons produce the incident dot bounds; radial support derives
convexity of this one corner; coherent panel orientation puts the hinge in the
strict positive cone generated by `-f` and `e`. -/
theorem extremal_corner_hinge_dot_neg {a f e G : Plane}
    (ha : a ≠ 0)
    (hprev : ‖a - f‖ ^ 2 ≤ ‖a‖ ^ 2)
    (hnext : ‖a + e‖ ^ 2 ≤ ‖a‖ ^ 2)
    (haf_det : MixedTurnSafeCut.det a f < 0)
    (hae_det : MixedTurnSafeCut.det a e < 0)
    (hfG : MixedTurnSafeCut.det f G < 0)
    (heG : MixedTurnSafeCut.det e G < 0) :
    inner ℝ a G < 0 := by
  have hf : f ≠ 0 := by
    intro h
    rw [h] at haf_det
    simp [MixedTurnSafeCut.det] at haf_det
  have he : e ≠ 0 := by
    intro h
    rw [h] at hae_det
    simp [MixedTurnSafeCut.det] at hae_det
  have haf : 0 < inner ℝ a f :=
    RadialExtremalSafety.incoming_dot_pos hf hprev
  have hae : inner ℝ a e < 0 :=
    RadialExtremalSafety.outgoing_dot_neg he hnext
  have hfe : MixedTurnSafeCut.det f e < 0 :=
    RadialExtremalSafety.det_incident_neg ha haf hae haf_det hae_det
  exact RadialExtremalSafety.inner_hinge_neg_of_incident_cone haf hae
    (RadialExtremalSafety.hinge_in_negative_positive_cone hfe hfG heG)

/-- Elementary one-sided limiting step used for triangular source facets.  It
passes only the scalar affine endpoint expression to depth zero; no seam or map
is selected by a limit. -/
theorem weak_endpoint_of_eventual_strict
    {U G : Plane} {ε : ℝ} (hε : 0 < ε)
    (hsmall : ∀ δ, 0 < δ → δ < ε →
      inner ℝ (U - δ • G) G < 0) :
    inner ℝ U G ≤ 0 := by
  by_contra hnot
  have hUG : 0 < inner ℝ U G := lt_of_not_ge hnot
  by_cases hG : G = 0
  · subst G
    simpa using hUG
  · have hn : 0 < ‖G‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hG)
    let δ := min (ε / 2) (inner ℝ U G / (2 * ‖G‖ ^ 2))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδε : δ < ε := by
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hbound : δ * ‖G‖ ^ 2 ≤ inner ℝ U G / 2 := by
      have hle := min_le_right (ε / 2) (inner ℝ U G / (2 * ‖G‖ ^ 2))
      have hm := mul_le_mul_of_nonneg_right hle (sq_nonneg ‖G‖)
      field_simp [ne_of_gt hn] at hm
      nlinarith
    have hs := hsmall δ hδ hδε
    rw [inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq] at hs
    simp only [starRingEnd_apply, star_trivial] at hs
    nlinarith

/-- Local extremal-corner theorem specialized to a genuine interior entry
hinge of a radially supported triangular strip.  The only maximum data are the
actual two neighboring retained upper endpoints. -/
theorem interior_entry_hinge_dot_neg
    {n : ℕ} (S : RadialExtremalSafety.TriangularRadialStrip n) (O : Plane)
    (hR : S.RadialSupport O)
    (hcoeff : ∀ j ≤ n, 0 < S.lowerCoeff j + S.upperCoeff j)
    {i : ℕ} (hi0 : 0 < i) (hin : i ≤ n)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hprev : ‖S.point (i - 1) 0 t - O‖ ^ 2 ≤
      ‖S.point i 0 t - O‖ ^ 2)
    (hnext : ‖S.point i 1 t - O‖ ^ 2 ≤
      ‖S.point i 0 t - O‖ ^ 2) :
    inner ℝ (S.point i 0 t - O) (S.d i) < 0 := by
  let ρprev := (1 - t) * S.lowerCoeff (i - 1) +
    t * S.upperCoeff (i - 1)
  let ρnext := (1 - t) * S.lowerCoeff i + t * S.upperCoeff i
  let a := S.point i 0 t - O
  let f := ρprev • S.v (i - 1)
  let e := ρnext • S.v i
  let G := S.d i
  have hip : i - 1 < n := by omega
  have hip_le : i - 1 ≤ n := by omega
  have hρprev : 0 < ρprev := by
    dsimp [ρprev]
    have hlo := S.lowerCoeff_nonneg (i - 1) hip_le
    have hup := S.upperCoeff_nonneg (i - 1) hip_le
    have hsum := hcoeff (i - 1) hip_le
    by_cases hup0 : S.upperCoeff (i - 1) = 0
    · have hlo0 : 0 < S.lowerCoeff (i - 1) := by linarith
      exact add_pos_of_pos_of_nonneg
        (mul_pos (sub_pos.mpr ht.2) hlo0) (mul_nonneg ht.1.le hup)
    · have hup_pos : 0 < S.upperCoeff (i - 1) := lt_of_le_of_ne hup (Ne.symm hup0)
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr ht.2.le) hlo) (mul_pos ht.1 hup_pos)
  have hρnext : 0 < ρnext := by
    dsimp [ρnext]
    have hlo := S.lowerCoeff_nonneg i hin
    have hup := S.upperCoeff_nonneg i hin
    have hsum := hcoeff i hin
    by_cases hup0 : S.upperCoeff i = 0
    · have hlo0 : 0 < S.lowerCoeff i := by linarith
      exact add_pos_of_pos_of_nonneg
        (mul_pos (sub_pos.mpr ht.2) hlo0) (mul_nonneg ht.1.le hup)
    · have hup_pos : 0 < S.upperCoeff i := lt_of_le_of_ne hup (Ne.symm hup0)
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr ht.2.le) hlo) (mul_pos ht.1 hup_pos)
  have hidx : i - 1 + 1 = i := by omega
  have hglue : S.point (i - 1) 1 t = S.point i 0 t := by
    simpa only [hidx] using FixedBaselinePolarTrace.point_exit_eq_next_entry S hip t
  have haf : a - f = S.point (i - 1) 0 t - O := by
    dsimp [a, f, ρprev]
    rw [← hglue]
    simp only [RadialExtremalSafety.TriangularRadialStrip.point]
    module
  have hae : a + e = S.point i 1 t - O := by
    dsimp [a, e, ρnext]
    simp only [RadialExtremalSafety.TriangularRadialStrip.point]
    module
  have ha0 : a ≠ 0 := sub_ne_zero.mpr
    (RadialExtremalSafety.TriangularRadialStrip.point_ne_pole hR hin
      (by norm_num) ⟨ht.1.le, ht.2.le⟩)
  have hafdet : MixedTurnSafeCut.det a f < 0 := by
    have hs := RadialExtremalSafety.TriangularRadialStrip.support_point hR hip_le
      (s := (1 : ℝ)) (t := t) (by norm_num) ⟨ht.1.le, ht.2.le⟩
    rw [hglue] at hs
    dsimp [a, f]
    rw [RadialExtremalSafety.det_smul_right]
    exact mul_neg_of_pos_of_neg hρprev hs
  have haedet : MixedTurnSafeCut.det a e < 0 := by
    have hs := RadialExtremalSafety.TriangularRadialStrip.support_point hR hin
      (s := (0 : ℝ)) (t := t) (by norm_num) ⟨ht.1.le, ht.2.le⟩
    dsimp [a, e]
    rw [RadialExtremalSafety.det_smul_right]
    exact mul_neg_of_pos_of_neg hρnext hs
  have hfg : MixedTurnSafeCut.det f G < 0 := by
    have hstep := S.hinge_step (i - 1) hip
    rw [hidx] at hstep
    have horient := S.orientation_neg (i - 1) hip_le
    dsimp [f, G]
    rw [RadialExtremalSafety.det_smul_left]
    have heq : MixedTurnSafeCut.det (S.v (i - 1)) (S.d i) =
        MixedTurnSafeCut.det (S.v (i - 1)) (S.d (i - 1)) := by
      rw [hstep]
      simp [MixedTurnSafeCut.det]
      ring
    rw [heq]
    exact mul_neg_of_pos_of_neg hρprev horient
  have heg : MixedTurnSafeCut.det e G < 0 := by
    have horient := S.orientation_neg i hin
    dsimp [e, G]
    rw [RadialExtremalSafety.det_smul_left]
    exact mul_neg_of_pos_of_neg hρnext horient
  have hmaxprev : ‖a - f‖ ^ 2 ≤ ‖a‖ ^ 2 := by
    rw [haf]
    exact hprev
  have hmaxnext : ‖a + e‖ ^ 2 ≤ ‖a‖ ^ 2 := by
    rw [hae]
    exact hnext
  have hdot := extremal_corner_hinge_dot_neg ha0
    hmaxprev hmaxnext hafdet haedet hfg heg
  exact hdot

end Coefficients

section Source

variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

abbrev SeamIndex := Fin (PhysicalMixedTurnSource.MechanismN A B + 1)

noncomputable def sourceUpper
    (i : SeamIndex A B) : Plane :=
  PhysicalMixedTurnSource.developedUpper A B hh 0 i.val

noncomputable def sourceHinge
    (i : SeamIndex A B) : Plane :=
  PhysicalMixedTurnSource.developedUpper A B hh 0 i.val -
    PhysicalMixedTurnSource.developedLower A B hh 0 i.val

/-- The selected original seam is computed once from the source and the genuine
circuit pole.  In particular its index does not depend on trim depth. -/
noncomputable def selectedNegativeSeam
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0) :
    FixedRetainedUpperChoice (SeamIndex A B) :=
  fixedRetainedUpperChoice
    (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
    (sourceUpper A B hh) (sourceHinge A B hh)

/-- Exact eventual-max certificate for the one source-selected negative seam. -/
theorem selectedNegativeSeam_spec
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0) :
    0 < (selectedNegativeSeam A B hh hΔ).threshold ∧
      ∀ i δ, 0 < δ → δ < (selectedNegativeSeam A B hh hΔ).threshold →
        ‖retainedUpperVector
          (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
          (sourceUpper A B hh i) (sourceHinge A B hh i) δ‖ ^ 2 ≤
        ‖retainedUpperVector
          (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
          (sourceUpper A B hh (selectedNegativeSeam A B hh hΔ).index)
          (sourceHinge A B hh (selectedNegativeSeam A B hh hΔ).index) δ‖ ^ 2 :=
  fixedRetainedUpperChoice_spec _ _ _

/-- The selector's quadratic vector is literally the centered point on the
corresponding original developed hinge at physical height `1 - δ`. -/
lemma retainedUpperVector_eq_baselinePoint
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    (i : SeamIndex A B) (δ : ℝ) :
    retainedUpperVector
        (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
        (sourceUpper A B hh i) (sourceHinge A B hh i) δ =
      (FixedBaselinePolarRayGeometry.baselineStrip A B hh).point
          i.val 0 (1 - δ) -
        PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ) := by
  simp only [retainedUpperVector, upperVector, sourceUpper, sourceHinge,
    RadialExtremalSafety.TriangularRadialStrip.point,
    FixedBaselinePolarRayGeometry.baselineStrip]
  module

/-- If the source-selected seam is not the baseline root, its eventual
quadratic maximality and the physical radial support hypotheses force the
strict retained-endpoint hinge dot inequality. -/
theorem selectedNegativeSeam_retained_dot_neg_of_index_pos
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hδmax : δ < (selectedNegativeSeam A B hh hΔ).threshold)
    (hk0 : 0 < (selectedNegativeSeam A B hh hΔ).index.val) :
    inner ℝ
      (retainedUpperVector
        (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
        (sourceUpper A B hh (selectedNegativeSeam A B hh hΔ).index)
        (sourceHinge A B hh (selectedNegativeSeam A B hh hΔ).index) δ)
      (sourceHinge A B hh (selectedNegativeSeam A B hh hΔ).index) < 0 := by
  let S := FixedBaselinePolarRayGeometry.baselineStrip A B hh
  let O := PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)
  let k := (selectedNegativeSeam A B hh hΔ).index
  have hkN : k.val ≤ PhysicalMixedTurnSource.MechanismN A B := by
    exact Nat.le_of_lt_succ k.isLt
  have hcoeff : ∀ j ≤ PhysicalMixedTurnSource.MechanismN A B,
      0 < S.lowerCoeff j + S.upperCoeff j := by
    intro j hj
    exact PhysicalMixedTurnSource.lowerRunCoeff_add_upperRunCoeff_pos A B hh
      (PhysicalMixedTurnSource.familySource A B 0 j)
  have hprevIndex : k.val - 1 < PhysicalMixedTurnSource.MechanismN A B + 1 := by
    omega
  let kp : SeamIndex A B := ⟨k.val - 1, hprevIndex⟩
  have hmax := (selectedNegativeSeam_spec A B hh hΔ).2
  have hprev0 := hmax kp δ hδ0 hδmax
  have hprev : ‖S.point (k.val - 1) 0 (1 - δ) - O‖ ^ 2 ≤
      ‖S.point k.val 0 (1 - δ) - O‖ ^ 2 := by
    rw [← retainedUpperVector_eq_baselinePoint A B hh hΔ kp δ,
      ← retainedUpperVector_eq_baselinePoint A B hh hΔ k δ]
    exact hprev0
  have hnext : ‖S.point k.val 1 (1 - δ) - O‖ ^ 2 ≤
      ‖S.point k.val 0 (1 - δ) - O‖ ^ 2 := by
    by_cases hklt : k.val < PhysicalMixedTurnSource.MechanismN A B
    · let kn : SeamIndex A B := ⟨k.val + 1, by omega⟩
      have hn0 := hmax kn δ hδ0 hδmax
      have hglue := FixedBaselinePolarTrace.point_exit_eq_next_entry S hklt (1 - δ)
      rw [hglue, ← retainedUpperVector_eq_baselinePoint A B hh hΔ kn δ,
        ← retainedUpperVector_eq_baselinePoint A B hh hΔ k δ]
      exact hn0
    · have hkEq : k.val = PhysicalMixedTurnSource.MechanismN A B := by omega
      have hroot0 := hmax (0 : SeamIndex A B) δ hδ0 hδmax
      have hcopy := FixedBaselinePolarRayGeometry.terminalPanelPoint_eq_fullCircuit_rootPoint
        A B hh (1 - δ)
      have hnorm := FixedBaselinePolarRayGeometry.fullCircuit_sub_pole A B hh
        (ne_of_lt hΔ) (S.point 0 0 (1 - δ))
      have hnorm' : ‖S.point (PhysicalMixedTurnSource.MechanismN A B) 1
            (1 - δ) - O‖ = ‖S.point 0 0 (1 - δ) - O‖ := by
        rw [hcopy, hnorm, (PhysicalMixedTurnSource.planeRotation _).norm_map]
      rw [retainedUpperVector_eq_baselinePoint A B hh hΔ
        (0 : SeamIndex A B) δ,
        retainedUpperVector_eq_baselinePoint A B hh hΔ k δ] at hroot0
      dsimp [S, O] at hroot0 ⊢
      rw [hkEq, hnorm']
      simpa only [hkEq] using hroot0
  have hdot := interior_entry_hinge_dot_neg S O
    (FixedBaselinePolarRayGeometry.baselineStrip_radialSupport A B hh hΔ)
    hcoeff hk0 hkN (t := 1 - δ) (by constructor <;> linarith)
    hprev hnext
  rw [retainedUpperVector_eq_baselinePoint A B hh hΔ k δ]
  change inner ℝ (S.point k.val 0 (1 - δ) - O) (S.d k.val) < 0
  exact hdot

/-- Root-index endpoint case, proved at the literal terminal full-circuit copy
so that both incident horizontal edges are present in one developed sheet. -/
theorem selectedNegativeSeam_retained_dot_neg_of_index_zero
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < (1 : ℝ) / 2)
    (hδmax : δ < (selectedNegativeSeam A B hh hΔ).threshold)
    (hk0 : (selectedNegativeSeam A B hh hΔ).index.val = 0) :
    inner ℝ
      (retainedUpperVector
        (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
        (sourceUpper A B hh (selectedNegativeSeam A B hh hΔ).index)
        (sourceHinge A B hh (selectedNegativeSeam A B hh hΔ).index) δ)
      (sourceHinge A B hh (selectedNegativeSeam A B hh hΔ).index) < 0 := by
  let N := PhysicalMixedTurnSource.MechanismN A B
  let S := FixedBaselinePolarRayGeometry.baselineStrip A B hh
  let O := PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)
  let Q := PhysicalMixedTurnSource.planeRotation
    (PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh))
  let H := PhysicalMixedTurnSource.fullCircuit A B hh 0
  let t := 1 - δ
  let x0 := S.point 0 0 t
  let x1 := S.point 0 1 t
  let y := S.point N 1 t
  let ρN := (1 - t) * S.lowerCoeff N + t * S.upperCoeff N
  let ρ0 := (1 - t) * S.lowerCoeff 0 + t * S.upperCoeff 0
  let a := y - O
  let f := ρN • S.v N
  let e := ρ0 • Q (S.v 0)
  let G := Q (S.d 0)
  have hN : 1 ≤ N := by
    have hs := three_le_sideCount A B
    change 1 ≤ sideCount A B - 1
    omega
  have hρN : 0 < ρN := by
    dsimp [ρN, t, S]
    simpa [PhysicalMixedTurnSource.retainedUpperRunCoeff,
      FixedBaselinePolarRayGeometry.baselineStrip] using
      (PhysicalMixedTurnSource.retainedUpperRunCoeff_pos A B hh hδ0 hδ1
        (PhysicalMixedTurnSource.familySource A B 0 N))
  have hρ0 : 0 < ρ0 := by
    dsimp [ρ0, t, S]
    simpa [PhysicalMixedTurnSource.retainedUpperRunCoeff,
      FixedBaselinePolarRayGeometry.baselineStrip] using
      (PhysicalMixedTurnSource.retainedUpperRunCoeff_pos A B hh hδ0 hδ1
        (PhysicalMixedTurnSource.familySource A B 0 0))
  have hy : y = H x0 := by
    exact FixedBaselinePolarRayGeometry.terminalPanelPoint_eq_fullCircuit_rootPoint
      A B hh t
  have hQ (x : Plane) : H x - O = Q (x - O) := by
    exact FixedBaselinePolarRayGeometry.fullCircuit_sub_pole A B hh
      (ne_of_lt hΔ) x
  have hQdiff (x z : Plane) : H x - H z = Q (x - z) := by
    have hx := hQ x
    have hz := hQ z
    calc
      H x - H z = (H x - O) - (H z - O) := by abel
      _ = Q (x - O) - Q (z - O) := by rw [hx, hz]
      _ = Q ((x - O) - (z - O)) := (map_sub Q (x - O) (z - O)).symm
      _ = Q (x - z) := by congr 1; abel
  have hx10 : x1 - x0 = ρ0 • S.v 0 := by
    dsimp [x1, x0, ρ0]
    simp only [RadialExtremalSafety.TriangularRadialStrip.point]
    module
  have hae : a + e = H x1 - O := by
    dsimp [a, e]
    rw [hy]
    have hd := hQdiff x1 x0
    rw [hx10, map_smul] at hd
    rw [← hd]
    abel
  have haf : a - f = S.point N 0 t - O := by
    dsimp [a, f, y, ρN]
    simp only [RadialExtremalSafety.TriangularRadialStrip.point]
    module
  have hmax := (selectedNegativeSeam_spec A B hh hΔ).2
  let iN : SeamIndex A B := ⟨N, by omega⟩
  let i1 : SeamIndex A B := ⟨1, by omega⟩
  have hprev0 := hmax iN δ hδ0 hδmax
  have hnext0 := hmax i1 δ hδ0 hδmax
  have hsel : (selectedNegativeSeam A B hh hΔ).index = (0 : SeamIndex A B) := by
    apply Fin.ext
    exact hk0
  have hprev : ‖a - f‖ ^ 2 ≤ ‖a‖ ^ 2 := by
    rw [haf]
    rw [retainedUpperVector_eq_baselinePoint A B hh hΔ iN δ,
      hsel, retainedUpperVector_eq_baselinePoint A B hh hΔ
        (0 : SeamIndex A B) δ] at hprev0
    dsimp [iN, S, O, N] at hprev0
    have hnorm : ‖a‖ = ‖x0 - O‖ := by
      dsimp [a]
      rw [hy, hQ, (PhysicalMixedTurnSource.planeRotation _).norm_map]
    rw [hnorm]
    exact hprev0
  have hnext : ‖a + e‖ ^ 2 ≤ ‖a‖ ^ 2 := by
    rw [hae]
    have hglue := FixedBaselinePolarTrace.point_exit_eq_next_entry S
      (show 0 < N by omega) t
    rw [retainedUpperVector_eq_baselinePoint A B hh hΔ i1 δ,
      hsel, retainedUpperVector_eq_baselinePoint A B hh hΔ
        (0 : SeamIndex A B) δ] at hnext0
    dsimp [i1, S, O, t] at hnext0
    rw [← hglue] at hnext0
    have hn1 : ‖H x1 - O‖ = ‖x1 - O‖ := by
      rw [hQ, (PhysicalMixedTurnSource.planeRotation _).norm_map]
    have hn0 : ‖a‖ = ‖x0 - O‖ := by
      dsimp [a]
      rw [hy, hQ, (PhysicalMixedTurnSource.planeRotation _).norm_map]
    rw [hn1, hn0]
    exact hnext0
  have ha0 : a ≠ 0 := by
    dsimp [a, y]
    exact sub_ne_zero.mpr
      (RadialExtremalSafety.TriangularRadialStrip.point_ne_pole
        (FixedBaselinePolarRayGeometry.baselineStrip_radialSupport A B hh hΔ)
        (i := N) (by omega) (s := (1 : ℝ)) (t := t) (by norm_num)
        (by dsimp [t]; constructor <;> linarith))
  have hafdet : MixedTurnSafeCut.det a f < 0 := by
    have hs := RadialExtremalSafety.TriangularRadialStrip.support_point
      (FixedBaselinePolarRayGeometry.baselineStrip_radialSupport A B hh hΔ)
      (i := N) (by omega) (s := (1 : ℝ)) (t := t) (by norm_num)
      (by dsimp [t]; constructor <;> linarith)
    dsimp [a, f, y]
    rw [RadialExtremalSafety.det_smul_right]
    exact mul_neg_of_pos_of_neg hρN hs
  have haedet : MixedTurnSafeCut.det a e < 0 := by
    have hs := RadialExtremalSafety.TriangularRadialStrip.support_point
      (FixedBaselinePolarRayGeometry.baselineStrip_radialSupport A B hh hΔ)
      (i := 0) (by omega) (s := (0 : ℝ)) (t := t) (by norm_num)
      (by dsimp [t]; constructor <;> linarith)
    dsimp [a, e]
    rw [hy, hQ]
    rw [RadialExtremalSafety.det_smul_right,
      PhysicalMixedTurnSource.planeRotation_det]
    exact mul_neg_of_pos_of_neg hρ0 hs
  have hterminalD : S.d (N + 1) = Q (S.d 0) := by
    have hu := PhysicalMixedTurnSource.baseline_developedUpper_fullCircuit A B hh 0
    have hl := PhysicalMixedTurnSource.baseline_developedLower_fullCircuit A B hh 0
    have hqu := FixedBaselinePolarRayGeometry.fullCircuit_sub_pole A B hh
      (ne_of_lt hΔ) (PhysicalMixedTurnSource.developedUpper A B hh 0 0)
    have hql := FixedBaselinePolarRayGeometry.fullCircuit_sub_pole A B hh
      (ne_of_lt hΔ) (PhysicalMixedTurnSource.developedLower A B hh 0 0)
    change PhysicalMixedTurnSource.developedUpper A B hh 0
          (PhysicalMixedTurnSource.MechanismN A B + 1) -
        PhysicalMixedTurnSource.developedLower A B hh 0
          (PhysicalMixedTurnSource.MechanismN A B + 1) =
      Q (PhysicalMixedTurnSource.developedUpper A B hh 0 0 -
        PhysicalMixedTurnSource.developedLower A B hh 0 0)
    calc
      _ = H (PhysicalMixedTurnSource.developedUpper A B hh 0 0) -
          H (PhysicalMixedTurnSource.developedLower A B hh 0 0) := by
        simpa only [Nat.add_zero] using congrArg₂ (· - ·) hu hl
      _ = (H (PhysicalMixedTurnSource.developedUpper A B hh 0 0) - O) -
          (H (PhysicalMixedTurnSource.developedLower A B hh 0 0) - O) := by abel
      _ = Q (PhysicalMixedTurnSource.developedUpper A B hh 0 0 - O) -
          Q (PhysicalMixedTurnSource.developedLower A B hh 0 0 - O) := by
        rw [hqu, hql]
      _ = _ := by rw [← map_sub]; congr 1; abel
  have hstepD : S.d (N + 1) = S.d N +
      (S.upperCoeff N - S.lowerCoeff N) • S.v N := by
    have hu := PhysicalMixedTurnSource.developedUpper_succ_sub A B hh 0
      (PhysicalMixedTurnSource.MechanismN A B)
    have hl := PhysicalMixedTurnSource.developedLower_succ_sub A B hh 0
      (PhysicalMixedTurnSource.MechanismN A B)
    have hu' := sub_eq_iff_eq_add.mp hu
    have hl' := sub_eq_iff_eq_add.mp hl
    change PhysicalMixedTurnSource.developedUpper A B hh 0
          (PhysicalMixedTurnSource.MechanismN A B + 1) -
        PhysicalMixedTurnSource.developedLower A B hh 0
          (PhysicalMixedTurnSource.MechanismN A B + 1) =
      (PhysicalMixedTurnSource.developedUpper A B hh 0
          (PhysicalMixedTurnSource.MechanismN A B) -
        PhysicalMixedTurnSource.developedLower A B hh 0
          (PhysicalMixedTurnSource.MechanismN A B)) +
      (PhysicalMixedTurnSource.upperRunCoeff A B hh
          (PhysicalMixedTurnSource.familySource A B 0
            (PhysicalMixedTurnSource.MechanismN A B)) -
        PhysicalMixedTurnSource.lowerRunCoeff A B hh
          (PhysicalMixedTurnSource.familySource A B 0
            (PhysicalMixedTurnSource.MechanismN A B))) •
        PhysicalMixedTurnSource.developedForward A B hh 0
          (PhysicalMixedTurnSource.MechanismN A B)
    rw [hu', hl']
    module
  have hfg : MixedTurnSafeCut.det f G < 0 := by
    have horient := S.orientation_neg N (by omega)
    have heq : MixedTurnSafeCut.det (S.v N) G =
        MixedTurnSafeCut.det (S.v N) (S.d N) := by
      dsimp [G]
      rw [← hterminalD, hstepD]
      simp [MixedTurnSafeCut.det]
      ring
    dsimp [f]
    rw [RadialExtremalSafety.det_smul_left, heq]
    exact mul_neg_of_pos_of_neg hρN horient
  have heg : MixedTurnSafeCut.det e G < 0 := by
    have horient := S.orientation_neg 0 (by omega)
    dsimp [e, G]
    rw [RadialExtremalSafety.det_smul_left,
      PhysicalMixedTurnSource.planeRotation_det]
    exact mul_neg_of_pos_of_neg hρ0 horient
  have hdot := extremal_corner_hinge_dot_neg ha0 hprev hnext
    hafdet haedet hfg heg
  have hinner : inner ℝ a G = inner ℝ (x0 - O) (S.d 0) := by
    dsimp [a, G]
    rw [hy, hQ, (PhysicalMixedTurnSource.planeRotation _).inner_map_map]
  rw [hinner] at hdot
  rw [hsel, retainedUpperVector_eq_baselinePoint A B hh hΔ
    (0 : SeamIndex A B) δ]
  change inner ℝ (S.point 0 0 (1 - δ) - O) (S.d 0) < 0
  simpa only [t, x0] using hdot

/-- Positive-defect normalization transports the complete seam geometry: it
reflects the plane and swaps lower/upper rims, rather than merely changing a
sign in an inequality. -/
noncomputable def positiveNormalizedUpper
    (i : SeamIndex A B) : Plane :=
  RadialExtremalSafety.reflectPlane
    (PhysicalMixedTurnSource.developedLower A B hh 0 i.val)

noncomputable def positiveNormalizedHinge
    (i : SeamIndex A B) : Plane :=
  -RadialExtremalSafety.reflectPlane (sourceHinge A B hh i)

noncomputable def selectedPositiveSeam
    (hΔ : 0 < PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh)) :
    FixedRetainedUpperChoice (SeamIndex A B) :=
  fixedRetainedUpperChoice
    (RadialExtremalSafety.reflectPlane
      (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ)))
    (positiveNormalizedUpper A B hh) (positiveNormalizedHinge A B hh)

/-- Exact eventual-max certificate after the global positive-branch
reflection/rim transport. -/
theorem selectedPositiveSeam_spec
    (hΔ : 0 < PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh)) :
    0 < (selectedPositiveSeam A B hh hΔ).threshold ∧
      ∀ i δ, 0 < δ → δ < (selectedPositiveSeam A B hh hΔ).threshold →
        ‖retainedUpperVector
          (RadialExtremalSafety.reflectPlane
            (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ)))
          (positiveNormalizedUpper A B hh i)
          (positiveNormalizedHinge A B hh i) δ‖ ^ 2 ≤
        ‖retainedUpperVector
          (RadialExtremalSafety.reflectPlane
            (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ)))
          (positiveNormalizedUpper A B hh
            (selectedPositiveSeam A B hh hΔ).index)
          (positiveNormalizedHinge A B hh
            (selectedPositiveSeam A B hh hΔ).index) δ‖ ^ 2 :=
  fixedRetainedUpperChoice_spec _ _ _

/-- The normalized seam is the reflected original seam with reversed height. -/
lemma positiveNormalizedPoint (i : SeamIndex A B) (s t : ℝ) :
    (RadialExtremalSafety.TriangularRadialStrip.reflectSwap
      (FixedBaselinePolarRayGeometry.baselineStrip A B hh)).point i.val s t =
    RadialExtremalSafety.reflectPlane
      ((FixedBaselinePolarRayGeometry.baselineStrip A B hh).point i.val s (1 - t)) :=
  RadialExtremalSafety.TriangularRadialStrip.reflectSwap_point _ _ _ _

lemma positiveRetained_eq_normalizedPoint
    (hΔ : 0 < PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh))
    (i : SeamIndex A B) (δ : ℝ) :
    retainedUpperVector
      (RadialExtremalSafety.reflectPlane
        (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ)))
      (positiveNormalizedUpper A B hh i) (positiveNormalizedHinge A B hh i) δ =
    (RadialExtremalSafety.TriangularRadialStrip.reflectSwap
      (FixedBaselinePolarRayGeometry.baselineStrip A B hh)).point i.val 0 (1 - δ) -
      RadialExtremalSafety.reflectPlane
        (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ)) := by
  simp only [retainedUpperVector, upperVector, positiveNormalizedUpper,
    positiveNormalizedHinge, sourceHinge, RadialExtremalSafety.TriangularRadialStrip.point,
    RadialExtremalSafety.TriangularRadialStrip.reflectSwap,
    FixedBaselinePolarRayGeometry.baselineStrip]
  ext j
  fin_cases j <;> simp [RadialExtremalSafety.reflectPlane] <;> ring

/-- Every physical original seam has nonzero hinge vector, including facets
whose lower or upper horizontal run coefficient is zero. -/
theorem sourceHinge_ne_zero (i : SeamIndex A B) :
    sourceHinge A B hh i ≠ 0 := by
  intro hzero
  have ho := PhysicalMixedTurnSource.developed_hinge_orientation_neg
    A B hh 0 i.val
  rw [show PhysicalMixedTurnSource.developedUpper A B hh 0 i.val -
      PhysicalMixedTurnSource.developedLower A B hh 0 i.val =
        sourceHinge A B hh i by rfl, hzero] at ho
  simp [MixedTurnSafeCut.det] at ho

/-- At a non-root maximizer the two actual adjacent source seams give the
strict normalized hinge derivative, even if either rim run vanishes. -/
theorem selectedPositiveSeam_retained_dot_neg_of_index_pos
    (hΔ : 0 < PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hδmax : δ < (selectedPositiveSeam A B hh hΔ).threshold)
    (hk0 : 0 < (selectedPositiveSeam A B hh hΔ).index.val) :
    inner ℝ
      (retainedUpperVector
        (RadialExtremalSafety.reflectPlane
          (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ)))
        (positiveNormalizedUpper A B hh (selectedPositiveSeam A B hh hΔ).index)
        (positiveNormalizedHinge A B hh (selectedPositiveSeam A B hh hΔ).index) δ)
      (positiveNormalizedHinge A B hh (selectedPositiveSeam A B hh hΔ).index) < 0 := by
  let S := RadialExtremalSafety.TriangularRadialStrip.reflectSwap
    (FixedBaselinePolarRayGeometry.baselineStrip A B hh)
  let O := RadialExtremalSafety.reflectPlane
    (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ))
  let k := (selectedPositiveSeam A B hh hΔ).index
  have hkN : k.val ≤ PhysicalMixedTurnSource.MechanismN A B := Nat.le_of_lt_succ k.isLt
  have hcoeff : ∀ j ≤ PhysicalMixedTurnSource.MechanismN A B,
      0 < S.lowerCoeff j + S.upperCoeff j := by
    intro j hj
    simpa [S, RadialExtremalSafety.TriangularRadialStrip.reflectSwap,
      FixedBaselinePolarRayGeometry.baselineStrip, add_comm] using
      PhysicalMixedTurnSource.lowerRunCoeff_add_upperRunCoeff_pos
        A B hh (PhysicalMixedTurnSource.familySource A B 0 j)
  let kp : SeamIndex A B := ⟨k.val - 1, by omega⟩
  have hmax := (selectedPositiveSeam_spec A B hh hΔ).2
  have hprev0 := hmax kp δ hδ0 hδmax
  have hprev : ‖S.point (k.val - 1) 0 (1 - δ) - O‖ ^ 2 ≤
      ‖S.point k.val 0 (1 - δ) - O‖ ^ 2 := by
    rw [← positiveRetained_eq_normalizedPoint A B hh hΔ kp δ,
      ← positiveRetained_eq_normalizedPoint A B hh hΔ k δ]
    exact hprev0
  have hnext : ‖S.point k.val 1 (1 - δ) - O‖ ^ 2 ≤
      ‖S.point k.val 0 (1 - δ) - O‖ ^ 2 := by
    by_cases hklt : k.val < PhysicalMixedTurnSource.MechanismN A B
    · let kn : SeamIndex A B := ⟨k.val + 1, by omega⟩
      have hn0 := hmax kn δ hδ0 hδmax
      have hglue := FixedBaselinePolarTrace.point_exit_eq_next_entry S hklt (1 - δ)
      rw [hglue, ← positiveRetained_eq_normalizedPoint A B hh hΔ kn δ,
        ← positiveRetained_eq_normalizedPoint A B hh hΔ k δ]
      exact hn0
    · have hkEq : k.val = PhysicalMixedTurnSource.MechanismN A B := by omega
      have hroot0 := hmax (0 : SeamIndex A B) δ hδ0 hδmax
      have hcopy := FixedBaselinePolarRayGeometry.terminalPanelPoint_eq_fullCircuit_rootPoint
        A B hh δ
      have hnorm : ‖S.point (PhysicalMixedTurnSource.MechanismN A B) 1
            (1 - δ) - O‖ = ‖S.point 0 0 (1 - δ) - O‖ := by
        rw [show S.point (PhysicalMixedTurnSource.MechanismN A B) 1 (1 - δ) =
          RadialExtremalSafety.reflectPlane
            ((FixedBaselinePolarRayGeometry.baselineStrip A B hh).point
              (PhysicalMixedTurnSource.MechanismN A B) 1 δ) by
                simp only [S, RadialExtremalSafety.TriangularRadialStrip.reflectSwap_point];
                congr 1 <;> ring]
        rw [show S.point 0 0 (1 - δ) =
          RadialExtremalSafety.reflectPlane
            ((FixedBaselinePolarRayGeometry.baselineStrip A B hh).point 0 0 δ) by
                simp only [S, RadialExtremalSafety.TriangularRadialStrip.reflectSwap_point];
                congr 1 <;> ring]
        rw [hcopy, ← RadialExtremalSafety.reflectPlane_sub,
          RadialExtremalSafety.reflectPlane_norm,
          FixedBaselinePolarRayGeometry.fullCircuit_sub_pole A B hh (ne_of_gt hΔ),
          (PhysicalMixedTurnSource.planeRotation _).norm_map]
        rw [show O = RadialExtremalSafety.reflectPlane
          (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ)) by rfl,
          ← RadialExtremalSafety.reflectPlane_sub,
          RadialExtremalSafety.reflectPlane_norm]
      rw [positiveRetained_eq_normalizedPoint A B hh hΔ
        (0 : SeamIndex A B) δ,
        positiveRetained_eq_normalizedPoint A B hh hΔ k δ] at hroot0
      dsimp [S, O] at hroot0 ⊢
      rw [hkEq, hnorm]
      simpa only [hkEq] using hroot0
  have hdot := interior_entry_hinge_dot_neg S O
    (FixedBaselinePolarRayGeometry.reflectedBaselineStrip_radialSupport A B hh hΔ)
    hcoeff hk0 hkN (t := 1 - δ) (by constructor <;> linarith)
    hprev hnext
  rw [positiveRetained_eq_normalizedPoint A B hh hΔ k δ]
  change inner ℝ (S.point k.val 0 (1 - δ) - O) (S.d k.val) < 0
  exact hdot

/-- The root seam uses the terminal full-circuit copy for its incoming
neighbor and the rotated first panel for its outgoing neighbor. -/
theorem selectedPositiveSeam_retained_dot_neg_of_index_zero
    (hΔ : 0 < PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < (1 : ℝ) / 2)
    (hδmax : δ < (selectedPositiveSeam A B hh hΔ).threshold)
    (hk0 : (selectedPositiveSeam A B hh hΔ).index.val = 0) :
    inner ℝ
      (retainedUpperVector
        (RadialExtremalSafety.reflectPlane
          (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ)))
        (positiveNormalizedUpper A B hh (selectedPositiveSeam A B hh hΔ).index)
        (positiveNormalizedHinge A B hh (selectedPositiveSeam A B hh hΔ).index) δ)
      (positiveNormalizedHinge A B hh (selectedPositiveSeam A B hh hΔ).index) < 0 := by
  let N := PhysicalMixedTurnSource.MechanismN A B
  let T := FixedBaselinePolarRayGeometry.baselineStrip A B hh
  let S := RadialExtremalSafety.TriangularRadialStrip.reflectSwap T
  let P := PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ)
  let O := RadialExtremalSafety.reflectPlane P
  let Q := PhysicalMixedTurnSource.planeRotation
    (PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh))
  let H := PhysicalMixedTurnSource.fullCircuit A B hh 0
  let t := 1 - δ
  let x0 := S.point 0 0 t
  let x1 := S.point 0 1 t
  let y := S.point N 1 t
  let ρN := (1 - t) * S.lowerCoeff N + t * S.upperCoeff N
  let ρ0 := (1 - t) * S.lowerCoeff 0 + t * S.upperCoeff 0
  let a := y - O
  let f := ρN • S.v N
  let e := ρ0 • RadialExtremalSafety.reflectPlane (Q (T.v 0))
  let G := -RadialExtremalSafety.reflectPlane (Q (T.d 0))
  have hN : 1 ≤ N := by
    have hs := three_le_sideCount A B
    change 1 ≤ sideCount A B - 1
    omega
  have hcoeff (j : ℕ) (hj : j ≤ N) :
      0 < S.lowerCoeff j + S.upperCoeff j := by
    simpa [S, T, RadialExtremalSafety.TriangularRadialStrip.reflectSwap,
      FixedBaselinePolarRayGeometry.baselineStrip, add_comm] using
        PhysicalMixedTurnSource.lowerRunCoeff_add_upperRunCoeff_pos
          A B hh (PhysicalMixedTurnSource.familySource A B 0 j)
  have hρN : 0 < ρN := by
    have hl := S.lowerCoeff_nonneg N (by omega)
    have hu := S.upperCoeff_nonneg N (by omega)
    have hs := hcoeff N (by omega)
    dsimp [ρN, t]
    by_cases hz : S.upperCoeff N = 0
    · have hp : 0 < S.lowerCoeff N := by linarith
      exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hp)
        (mul_nonneg (by linarith) hu)
    · have hp : 0 < S.upperCoeff N := lt_of_le_of_ne hu (Ne.symm hz)
      exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) hl)
        (mul_pos (by linarith) hp)
  have hρ0 : 0 < ρ0 := by
    have hl := S.lowerCoeff_nonneg 0 (by omega)
    have hu := S.upperCoeff_nonneg 0 (by omega)
    have hs := hcoeff 0 (by omega)
    dsimp [ρ0, t]
    by_cases hz : S.upperCoeff 0 = 0
    · have hp : 0 < S.lowerCoeff 0 := by linarith
      exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hp)
        (mul_nonneg (by linarith) hu)
    · have hp : 0 < S.upperCoeff 0 := lt_of_le_of_ne hu (Ne.symm hz)
      exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) hl)
        (mul_pos (by linarith) hp)
  have hx0 : x0 = RadialExtremalSafety.reflectPlane (T.point 0 0 δ) := by
    dsimp [x0, S, t]
    rw [RadialExtremalSafety.TriangularRadialStrip.reflectSwap_point]
    congr 1 <;> ring
  have hx1 : x1 = RadialExtremalSafety.reflectPlane (T.point 0 1 δ) := by
    dsimp [x1, S, t]
    rw [RadialExtremalSafety.TriangularRadialStrip.reflectSwap_point]
    congr 1 <;> ring
  have hy : y = RadialExtremalSafety.reflectPlane (H (T.point 0 0 δ)) := by
    dsimp [y, S, t]
    rw [RadialExtremalSafety.TriangularRadialStrip.reflectSwap_point]
    convert congrArg RadialExtremalSafety.reflectPlane
      (FixedBaselinePolarRayGeometry.terminalPanelPoint_eq_fullCircuit_rootPoint
        A B hh δ) using 1 <;> congr 2 <;> ring
  have hQ (z : Plane) : H z - P = Q (z - P) :=
    FixedBaselinePolarRayGeometry.fullCircuit_sub_pole A B hh (ne_of_gt hΔ) z
  have hQdiff (z w : Plane) : H z - H w = Q (z - w) := by
    have hz := hQ z
    have hw := hQ w
    calc
      H z - H w = (H z - P) - (H w - P) := by abel
      _ = Q (z - P) - Q (w - P) := by rw [hz, hw]
      _ = Q (z - w) := by rw [← map_sub]; congr 1; abel
  have hcenter : a = RadialExtremalSafety.reflectPlane (Q (T.point 0 0 δ - P)) := by
    dsimp [a, O]
    rw [hy, ← RadialExtremalSafety.reflectPlane_sub, hQ]
  have hx10 : T.point 0 1 δ - T.point 0 0 δ =
      ((1 - δ) * T.lowerCoeff 0 + δ * T.upperCoeff 0) • T.v 0 := by
    simp only [RadialExtremalSafety.TriangularRadialStrip.point]
    module
  have hρ0' : ρ0 = (1 - δ) * T.lowerCoeff 0 + δ * T.upperCoeff 0 := by
    dsimp [ρ0, S, t, RadialExtremalSafety.TriangularRadialStrip.reflectSwap]
    ring
  have hae : a + e = RadialExtremalSafety.reflectPlane (H (T.point 0 1 δ)) - O := by
    dsimp [a, e]
    rw [hy, hρ0', ← RadialExtremalSafety.reflectPlane_smul,
      ← map_smul Q, ← hx10, ← hQdiff,
      ← RadialExtremalSafety.reflectPlane_sub]
    rw [show O = RadialExtremalSafety.reflectPlane P by rfl,
      ← RadialExtremalSafety.reflectPlane_sub,
      ← RadialExtremalSafety.reflectPlane_add]
    congr 1
    abel
  have haf : a - f = S.point N 0 t - O := by
    dsimp [a, f, y, ρN]
    simp only [RadialExtremalSafety.TriangularRadialStrip.point]
    module
  have hmax := (selectedPositiveSeam_spec A B hh hΔ).2
  let iN : SeamIndex A B := ⟨N, by omega⟩
  let i1 : SeamIndex A B := ⟨1, by omega⟩
  have hprev0 := hmax iN δ hδ0 hδmax
  have hnext0 := hmax i1 δ hδ0 hδmax
  have hsel : (selectedPositiveSeam A B hh hΔ).index = (0 : SeamIndex A B) :=
    Fin.ext hk0
  have hnorm (z : Plane) :
      ‖RadialExtremalSafety.reflectPlane (H z) - O‖ = ‖z - P‖ := by
    rw [show O = RadialExtremalSafety.reflectPlane P by rfl,
      ← RadialExtremalSafety.reflectPlane_sub,
      RadialExtremalSafety.reflectPlane_norm, hQ,
      (PhysicalMixedTurnSource.planeRotation _).norm_map]
  have hprev : ‖a - f‖ ^ 2 ≤ ‖a‖ ^ 2 := by
    rw [haf]
    rw [positiveRetained_eq_normalizedPoint A B hh hΔ iN δ,
      hsel, positiveRetained_eq_normalizedPoint A B hh hΔ
        (0 : SeamIndex A B) δ] at hprev0
    dsimp [iN, S, O, N] at hprev0
    rw [show ‖a‖ = ‖x0 - O‖ by
      dsimp [a]; rw [hy, hx0];
      rw [hnorm, ← RadialExtremalSafety.reflectPlane_sub,
        RadialExtremalSafety.reflectPlane_norm]]
    exact hprev0
  have hnext : ‖a + e‖ ^ 2 ≤ ‖a‖ ^ 2 := by
    rw [hae]
    have hglue := FixedBaselinePolarTrace.point_exit_eq_next_entry S
      (show 0 < N by omega) t
    rw [positiveRetained_eq_normalizedPoint A B hh hΔ i1 δ,
      hsel, positiveRetained_eq_normalizedPoint A B hh hΔ
        (0 : SeamIndex A B) δ] at hnext0
    dsimp [i1, S, O, t] at hnext0
    rw [← hglue] at hnext0
    have h1 : ‖RadialExtremalSafety.reflectPlane (H (T.point 0 1 δ)) - O‖ =
        ‖x1 - O‖ := by
      rw [hnorm, hx1, show O = RadialExtremalSafety.reflectPlane P by rfl,
        ← RadialExtremalSafety.reflectPlane_sub,
        RadialExtremalSafety.reflectPlane_norm]
    have h0 : ‖a‖ = ‖x0 - O‖ := by
      dsimp [a]; rw [hy, hnorm, hx0,
        show O = RadialExtremalSafety.reflectPlane P by rfl,
        ← RadialExtremalSafety.reflectPlane_sub,
        RadialExtremalSafety.reflectPlane_norm]
    rw [h1, h0]
    exact hnext0
  have ha0 : a ≠ 0 := sub_ne_zero.mpr
    (RadialExtremalSafety.TriangularRadialStrip.point_ne_pole
      (FixedBaselinePolarRayGeometry.reflectedBaselineStrip_radialSupport A B hh hΔ)
      (i := N) (by omega) (s := (1 : ℝ)) (t := t) (by norm_num)
      (by dsimp [t]; constructor <;> linarith))
  have hafdet : MixedTurnSafeCut.det a f < 0 := by
    have hs := RadialExtremalSafety.TriangularRadialStrip.support_point
      (FixedBaselinePolarRayGeometry.reflectedBaselineStrip_radialSupport A B hh hΔ)
      (i := N) (by omega) (s := (1 : ℝ)) (t := t) (by norm_num)
      (by dsimp [t]; constructor <;> linarith)
    dsimp [a, f, y]
    rw [RadialExtremalSafety.det_smul_right]
    exact mul_neg_of_pos_of_neg hρN hs
  have haedet : MixedTurnSafeCut.det a e < 0 := by
    have hs := (FixedBaselinePolarRayGeometry.baselineStrip_positiveRadialSupport
      A B hh hΔ) 0 (by omega)
    have hp := RadialExtremalSafety.TriangularRadialStrip.det_point T P 0 0 δ
    have hd : 0 < MixedTurnSafeCut.det (T.point 0 0 δ - P) (T.v 0) := by
      rw [hp]
      nlinarith [mul_pos hδ0 hs.2, mul_pos (by linarith : 0 < 1 - δ) hs.1]
    rw [show a = RadialExtremalSafety.reflectPlane
      (Q (T.point 0 0 δ - P)) from hcenter]
    dsimp [e]
    rw [RadialExtremalSafety.det_smul_right,
      RadialExtremalSafety.det_reflectPlane,
      PhysicalMixedTurnSource.planeRotation_det]
    exact mul_neg_of_pos_of_neg hρ0 (neg_neg_of_pos hd)
  have hterminalD : S.d (N + 1) = G := by
    have hu := PhysicalMixedTurnSource.baseline_developedUpper_fullCircuit A B hh 0
    have hl := PhysicalMixedTurnSource.baseline_developedLower_fullCircuit A B hh 0
    have hqu := hQ (PhysicalMixedTurnSource.developedUpper A B hh 0 0)
    have hql := hQ (PhysicalMixedTurnSource.developedLower A B hh 0 0)
    have ht : T.d (N + 1) = Q (T.d 0) := by
      change PhysicalMixedTurnSource.developedUpper A B hh 0 (N + 1) -
          PhysicalMixedTurnSource.developedLower A B hh 0 (N + 1) =
        Q (PhysicalMixedTurnSource.developedUpper A B hh 0 0 -
          PhysicalMixedTurnSource.developedLower A B hh 0 0)
      calc
        _ = H (PhysicalMixedTurnSource.developedUpper A B hh 0 0) -
            H (PhysicalMixedTurnSource.developedLower A B hh 0 0) := by
          simpa only [Nat.add_zero, N] using congrArg₂ (· - ·) hu hl
        _ = (H (PhysicalMixedTurnSource.developedUpper A B hh 0 0) - P) -
            (H (PhysicalMixedTurnSource.developedLower A B hh 0 0) - P) := by abel
        _ = Q (PhysicalMixedTurnSource.developedUpper A B hh 0 0 - P) -
            Q (PhysicalMixedTurnSource.developedLower A B hh 0 0 - P) := by rw [hqu, hql]
        _ = _ := by rw [← map_sub]; congr 1; abel
    change -RadialExtremalSafety.reflectPlane (T.d (N + 1)) =
      -RadialExtremalSafety.reflectPlane (Q (T.d 0))
    rw [ht]
  have hstepD : S.d (N + 1) = S.d N +
      (S.upperCoeff N - S.lowerCoeff N) • S.v N := by
    have hu := PhysicalMixedTurnSource.developedUpper_succ_sub A B hh 0 N
    have hl := PhysicalMixedTurnSource.developedLower_succ_sub A B hh 0 N
    have hu' := sub_eq_iff_eq_add.mp hu
    have hl' := sub_eq_iff_eq_add.mp hl
    have hb : T.d (N + 1) = T.d N +
        (T.upperCoeff N - T.lowerCoeff N) • T.v N := by
      change PhysicalMixedTurnSource.developedUpper A B hh 0 (N + 1) -
          PhysicalMixedTurnSource.developedLower A B hh 0 (N + 1) =
        (PhysicalMixedTurnSource.developedUpper A B hh 0 N -
          PhysicalMixedTurnSource.developedLower A B hh 0 N) +
        (PhysicalMixedTurnSource.upperRunCoeff A B hh
          (PhysicalMixedTurnSource.familySource A B 0 N) -
          PhysicalMixedTurnSource.lowerRunCoeff A B hh
            (PhysicalMixedTurnSource.familySource A B 0 N)) •
          PhysicalMixedTurnSource.developedForward A B hh 0 N
      rw [hu', hl']
      module
    change -RadialExtremalSafety.reflectPlane (T.d (N + 1)) =
      -RadialExtremalSafety.reflectPlane (T.d N) +
        (T.lowerCoeff N - T.upperCoeff N) •
          RadialExtremalSafety.reflectPlane (T.v N)
    rw [hb, RadialExtremalSafety.reflectPlane_add,
      RadialExtremalSafety.reflectPlane_smul]
    module
  have hfg : MixedTurnSafeCut.det f G < 0 := by
    have horient := S.orientation_neg N (by omega)
    have heq : MixedTurnSafeCut.det (S.v N) G =
        MixedTurnSafeCut.det (S.v N) (S.d N) := by
      rw [← hterminalD, hstepD]
      simp [MixedTurnSafeCut.det]
      ring
    dsimp [f]
    rw [RadialExtremalSafety.det_smul_left, heq]
    exact mul_neg_of_pos_of_neg hρN horient
  have heg : MixedTurnSafeCut.det e G < 0 := by
    have horient := T.orientation_neg 0 (by omega)
    dsimp [e, G]
    rw [RadialExtremalSafety.det_smul_left,
      RadialExtremalSafety.det_neg_right,
      RadialExtremalSafety.det_reflectPlane,
      PhysicalMixedTurnSource.planeRotation_det]
    simpa only [neg_neg] using mul_neg_of_pos_of_neg hρ0 horient
  have hdot := extremal_corner_hinge_dot_neg ha0 hprev hnext
    hafdet haedet hfg heg
  have hinner : inner ℝ a G = inner ℝ (x0 - O) (S.d 0) := by
    rw [hcenter]
    dsimp [G, S, T, RadialExtremalSafety.TriangularRadialStrip.reflectSwap]
    rw [inner_neg_right, inner_neg_right,
      RadialExtremalSafety.reflectPlane_inner,
      (PhysicalMixedTurnSource.planeRotation _).inner_map_map]
    rw [hx0, show O = RadialExtremalSafety.reflectPlane P by rfl,
      ← RadialExtremalSafety.reflectPlane_sub,
      RadialExtremalSafety.reflectPlane_inner]
  rw [hinner] at hdot
  rw [hsel, positiveRetained_eq_normalizedPoint A B hh hΔ
    (0 : SeamIndex A B) δ]
  change inner ℝ (S.point 0 0 (1 - δ) - O) (S.d 0) < 0
  simpa only [t, x0] using hdot

/-- Once the source-local cone argument supplies the weak endpoint dot bound,
the selected *original* seam is strictly radially inward. -/
theorem selectedNegativeSeam_radiallyInward_of_dot
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    (hdot : inner ℝ
      (sourceUpper A B hh (selectedNegativeSeam A B hh hΔ).index -
        PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
      (sourceHinge A B hh (selectedNegativeSeam A B hh hΔ).index) ≤ 0) :
    FixedBaselinePolarTrace.RadiallyInward
      (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
      (fun t => PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ) +
        RadialExtremalSafety.hingePoint
          (sourceUpper A B hh (selectedNegativeSeam A B hh hΔ).index -
            PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
          (sourceHinge A B hh (selectedNegativeSeam A B hh hΔ).index) t) :=
  radiallyInward_of_weak_endpoint
    (sourceHinge_ne_zero A B hh _) hdot

/-- The source selector itself supplies the weak endpoint dot bound; no caller
provides a seam certificate. -/
theorem selectedNegativeSeam_weak_endpoint_dot
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0) :
    inner ℝ
      (sourceUpper A B hh (selectedNegativeSeam A B hh hΔ).index -
        PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
      (sourceHinge A B hh (selectedNegativeSeam A B hh hΔ).index) ≤ 0 := by
  let ε := min (selectedNegativeSeam A B hh hΔ).threshold ((1 : ℝ) / 2)
  have hε : 0 < ε := lt_min (selectedNegativeSeam_spec A B hh hΔ).1 (by norm_num)
  apply weak_endpoint_of_eventual_strict hε
  intro δ hδ0 hδε
  have hδmax : δ < (selectedNegativeSeam A B hh hΔ).threshold :=
    hδε.trans_le (min_le_left _ _)
  have hδhalf : δ < (1 : ℝ) / 2 := hδε.trans_le (min_le_right _ _)
  have hlocal : inner ℝ
      (retainedUpperVector
        (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
        (sourceUpper A B hh (selectedNegativeSeam A B hh hΔ).index)
        (sourceHinge A B hh (selectedNegativeSeam A B hh hΔ).index) δ)
      (sourceHinge A B hh (selectedNegativeSeam A B hh hΔ).index) < 0 := by
    by_cases hk0 : (selectedNegativeSeam A B hh hΔ).index.val = 0
    · exact selectedNegativeSeam_retained_dot_neg_of_index_zero A B hh hΔ
        hδ0 hδhalf hδmax hk0
    · exact selectedNegativeSeam_retained_dot_neg_of_index_pos A B hh hΔ
        hδ0 (by linarith) hδmax (Nat.pos_of_ne_zero hk0)
  simpa only [retainedUpperVector, upperVector] using hlocal

/-- Premise-free inwardness of the selected negative-defect original seam. -/
theorem selectedNegativeSeam_radiallyInward
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0) :
    FixedBaselinePolarTrace.RadiallyInward
      (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
      (fun t => PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ) +
        RadialExtremalSafety.hingePoint
          (sourceUpper A B hh (selectedNegativeSeam A B hh hΔ).index -
            PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
          (sourceHinge A B hh (selectedNegativeSeam A B hh hΔ).index) t) :=
  selectedNegativeSeam_radiallyInward_of_dot A B hh hΔ
    (selectedNegativeSeam_weak_endpoint_dot A B hh hΔ)

/-- The source-selected positive seam has a weak derivative at its normalized
upper endpoint.  Ties are allowed: strictness comes from its nonzero hinge. -/
theorem selectedPositiveSeam_normalized_weak_endpoint_dot
    (hΔ : 0 < PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh)) :
    inner ℝ
      (positiveNormalizedUpper A B hh (selectedPositiveSeam A B hh hΔ).index -
        RadialExtremalSafety.reflectPlane
          (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ)))
      (positiveNormalizedHinge A B hh (selectedPositiveSeam A B hh hΔ).index) ≤ 0 := by
  let ε := min (selectedPositiveSeam A B hh hΔ).threshold ((1 : ℝ) / 2)
  have hε : 0 < ε := lt_min (selectedPositiveSeam_spec A B hh hΔ).1 (by norm_num)
  apply weak_endpoint_of_eventual_strict hε
  intro δ hδ0 hδε
  have hδmax : δ < (selectedPositiveSeam A B hh hΔ).threshold :=
    hδε.trans_le (min_le_left _ _)
  have hδhalf : δ < (1 : ℝ) / 2 := hδε.trans_le (min_le_right _ _)
  have hlocal : inner ℝ
      (retainedUpperVector
        (RadialExtremalSafety.reflectPlane
          (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ)))
        (positiveNormalizedUpper A B hh (selectedPositiveSeam A B hh hΔ).index)
        (positiveNormalizedHinge A B hh (selectedPositiveSeam A B hh hΔ).index) δ)
      (positiveNormalizedHinge A B hh (selectedPositiveSeam A B hh hΔ).index) < 0 := by
    by_cases hk0 : (selectedPositiveSeam A B hh hΔ).index.val = 0
    · exact selectedPositiveSeam_retained_dot_neg_of_index_zero A B hh hΔ
        hδ0 hδhalf hδmax hk0
    · exact selectedPositiveSeam_retained_dot_neg_of_index_pos A B hh hΔ
        hδ0 (by linarith) hδmax (Nat.pos_of_ne_zero hk0)
  simpa only [retainedUpperVector, upperVector] using hlocal

/-- Premise-free strict inwardness from the reflected/rim-swapped source seam. -/
theorem selectedPositiveSeam_normalized_radiallyInward
    (hΔ : 0 < PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh)) :
    FixedBaselinePolarTrace.RadiallyInward
      (RadialExtremalSafety.reflectPlane
        (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ)))
      (fun t => RadialExtremalSafety.reflectPlane
          (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ)) +
        RadialExtremalSafety.hingePoint
          (positiveNormalizedUpper A B hh (selectedPositiveSeam A B hh hΔ).index -
            RadialExtremalSafety.reflectPlane
              (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ)))
          (positiveNormalizedHinge A B hh (selectedPositiveSeam A B hh hΔ).index) t) := by
  apply radiallyInward_of_weak_endpoint
    (G := positiveNormalizedHinge A B hh (selectedPositiveSeam A B hh hΔ).index)
  · intro hz
    have h := sourceHinge_ne_zero A B hh (selectedPositiveSeam A B hh hΔ).index
    change -RadialExtremalSafety.reflectPlane
      (sourceHinge A B hh (selectedPositiveSeam A B hh hΔ).index) = 0 at hz
    have hr := congrArg RadialExtremalSafety.reflectPlane (neg_eq_zero.mp hz)
    apply h
    have hzero : RadialExtremalSafety.reflectPlane (0 : Plane) = 0 := by
      ext j
      fin_cases j <;> simp [RadialExtremalSafety.reflectPlane]
    simpa only [RadialExtremalSafety.reflectPlane_reflectPlane,
      hzero] using hr
  · exact selectedPositiveSeam_normalized_weak_endpoint_dot A B hh hΔ

/-- The actual normalized seam; `t' = 1 - t` on the physical source. -/
noncomputable def selectedPositiveNormalizedSeamCurve
    (hΔ : 0 < PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh)) (t : ℝ) : Plane :=
  positiveNormalizedUpper A B hh (selectedPositiveSeam A B hh hΔ).index -
    (1 - t) • positiveNormalizedHinge A B hh (selectedPositiveSeam A B hh hΔ).index

noncomputable def selectedPositiveNormalizedTerminalSeamCurve
    (hΔ : 0 < PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh)) (t : ℝ) : Plane :=
  RadialExtremalSafety.reflectPlane
    (PhysicalMixedTurnSource.fullCircuit A B hh 0
      (RadialExtremalSafety.reflectPlane
        (selectedPositiveNormalizedSeamCurve A B hh hΔ t)))

/-- Physical height reverses while panel index and longitudinal coordinate stay fixed. -/
theorem selectedPositiveNormalizedSeamCurve_eq_source
    (hΔ : 0 < PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh)) (t : ℝ) :
    selectedPositiveNormalizedSeamCurve A B hh hΔ t =
      RadialExtremalSafety.reflectPlane
        (PhysicalMixedTurnSource.developedLower A B hh 0
          (selectedPositiveSeam A B hh hΔ).index.val +
          (1 - t) • sourceHinge A B hh
            (selectedPositiveSeam A B hh hΔ).index) := by
  simp only [selectedPositiveNormalizedSeamCurve, positiveNormalizedUpper,
    positiveNormalizedHinge, smul_neg, sub_neg_eq_add,
    ← RadialExtremalSafety.reflectPlane_smul,
    ← RadialExtremalSafety.reflectPlane_add]

/-- The normalized terminal full circuit preserves radial distance at *every*
height, not only when the two heights agree. -/
theorem selectedPositiveNormalizedTerminalSeam_radius_eq
    (hΔ : 0 < PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh))
    (t : ℝ) :
    ‖selectedPositiveNormalizedTerminalSeamCurve A B hh hΔ t -
        RadialExtremalSafety.reflectPlane
          (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ))‖ =
      ‖selectedPositiveNormalizedSeamCurve A B hh hΔ t -
        RadialExtremalSafety.reflectPlane
          (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ))‖ := by
  unfold selectedPositiveNormalizedTerminalSeamCurve
  rw [← RadialExtremalSafety.reflectPlane_sub,
    RadialExtremalSafety.reflectPlane_norm,
    FixedBaselinePolarRayGeometry.fullCircuit_sub_pole A B hh (ne_of_gt hΔ),
    (PhysicalMixedTurnSource.planeRotation _).norm_map]
  conv_lhs =>
    rw [show PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ) =
      RadialExtremalSafety.reflectPlane
        (RadialExtremalSafety.reflectPlane
          (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ))) by
        rw [RadialExtremalSafety.reflectPlane_reflectPlane]]
  rw [← RadialExtremalSafety.reflectPlane_sub,
    RadialExtremalSafety.reflectPlane_norm]

/-- Arbitrary-height radial distance identity between the terminal copy and
the source seam.  In particular the bracket is strictly negative when
`0 ≤ s < t ≤ 1`, even at a weak endpoint dot or a selector tie. -/
theorem selectedPositiveNormalizedTerminalSeam_normSq_sub
    (hΔ : 0 < PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh))
    (s t : ℝ) :
    ‖selectedPositiveNormalizedTerminalSeamCurve A B hh hΔ t -
        RadialExtremalSafety.reflectPlane
          (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ))‖ ^ 2 -
      ‖selectedPositiveNormalizedSeamCurve A B hh hΔ s -
        RadialExtremalSafety.reflectPlane
          (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ))‖ ^ 2 =
    (t - s) * (2 * inner ℝ
      (positiveNormalizedUpper A B hh (selectedPositiveSeam A B hh hΔ).index -
        RadialExtremalSafety.reflectPlane
          (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ)))
      (positiveNormalizedHinge A B hh (selectedPositiveSeam A B hh hΔ).index) -
      (2 - s - t) *
        ‖positiveNormalizedHinge A B hh (selectedPositiveSeam A B hh hΔ).index‖ ^ 2) := by
  rw [selectedPositiveNormalizedTerminalSeam_radius_eq]
  have he := RadialExtremalSafety.hinge_normSq_sub
    (positiveNormalizedUpper A B hh (selectedPositiveSeam A B hh hΔ).index -
      RadialExtremalSafety.reflectPlane
        (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ)))
    (positiveNormalizedHinge A B hh (selectedPositiveSeam A B hh hΔ).index)
    (t₁ := s) (t₂ := t)
  convert he using 1 <;>
    simp only [selectedPositiveNormalizedSeamCurve,
      RadialExtremalSafety.hingePoint] <;> abel

/-- Direct strict radial order of the normalized selected source curve. -/
theorem selectedPositiveNormalizedSeamCurve_radiallyInward
    (hΔ : 0 < PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh)) :
    FixedBaselinePolarTrace.RadiallyInward
      (RadialExtremalSafety.reflectPlane
        (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ)))
      (selectedPositiveNormalizedSeamCurve A B hh hΔ) := by
  intro s hs t ht hst
  have hin := selectedPositiveSeam_normalized_radiallyInward A B hh hΔ hs ht hst
  have hcurve (u : ℝ) :
      RadialExtremalSafety.reflectPlane
          (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ)) +
        RadialExtremalSafety.hingePoint
          (positiveNormalizedUpper A B hh (selectedPositiveSeam A B hh hΔ).index -
            RadialExtremalSafety.reflectPlane
              (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ)))
          (positiveNormalizedHinge A B hh (selectedPositiveSeam A B hh hΔ).index) u =
        selectedPositiveNormalizedSeamCurve A B hh hΔ u := by
    simp only [RadialExtremalSafety.hingePoint,
      selectedPositiveNormalizedSeamCurve]
    abel
  simpa only [Function.comp_apply, hcurve] using hin

/-- Distinct normalized heights cannot collide across the cut's full-circuit
copy; the radius identity is used at the *other* height. -/
theorem selectedPositiveSeam_crossGap_allPairs_ne
    (hΔ : 0 < PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh))
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hst : s ≠ t) :
    selectedPositiveNormalizedSeamCurve A B hh hΔ s ≠
      selectedPositiveNormalizedTerminalSeamCurve A B hh hΔ t := by
  intro heq
  have hin := selectedPositiveSeam_normalized_radiallyInward A B hh hΔ
  have hcurve (u : ℝ) :
      RadialExtremalSafety.reflectPlane
          (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ)) +
        RadialExtremalSafety.hingePoint
          (positiveNormalizedUpper A B hh (selectedPositiveSeam A B hh hΔ).index -
            RadialExtremalSafety.reflectPlane
              (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ)))
          (positiveNormalizedHinge A B hh (selectedPositiveSeam A B hh hΔ).index) u =
        selectedPositiveNormalizedSeamCurve A B hh hΔ u := by
    simp only [RadialExtremalSafety.hingePoint,
      selectedPositiveNormalizedSeamCurve]
    abel
  obtain hlt | hgt := lt_or_gt_of_ne hst
  · have hr := hin hs ht hlt
    simp only [Function.comp_apply, FixedBaselinePolarTrace.polarRadius_eq_norm,
      hcurve] at hr
    rw [← selectedPositiveNormalizedTerminalSeam_radius_eq A B hh hΔ t,
      heq] at hr
    exact (lt_irrefl _ hr)
  · have hr := hin ht hs hgt
    simp only [Function.comp_apply, FixedBaselinePolarTrace.polarRadius_eq_norm,
      hcurve] at hr
    rw [← selectedPositiveNormalizedTerminalSeam_radius_eq A B hh hΔ t] at hr
    rw [← heq] at hr
    exact (lt_irrefl _ hr)

/-- The actual selected source seam, parameterized from upper to lower. -/
noncomputable def selectedNegativeSeamCurve
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0) (t : ℝ) : Plane :=
  sourceUpper A B hh (selectedNegativeSeam A B hh hΔ).index -
    (1 - t) • sourceHinge A B hh (selectedNegativeSeam A B hh hΔ).index

/-- The literal full-circuit developed copy facing the selected cut seam. -/
noncomputable def selectedNegativeTerminalSeamCurve
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0) (t : ℝ) : Plane :=
  PhysicalMixedTurnSource.fullCircuit A B hh 0
    (selectedNegativeSeamCurve A B hh hΔ t)

theorem selectedNegativeSeamCurve_radiallyInward
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0) :
    FixedBaselinePolarTrace.RadiallyInward
      (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
      (selectedNegativeSeamCurve A B hh hΔ) := by
  intro s hs t ht hst
  have hin := selectedNegativeSeam_radiallyInward A B hh hΔ hs ht hst
  have hcurve (u : ℝ) :
      PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ) +
          RadialExtremalSafety.hingePoint
            (sourceUpper A B hh (selectedNegativeSeam A B hh hΔ).index -
              PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
            (sourceHinge A B hh (selectedNegativeSeam A B hh hΔ).index) u =
        selectedNegativeSeamCurve A B hh hΔ u := by
    simp only [RadialExtremalSafety.hingePoint, selectedNegativeSeamCurve]
    abel
  simpa only [Function.comp_apply, hcurve] using hin

/-- Concrete strict radius order for arbitrary developed interior points on
the selected source seam. -/
theorem selectedNegativeSeam_radius_strict
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0) :
    StrictAntiOn
      (FixedBaselinePolarTrace.polarRadius
        (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)) ∘
          selectedNegativeSeamCurve A B hh hΔ)
      (Icc (0 : ℝ) 1) :=
  selectedNegativeSeamCurve_radiallyInward A B hh hΔ

/-- Full-circuit conjugacy preserves selected-seam radius exactly. -/
theorem selectedNegativeTerminalSeam_radius_eq
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    (t : ℝ) :
    ‖selectedNegativeTerminalSeamCurve A B hh hΔ t -
        PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)‖ =
      ‖selectedNegativeSeamCurve A B hh hΔ t -
        PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)‖ := by
  unfold selectedNegativeTerminalSeamCurve
  rw [FixedBaselinePolarRayGeometry.fullCircuit_sub_pole A B hh (ne_of_lt hΔ),
    (PhysicalMixedTurnSource.planeRotation _).norm_map]

/-- Arbitrary-height cross-gap nonintersection for the two physical copies of
the selected cut seam. -/
theorem selectedNegativeSeam_crossGap_allPairs_ne
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hst : s ≠ t) :
    selectedNegativeSeamCurve A B hh hΔ s ≠
      selectedNegativeTerminalSeamCurve A B hh hΔ t := by
  intro heq
  have hin := selectedNegativeSeamCurve_radiallyInward A B hh hΔ
  obtain hlt | hgt := lt_or_gt_of_ne hst
  · have hr := hin hs ht hlt
    simp only [Function.comp_apply, FixedBaselinePolarTrace.polarRadius_eq_norm] at hr
    rw [← selectedNegativeTerminalSeam_radius_eq A B hh hΔ t, heq] at hr
    exact (lt_irrefl _ hr)
  · have hr := hin ht hs hgt
    simp only [Function.comp_apply, FixedBaselinePolarTrace.polarRadius_eq_norm] at hr
    rw [← selectedNegativeTerminalSeam_radius_eq A B hh hΔ t] at hr
    rw [← heq] at hr
    exact (lt_irrefl _ hr)

end Source

end
end RadialOriginalSeam

#print axioms RadialOriginalSeam.exists_fixed_eventual_retainedUpper_max
#print axioms RadialOriginalSeam.fixedRetainedUpperChoice_spec
#print axioms RadialOriginalSeam.radiallyInward_of_weak_endpoint
#print axioms RadialOriginalSeam.extremal_corner_hinge_dot_neg
#print axioms RadialOriginalSeam.weak_endpoint_of_eventual_strict
#print axioms RadialOriginalSeam.selectedNegativeSeam_spec
#print axioms RadialOriginalSeam.selectedPositiveSeam_spec
#print axioms RadialOriginalSeam.sourceHinge_ne_zero
#print axioms RadialOriginalSeam.selectedNegativeSeam_radiallyInward_of_dot
#print axioms RadialOriginalSeam.selectedNegativeSeam_weak_endpoint_dot
#print axioms RadialOriginalSeam.selectedNegativeSeam_radiallyInward
#print axioms RadialOriginalSeam.selectedNegativeSeam_radius_strict
#print axioms RadialOriginalSeam.selectedNegativeSeam_crossGap_allPairs_ne
#print axioms RadialOriginalSeam.selectedPositiveSeam_normalized_weak_endpoint_dot
#print axioms RadialOriginalSeam.selectedPositiveSeam_normalized_radiallyInward
#print axioms RadialOriginalSeam.selectedPositiveNormalizedSeamCurve_radiallyInward
#print axioms RadialOriginalSeam.selectedPositiveNormalizedTerminalSeam_normSq_sub
#print axioms RadialOriginalSeam.selectedPositiveSeam_crossGap_allPairs_ne
