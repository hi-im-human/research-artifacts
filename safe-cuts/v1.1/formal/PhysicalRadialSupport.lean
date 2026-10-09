import PhysicalMixedTurnDevelopment
import FoldedTurnProjection

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
set_option maxHeartbeats 4000000

section Raw
variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

/-- The real total intrinsic turn lies strictly inside one full revolution. -/
theorem abs_intrinsicDelta_lt_two_pi :
    |intrinsicDelta A B (hh := hh)| < 2 * Real.pi := by
  calc
    |intrinsicDelta A B (hh := hh)| =
        |∑ i, intrinsicQ A B (hh := hh) i| := rfl
    _ ≤ ∑ i, |intrinsicQ A B (hh := hh) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ < 2 * Real.pi := intrinsic_sum_abs_lt_two_pi A B hh

@[simp] lemma planeRotation_zero_angle (x : Plane) :
    planeRotation 0 x = x := by
  ext i
  fin_cases i <;> simp [planeRotation, planeRotationLinear]

/-- Exact half-angle factorization of `Rot Δ - I`, with the project's
counterclockwise rotation and determinant conventions. -/
lemma planeRotation_sub_identity (Δ : ℝ) (x : Plane) :
    planeRotation Δ x - x =
      (2 * Real.sin (Δ / 2)) •
        planeRotation (Δ / 2) (planeRotation (Real.pi / 2) x) := by
  have htwo : 2 * (Δ / 2) = Δ := by ring
  have hhalf : 2 * (Δ / 2) / 2 = Δ / 2 := by ring
  have hs : Real.sin Δ = 2 * Real.sin (Δ / 2) * Real.cos (Δ / 2) := by
    rw [← htwo, Real.sin_two_mul, hhalf]
  have hc : Real.cos Δ = 2 * Real.cos (Δ / 2) ^ 2 - 1 := by
    rw [← htwo, Real.cos_two_mul, hhalf]
  have hsc := Real.sin_sq_add_cos_sq (Δ / 2)
  ext i
  fin_cases i
  · simp [planeRotation, planeRotationLinear, hs, hc]
    linear_combination 2 * x 0 * hsc
  · simp [planeRotation, planeRotationLinear, hs, hc]
    linear_combination 2 * x 1 * hsc

lemma plane_decompose_unit (u v : Plane) (hu : ‖u‖ = 1) :
    v = (inner ℝ u v) • u + MixedTurnSafeCut.det u v •
      planeRotation (Real.pi / 2) u := by
  have hu2 : u 0 ^ 2 + u 1 ^ 2 = 1 := by
    have hs := real_inner_self_eq_norm_sq u
    simp [inner, Fin.sum_univ_two, hu] at hs
    nlinarith
  ext i
  fin_cases i
  · simp [inner, Fin.sum_univ_two, MixedTurnSafeCut.det,
      planeRotation, planeRotationLinear]
    linear_combination -v 0 * hu2
  · simp [inner, Fin.sum_univ_two, MixedTurnSafeCut.det,
      planeRotation, planeRotationLinear]
    linear_combination -v 1 * hu2

lemma det_sq_of_unit (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    MixedTurnSafeCut.det u v ^ 2 + inner ℝ u v ^ 2 = 1 := by
  have hu2 : u 0 ^ 2 + u 1 ^ 2 = 1 := by
    have hs := real_inner_self_eq_norm_sq u
    simp [inner, Fin.sum_univ_two, hu] at hs
    nlinarith
  have hv2 : v 0 ^ 2 + v 1 ^ 2 = 1 := by
    have hs := real_inner_self_eq_norm_sq v
    simp [inner, Fin.sum_univ_two, hv] at hs
    nlinarith
  simp [inner, Fin.sum_univ_two, MixedTurnSafeCut.det]
  nlinarith

/-- Signed planar angle reconstruction: the clockwise determinant selects
rotation by the negative (unsigned) Euclidean angle. -/
lemma clockwise_rotation_eq (u v : Plane)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hdet : MixedTurnSafeCut.det u v < 0) :
    v = planeRotation (-InnerProductGeometry.angle u v) u := by
  let τ := InnerProductGeometry.angle u v
  have hcos : inner ℝ u v = Real.cos τ := by
    have hc := InnerProductGeometry.cos_angle_mul_norm_mul_norm u v
    dsimp [τ]
    rw [hu, hv] at hc
    norm_num at hc
    exact hc.symm
  have hτ0 := InnerProductGeometry.angle_nonneg u v
  have hτpi := InnerProductGeometry.angle_le_pi u v
  have hτne0 : τ ≠ 0 := by
    intro hz
    obtain ⟨_, r, hr, huv⟩ := InnerProductGeometry.angle_eq_zero_iff.mp hz
    rw [huv] at hdet
    have hzdet : MixedTurnSafeCut.det u (r • u) = 0 := by
      simp [MixedTurnSafeCut.det]
      ring
    rw [hzdet] at hdet
    linarith
  have hτnepi : τ ≠ Real.pi := by
    intro hz
    obtain ⟨_, r, hr, huv⟩ := InnerProductGeometry.angle_eq_pi_iff.mp hz
    rw [huv] at hdet
    have hzdet : MixedTurnSafeCut.det u (r • u) = 0 := by
      simp [MixedTurnSafeCut.det]
      ring
    rw [hzdet] at hdet
    linarith
  have hτ : τ ∈ Set.Ioo (0 : ℝ) Real.pi :=
    ⟨lt_of_le_of_ne hτ0 (Ne.symm hτne0), lt_of_le_of_ne hτpi hτnepi⟩
  have hsin : 0 < Real.sin τ := Real.sin_pos_of_pos_of_lt_pi hτ.1 hτ.2
  have hsq := det_sq_of_unit u v hu hv
  have htrig := Real.sin_sq_add_cos_sq τ
  have hdetval : MixedTurnSafeCut.det u v = -Real.sin τ := by
    rw [hcos] at hsq
    nlinarith
  have hdec := plane_decompose_unit u v hu
  rw [hcos, hdetval] at hdec
  calc
    v = Real.cos τ • u + (-Real.sin τ) •
        planeRotation (Real.pi / 2) u := hdec
    _ = planeRotation (-τ) u := by
      ext i
      fin_cases i <;>
        simp [planeRotation, planeRotationLinear, Real.cos_neg, Real.sin_neg] <;>
        ring

lemma inner_rotation_self_of_unit (u : Plane) (hu : ‖u‖ = 1) (θ : ℝ) :
    inner ℝ u (planeRotation θ u) = Real.cos θ := by
  have hu2 : u 0 ^ 2 + u 1 ^ 2 = 1 := by
    have hs := real_inner_self_eq_norm_sq u
    simp [inner, Fin.sum_univ_two, hu] at hs
    nlinarith
  simp [inner, Fin.sum_univ_two, planeRotation, planeRotationLinear]
  linear_combination Real.cos θ * hu2

lemma inner_quarter_rotation_neg_of_unit (u : Plane) (hu : ‖u‖ = 1) (θ : ℝ) :
    inner ℝ (planeRotation (Real.pi / 2) u) (planeRotation (-θ) u) =
      -Real.sin θ := by
  have hu2 : u 0 ^ 2 + u 1 ^ 2 = 1 := by
    have hs := real_inner_self_eq_norm_sq u
    simp [inner, Fin.sum_univ_two, hu] at hs
    nlinarith
  simp [inner, Fin.sum_univ_two, planeRotation, planeRotationLinear,
    Real.cos_neg, Real.sin_neg]
  linear_combination -Real.sin θ * hu2

lemma det_edgeVector_prev_neg {n : ℕ} [NeZero n]
    (P : ReducedConvexPolygon n) (i : Fin n) :
    MixedTurnSafeCut.det (edgeVector P.vertex (prev i))
      (edgeVector P.vertex i) < 0 := by
  have hc := PolygonSupportCompleteness.ReducedConvexPolygon.corner_det_pos P i
  have hc' : 0 < MixedTurnSafeCut.det (back P i) (ahead P i) := by
    simpa [PolygonSupportCompleteness.det, MixedTurnSafeCut.det] using hc
  have hrel : MixedTurnSafeCut.det (edgeVector P.vertex (prev i))
      (edgeVector P.vertex i) =
      -MixedTurnSafeCut.det (back P i) (ahead P i) := by
    simp [edgeVector, back, ahead, next_prev, MixedTurnSafeCut.det]
    ring
  rw [hrel]
  linarith

def middlePlanarDirection (i : SourceIndex A B) : Plane :=
  NormedSpace.normalize (edgeVector (middlePolygon A B).vertex i)

lemma middlePlanarDirection_norm (i : SourceIndex A B) :
    ‖middlePlanarDirection A B i‖ = 1 := by
  rw [middlePlanarDirection, NormedSpace.norm_normalize_eq_one_iff]
  exact outgoing_ne_zero (middlePolygon A B) i

lemma angle_middlePlanarDirection (i : SourceIndex A B) :
    InnerProductGeometry.angle (middlePlanarDirection A B (prev i))
      (middlePlanarDirection A B i) = middleExteriorTurn A B i := by
  let u := edgeVector (middlePolygon A B).vertex (prev i)
  let v := edgeVector (middlePolygon A B).vertex i
  have hu : 0 < ‖u‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr
    (incoming_ne_zero (middlePolygon A B) i))
  have hv : 0 < ‖v‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr
    (outgoing_ne_zero (middlePolygon A B) i))
  change InnerProductGeometry.angle (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) =
    middleExteriorTurn A B i
  rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hu,
    InnerProductGeometry.angle_smul_right_of_pos _ _ hv]
  rfl

lemma middlePlanarDirection_det_neg (i : SourceIndex A B) :
    MixedTurnSafeCut.det (middlePlanarDirection A B (prev i))
      (middlePlanarDirection A B i) < 0 := by
  let u := edgeVector (middlePolygon A B).vertex (prev i)
  let v := edgeVector (middlePolygon A B).vertex i
  have hu : 0 < ‖u‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr
    (incoming_ne_zero (middlePolygon A B) i))
  have hv : 0 < ‖v‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr
    (outgoing_ne_zero (middlePolygon A B) i))
  have hedge : MixedTurnSafeCut.det u v < 0 :=
    det_edgeVector_prev_neg (middlePolygon A B) i
  change MixedTurnSafeCut.det (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) < 0
  have heq : MixedTurnSafeCut.det (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) =
      (‖u‖⁻¹ * ‖v‖⁻¹) * MixedTurnSafeCut.det u v := by
    simp [MixedTurnSafeCut.det]
    ring
  rw [heq]
  exact mul_neg_of_pos_of_neg (mul_pos hu hv) hedge

lemma middlePlanarDirection_next_rotation (i : SourceIndex A B) :
    middlePlanarDirection A B i =
      planeRotation (-middleExteriorTurn A B i)
        (middlePlanarDirection A B (prev i)) := by
  rw [← angle_middlePlanarDirection A B i]
  exact clockwise_rotation_eq
    (middlePlanarDirection A B (prev i)) (middlePlanarDirection A B i)
    (middlePlanarDirection_norm A B (prev i))
    (middlePlanarDirection_norm A B i)
    (middlePlanarDirection_det_neg A B i)

lemma horizontalIsometry_middlePlanarDirection (i : SourceIndex A B) :
    horizontalIsometry (middlePlanarDirection A B i) =
      middleDirection A B hh i := by
  rw [middleDirection, middleLength, middleStep_eq_horizontal]
  change horizontalIsometry
      (‖edgeVector (middlePolygon A B).vertex i‖⁻¹ •
        edgeVector (middlePolygon A B).vertex i) = _
  rw [map_smul, LinearIsometry.norm_map]

lemma upperPlanarRun_decompose (i : SourceIndex A B) :
    upperPlanarRun A B i =
      upperRunCoeff A B hh i • middlePlanarDirection A B i := by
  apply horizontalIsometry.injective
  rw [map_smul, horizontalIsometry_middlePlanarDirection]
  rw [← chartLinear_faceUpperRun A B hh i,
    faceUpperRun_decompose, map_smul, chartLinear_faceUnit]

lemma lowerPlanarRun_decompose (i : SourceIndex A B) :
    lowerPlanarRun A B i =
      lowerRunCoeff A B hh i • middlePlanarDirection A B i := by
  apply horizontalIsometry.injective
  rw [map_smul, horizontalIsometry_middlePlanarDirection]
  rw [← chartLinear_faceLowerRun A B hh i,
    faceLowerRun_decompose, map_smul, chartLinear_faceUnit]

/-- Dotting with a positive quarter-turn is the determinant in the exact order
used by the radial-support bridge. -/
lemma inner_quarterTurn_eq_det (x y : Plane) :
    inner ℝ x (planeRotation (Real.pi / 2) y) =
      MixedTurnSafeCut.det y x := by
  simp [planeRotation, planeRotationLinear, inner, Fin.sum_univ_two,
    MixedTurnSafeCut.det]
  ring

/-- Coordinate sign sanity: the positive x basis dotted with the positive
quarter-turn of the positive y basis equals the corresponding determinant. -/
example :
    inner ℝ (WithLp.toLp 2 ![(1 : ℝ), 0])
      (planeRotation (Real.pi / 2) (WithLp.toLp 2 ![(0 : ℝ), 1])) = -1 := by
  norm_num [planeRotation, planeRotationLinear, inner, Fin.sum_univ_two]

lemma source_function_eq_zero_of_next_eq {α : Type*}
    (f : SourceIndex A B → α) (hnext : ∀ i, f (next i) = f i) :
    ∀ i, f i = f (sourceIndexEquiv A B 0) := by
  have hg : ∀ k : Fin (MechanismN A B + 1),
      f (sourceIndexEquiv A B k) = f (sourceIndexEquiv A B 0) := by
    intro k
    induction k using Fin.induction with
    | zero => rfl
    | succ j ih =>
        have hr : finRotate (MechanismN A B + 1) j.castSucc = j.succ :=
          finRotate_of_lt j.isLt
        calc
          f (sourceIndexEquiv A B j.succ) =
              f (sourceIndexEquiv A B (finRotate _ j.castSucc)) := by rw [hr]
          _ = f (next (sourceIndexEquiv A B j.castSucc)) := by
            rw [sourceIndexEquiv_next]
          _ = f (sourceIndexEquiv A B j.castSucc) := hnext _
          _ = f (sourceIndexEquiv A B 0) := ih
  intro i
  simpa using hg ((sourceIndexEquiv A B).symm i)

/-- Telescoping around the actual source cycle. -/
lemma sum_next_sub_self (f : SourceIndex A B → Plane) :
    (∑ i, (f (next i) - f i)) = 0 := by
  rw [Finset.sum_sub_distrib]
  have hp := Equiv.sum_comp (finRotate (sideCount A B)) f
  have hp' : (∑ i, f (next i)) = ∑ i, f i := by
    simpa only [finRotate_eq_next A B] using hp
  rw [hp', sub_self]

/-- Closure of the actual upper rim increments, allowing zero runs. -/
theorem sum_upperPlanarRun_eq_zero :
    (∑ i, upperPlanarRun A B i) = 0 := by
  simpa only [upperPlanarRun] using
    sum_next_sub_self A B (fun i => A.vertex (entryGap A B i).1)

/-- Closure of the actual lower rim increments, allowing zero runs. -/
theorem sum_lowerPlanarRun_eq_zero :
    (∑ i, lowerPlanarRun A B i) = 0 := by
  simpa only [lowerPlanarRun] using
    sum_next_sub_self A B
      (fun i => B.vertex (gapB A B (entryGap A B i)))

/-- The upper-rim coefficients have positive total even though individual
merged-normal runs may vanish (triangular facets). -/
theorem sum_upperRunCoeff_pos :
    0 < ∑ i, upperRunCoeff A B hh i := by
  have hnonneg : 0 ≤ ∑ i, upperRunCoeff A B hh i :=
    Finset.sum_nonneg (fun i _ => upperRunCoeff_nonneg A B hh i)
  apply lt_of_le_of_ne hnonneg
  intro heq
  have hsum : (∑ i, upperRunCoeff A B hh i) = 0 := heq.symm
  have hcoeff : ∀ i, upperRunCoeff A B hh i = 0 := by
    intro i
    exact ((Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) => upperRunCoeff_nonneg A B hh j)).mp hsum)
      i (Finset.mem_univ i)
  have hrun : ∀ i, upperPlanarRun A B i = 0 := by
    intro i
    have hf : faceUpperRun A B hh i = 0 := by
      rw [faceUpperRun_decompose, hcoeff]
      simp
    have hc := chartLinear_faceUpperRun A B hh i
    rw [hf, map_zero] at hc
    exact horizontalIsometry.injective (by simpa using hc.symm)
  have hnext : ∀ i : SourceIndex A B,
      A.vertex (entryGap A B (next i)).1 = A.vertex (entryGap A B i).1 := by
    intro i
    exact sub_eq_zero.mp (hrun i)
  let gapAt (i : Fin nA) : Gap A B :=
    ⟨i, ⟨0, by have hc := one_lt_knots_card A B i; omega⟩⟩
  let sourceAt (i : Fin nA) : SourceIndex A B :=
    next ((orderedGaps A B).symm (toLex (gapAt i)))
  have hsource (i : Fin nA) : entryGap A B (sourceAt i) = gapAt i := by
    change ofLex ((orderedGaps A B)
      (prev (next ((orderedGaps A B).symm (toLex (gapAt i)))))) = gapAt i
    rw [prev_next, OrderIso.apply_symm_apply]
    rfl
  have hconst := source_function_eq_zero_of_next_eq A B
    (fun i => A.vertex (entryGap A B i).1) hnext
  let i0 : Fin nA := ⟨0, by have := A.three_le; omega⟩
  let i1 : Fin nA := ⟨1, by have := A.three_le; omega⟩
  have hv : A.vertex i0 = A.vertex i1 := by
    calc
      A.vertex i0 = A.vertex (entryGap A B (sourceAt i0)).1 := by rw [hsource]
      _ = A.vertex (entryGap A B 0).1 := hconst (sourceAt i0)
      _ = A.vertex (entryGap A B (sourceAt i1)).1 := (hconst (sourceAt i1)).symm
      _ = A.vertex i1 := by rw [hsource]
  have hi := raw_vertex_injective A hv
  have hne : i0 ≠ i1 := by
    intro he
    have hev := congrArg Fin.val he
    norm_num [i0, i1] at hev
  exact hne hi

/-- The lower-rim coefficients also have positive total.  The nontrivial
point is that the dependent merged-gap enumeration cannot keep one lower
vertex constant around every normal cell: every original lower edge ray is a
merged side. -/
theorem sum_lowerRunCoeff_pos :
    0 < ∑ i, lowerRunCoeff A B hh i := by
  have hnonneg : 0 ≤ ∑ i, lowerRunCoeff A B hh i :=
    Finset.sum_nonneg (fun i _ => lowerRunCoeff_nonneg A B hh i)
  apply lt_of_le_of_ne hnonneg
  intro heq
  have hsum : (∑ i, lowerRunCoeff A B hh i) = 0 := heq.symm
  have hcoeff : ∀ i, lowerRunCoeff A B hh i = 0 := by
    intro i
    exact ((Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) => lowerRunCoeff_nonneg A B hh j)).mp hsum)
      i (Finset.mem_univ i)
  have hrun : ∀ i, lowerPlanarRun A B i = 0 := by
    intro i
    rw [lowerPlanarRun_decompose A B hh i, hcoeff]
    simp
  have hnext : ∀ i : SourceIndex A B,
      B.vertex (gapB A B (entryGap A B (next i))) =
        B.vertex (gapB A B (entryGap A B i)) := by
    intro i
    exact sub_eq_zero.mp (hrun i)
  have hconst := source_function_eq_zero_of_next_eq A B
    (fun i => B.vertex (gapB A B (entryGap A B i))) hnext
  let b0 : Fin nB := gapB A B (entryGap A B 0)
  have hgap (g : Gap A B) : gapB A B g = b0 := by
    let s : SourceIndex A B :=
      next ((orderedGaps A B).symm (toLex g))
    have hs : entryGap A B s = g := by
      change ofLex ((orderedGaps A B)
        (prev (next ((orderedGaps A B).symm (toLex g))))) = g
      rw [prev_next, OrderIso.apply_symm_apply]
      rfl
    apply raw_vertex_injective B
    calc
      B.vertex (gapB A B g) =
          B.vertex (gapB A B (entryGap A B s)) := by rw [hs]
      _ = B.vertex (gapB A B (entryGap A B 0)) := hconst s
      _ = B.vertex b0 := rfl
  let e : Fin nB := next b0
  let w : Plane := outwardNormal B.vertex e
  have hw : w ≠ 0 := B.outwardNormal_ne_zero e
  let u : Side A B := ⟨unitRay w, (mem_mergedRays A B _).mpr ⟨Sum.inr e, rfl⟩⟩
  obtain ⟨g, hg⟩ := gapSide_surjective A B u
  have hspec := (gapB_spec A B g).1 (leftKnot A B g)
    ⟨le_rfl, (gap_consecutive A B g).2.2.1.le⟩
  have hunit0 : Maximizes B (unitRay (normalBlend A g.1 (leftKnot A B g))) b0 := by
    rw [← hgap g]
    intro x hx
    have hs := hspec.2 x hx
    change inner ℝ (‖normalBlend A g.1 (leftKnot A B g)‖⁻¹ •
        normalBlend A g.1 (leftKnot A B g)) x ≤
      inner ℝ (‖normalBlend A g.1 (leftKnot A B g)‖⁻¹ •
        normalBlend A g.1 (leftKnot A B g)) (B.vertex (gapB A B g))
    simp only [real_inner_smul_left]
    exact mul_le_mul_of_nonneg_left hs
      (inv_pos.mpr (norm_pos_iff.mpr (normalBlend_ne_zero A g.1))).le
  have hval := congrArg Subtype.val hg
  have hunit : Maximizes B (unitRay w) b0 := by
    rw [← show unitRay (normalBlend A g.1 (leftKnot A B g)) = unitRay w by
      exact hval]
    exact hunit0
  have hwpos : 0 < ‖w‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hw)
  have hmax : Maximizes B w b0 := by
    intro x hx
    have hu := hunit x hx
    change inner ℝ (‖w‖⁻¹ • w) x ≤ inner ℝ (‖w‖⁻¹ • w) (B.vertex b0) at hu
    simp only [real_inner_smul_left] at hu
    exact (mul_le_mul_iff_of_pos_left hwpos).mp hu
  have hemax := edgeNormal_maximizes B e
  have hrow : B.edgeRow e (B.vertex b0) = 0 := by
    have h1 := hemax _ (B.vertex_mem_body b0)
    have h2 := hmax _ (B.vertex_mem_body e)
    rw [B.edgeRow_apply, inner_sub_right]
    linarith
  rcases (B.vertex_edge_eq_iff e b0).mp hrow with heb | hnextb
  · exact (next_ne (le_trans (by norm_num) B.three_le) b0) heb.symm
  · exact self_ne_next_next B.three_le b0 (by simpa [e] using hnextb)

/-- Complete path interval order, including the virtual closing turn. -/
lemma familySource_succ_eq_cyclicPerm
    (k j : Fin (MechanismN A B + 1)) :
    familySource A B k (j.val + 1) =
      sourceIndexEquiv A B (k + finRotate _ j) := by
  rw [familySource_succ, familySource_eq_add A B k j.val j.isLt,
    next_sourceIndexEquiv_add]

/-- The terminal real heading is exactly the real intrinsic defect, not merely
congruent modulo a full turn. -/
theorem familyHeading_full (k : Fin (MechanismN A B + 1)) :
    familyHeading A B hh k (MechanismN A B + 1) =
      intrinsicDelta A B (hh := hh) := by
  rw [familyHeading]
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => intrinsicQ A B (hh := hh) (familySource A B k (j + 1)))
    (MechanismN A B + 1)]
  calc
    (∑ j : Fin (MechanismN A B + 1),
        intrinsicQ A B (hh := hh) (familySource A B k (j.val + 1))) =
      ∑ j : Fin (MechanismN A B + 1),
        intrinsicQ A B (hh := hh)
          (sourceIndexEquiv A B (k + finRotate _ j)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [familySource_succ_eq_cyclicPerm A B]
    _ = ∑ i : SourceIndex A B, intrinsicQ A B (hh := hh) i := by
      let e : Fin (MechanismN A B + 1) ≃ SourceIndex A B :=
        ((finRotate (MechanismN A B + 1)).trans
          (Equiv.addLeft k)).trans (sourceIndexEquiv A B)
      exact Equiv.sum_comp e (intrinsicQ A B (hh := hh))
    _ = intrinsicDelta A B (hh := hh) := rfl

/-- Cumulative original middle-polygon turn parameter in one cyclic root. -/
def familySourcePos (k : Fin (MechanismN A B + 1)) (j : ℕ) : ℝ :=
  ∑ r ∈ Finset.range j,
    middleExteriorTurn A B (next (familySource A B k r))

@[simp] lemma familySourcePos_zero (k : Fin (MechanismN A B + 1)) :
    familySourcePos A B k 0 = 0 := by simp [familySourcePos]

lemma familySourcePos_succ (k : Fin (MechanismN A B + 1)) (j : ℕ) :
    familySourcePos A B k (j + 1) - familySourcePos A B k j =
      middleExteriorTurn A B (next (familySource A B k j)) := by
  rw [familySourcePos, familySourcePos, Finset.sum_range_succ]
  ring

lemma familySourcePos_full (k : Fin (MechanismN A B + 1)) :
    familySourcePos A B k (MechanismN A B + 1) = 2 * Real.pi := by
  rw [familySourcePos]
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => middleExteriorTurn A B (next (familySource A B k j)))
    (MechanismN A B + 1)]
  calc
    (∑ j : Fin (MechanismN A B + 1),
        middleExteriorTurn A B (next (familySource A B k j.val))) =
      ∑ j : Fin (MechanismN A B + 1),
        middleExteriorTurn A B
          (sourceIndexEquiv A B (k + finRotate _ j)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← familySource_succ, familySource_succ_eq_cyclicPerm A B]
    _ = ∑ i : SourceIndex A B, middleExteriorTurn A B i := by
      let e : Fin (MechanismN A B + 1) ≃ SourceIndex A B :=
        ((finRotate (MechanismN A B + 1)).trans
          (Equiv.addLeft k)).trans (sourceIndexEquiv A B)
      exact Equiv.sum_comp e (middleExteriorTurn A B)
    _ = 2 * Real.pi := sum_middleExteriorTurn_eq_two_pi A B

lemma middlePlanarDirection_familySource
    (k : Fin (MechanismN A B + 1)) (j : ℕ) :
    middlePlanarDirection A B (familySource A B k j) =
      planeRotation (-familySourcePos A B k j)
        (middlePlanarDirection A B (familySource A B k 0)) := by
  induction j with
  | zero => simp [familySourcePos]
  | succ j ih =>
      calc
        middlePlanarDirection A B (familySource A B k (j + 1)) =
            middlePlanarDirection A B (next (familySource A B k j)) := by
          rw [familySource_succ]
        _ = planeRotation
              (-middleExteriorTurn A B (next (familySource A B k j)))
              (middlePlanarDirection A B (familySource A B k j)) := by
          simpa only [prev_next] using
            middlePlanarDirection_next_rotation A B (next (familySource A B k j))
        _ = planeRotation
              (-middleExteriorTurn A B (next (familySource A B k j)))
              (planeRotation (-familySourcePos A B k j)
                (middlePlanarDirection A B (familySource A B k 0))) := by rw [ih]
        _ = planeRotation
              (-middleExteriorTurn A B (next (familySource A B k j)) +
                -familySourcePos A B k j)
              (middlePlanarDirection A B (familySource A B k 0)) := by
          rw [planeRotation_comp]
        _ = planeRotation (-familySourcePos A B k (j + 1))
              (middlePlanarDirection A B (familySource A B k 0)) := by
          have hs := familySourcePos_succ A B k j
          congr 2
          linarith

lemma sum_family_upper_weight_direction
    (k : Fin (MechanismN A B + 1)) :
    (∑ j : Fin (MechanismN A B + 1),
      upperRunCoeff A B hh (familySource A B k j.val) •
        middlePlanarDirection A B (familySource A B k j.val)) = 0 := by
  let e : Fin (MechanismN A B + 1) ≃ SourceIndex A B :=
    (Equiv.addLeft k).trans (sourceIndexEquiv A B)
  calc
    _ = ∑ j : Fin (MechanismN A B + 1),
        upperRunCoeff A B hh (e j) • middlePlanarDirection A B (e j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [familySource_eq_add A B k j.val j.isLt]
      simp [e]
    _ = ∑ i : SourceIndex A B,
        upperRunCoeff A B hh i • middlePlanarDirection A B i :=
      Equiv.sum_comp e (fun i =>
        upperRunCoeff A B hh i • middlePlanarDirection A B i)
    _ = ∑ i : SourceIndex A B, upperPlanarRun A B i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [upperPlanarRun_decompose A B hh]
    _ = 0 := sum_upperPlanarRun_eq_zero A B

lemma sum_family_upper_cos_sourcePos
    (k : Fin (MechanismN A B + 1)) :
    (∑ j : Fin (MechanismN A B + 1),
      upperRunCoeff A B hh (familySource A B k j.val) *
        Real.cos (familySourcePos A B k j.val)) = 0 := by
  let u := middlePlanarDirection A B (familySource A B k 0)
  have hsum := congrArg (inner ℝ u) (sum_family_upper_weight_direction A B hh k)
  rw [inner_sum, inner_zero_right] at hsum
  calc
    _ = ∑ j : Fin (MechanismN A B + 1),
        inner ℝ u
          (upperRunCoeff A B hh (familySource A B k j.val) •
            middlePlanarDirection A B (familySource A B k j.val)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [inner_smul_right, middlePlanarDirection_familySource,
        inner_rotation_self_of_unit u (middlePlanarDirection_norm A B _)]
      simp [Real.cos_neg]
    _ = 0 := hsum

lemma sum_family_upper_sin_sourcePos
    (k : Fin (MechanismN A B + 1)) :
    (∑ j : Fin (MechanismN A B + 1),
      upperRunCoeff A B hh (familySource A B k j.val) *
        Real.sin (familySourcePos A B k j.val)) = 0 := by
  let u := middlePlanarDirection A B (familySource A B k 0)
  have hsum := congrArg
    (inner ℝ (planeRotation (Real.pi / 2) u))
    (sum_family_upper_weight_direction A B hh k)
  rw [inner_sum, inner_zero_right] at hsum
  have hneg : (∑ j : Fin (MechanismN A B + 1),
      -(upperRunCoeff A B hh (familySource A B k j.val) *
        Real.sin (familySourcePos A B k j.val))) = 0 := by
    calc
      _ = ∑ j : Fin (MechanismN A B + 1),
          inner ℝ (planeRotation (Real.pi / 2) u)
            (upperRunCoeff A B hh (familySource A B k j.val) •
              middlePlanarDirection A B (familySource A B k j.val)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [inner_smul_right, middlePlanarDirection_familySource,
          inner_quarter_rotation_neg_of_unit u
            (middlePlanarDirection_norm A B _)]
        ring
      _ = 0 := hsum
  rw [Finset.sum_neg_distrib] at hneg
  exact neg_eq_zero.mp hneg

lemma sum_family_lower_weight_direction
    (k : Fin (MechanismN A B + 1)) :
    (∑ j : Fin (MechanismN A B + 1),
      lowerRunCoeff A B hh (familySource A B k j.val) •
        middlePlanarDirection A B (familySource A B k j.val)) = 0 := by
  let e : Fin (MechanismN A B + 1) ≃ SourceIndex A B :=
    (Equiv.addLeft k).trans (sourceIndexEquiv A B)
  calc
    _ = ∑ j : Fin (MechanismN A B + 1),
        lowerRunCoeff A B hh (e j) • middlePlanarDirection A B (e j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [familySource_eq_add A B k j.val j.isLt]
      simp [e]
    _ = ∑ i : SourceIndex A B,
        lowerRunCoeff A B hh i • middlePlanarDirection A B i :=
      Equiv.sum_comp e (fun i =>
        lowerRunCoeff A B hh i • middlePlanarDirection A B i)
    _ = ∑ i : SourceIndex A B, lowerPlanarRun A B i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [lowerPlanarRun_decompose A B hh]
    _ = 0 := sum_lowerPlanarRun_eq_zero A B

lemma sum_family_lower_cos_sourcePos
    (k : Fin (MechanismN A B + 1)) :
    (∑ j : Fin (MechanismN A B + 1),
      lowerRunCoeff A B hh (familySource A B k j.val) *
        Real.cos (familySourcePos A B k j.val)) = 0 := by
  let u := middlePlanarDirection A B (familySource A B k 0)
  have hsum := congrArg (inner ℝ u) (sum_family_lower_weight_direction A B hh k)
  rw [inner_sum, inner_zero_right] at hsum
  calc
    _ = ∑ j : Fin (MechanismN A B + 1),
        inner ℝ u
          (lowerRunCoeff A B hh (familySource A B k j.val) •
            middlePlanarDirection A B (familySource A B k j.val)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [inner_smul_right, middlePlanarDirection_familySource,
        inner_rotation_self_of_unit u (middlePlanarDirection_norm A B _)]
      simp [Real.cos_neg]
    _ = 0 := hsum

lemma sum_family_lower_sin_sourcePos
    (k : Fin (MechanismN A B + 1)) :
    (∑ j : Fin (MechanismN A B + 1),
      lowerRunCoeff A B hh (familySource A B k j.val) *
        Real.sin (familySourcePos A B k j.val)) = 0 := by
  let u := middlePlanarDirection A B (familySource A B k 0)
  have hsum := congrArg
    (inner ℝ (planeRotation (Real.pi / 2) u))
    (sum_family_lower_weight_direction A B hh k)
  rw [inner_sum, inner_zero_right] at hsum
  have hneg : (∑ j : Fin (MechanismN A B + 1),
      -(lowerRunCoeff A B hh (familySource A B k j.val) *
        Real.sin (familySourcePos A B k j.val))) = 0 := by
    calc
      _ = ∑ j : Fin (MechanismN A B + 1),
          inner ℝ (planeRotation (Real.pi / 2) u)
            (lowerRunCoeff A B hh (familySource A B k j.val) •
              middlePlanarDirection A B (familySource A B k j.val)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [inner_smul_right, middlePlanarDirection_familySource,
          inner_quarter_rotation_neg_of_unit u
            (middlePlanarDirection_norm A B _)]
        ring
      _ = 0 := hsum
  rw [Finset.sum_neg_distrib] at hneg
  exact neg_eq_zero.mp hneg

lemma sum_family_upperRunCoeff_pos
    (k : Fin (MechanismN A B + 1)) :
    0 < ∑ j : Fin (MechanismN A B + 1),
      upperRunCoeff A B hh (familySource A B k j.val) := by
  let e : Fin (MechanismN A B + 1) ≃ SourceIndex A B :=
    (Equiv.addLeft k).trans (sourceIndexEquiv A B)
  have he : (∑ j : Fin (MechanismN A B + 1),
      upperRunCoeff A B hh (familySource A B k j.val)) =
      ∑ i : SourceIndex A B, upperRunCoeff A B hh i := by
    calc
      _ = ∑ j : Fin (MechanismN A B + 1), upperRunCoeff A B hh (e j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [familySource_eq_add A B k j.val j.isLt]
        simp [e]
      _ = _ := Equiv.sum_comp e (upperRunCoeff A B hh)
  rw [he]
  exact sum_upperRunCoeff_pos A B hh

/-- The actual upper-rim folded-turn chain, with source closure supplied by the
original polygon and terminal heading supplied by the developed holonomy. -/
noncomputable def upperFoldedChain
    (k : Fin (MechanismN A B + 1)) :
    FoldedTurnProjection.Chain (MechanismN A B) where
  gap j := middleExteriorTurn A B (next (familySource A B k j.val))
  turnValue j := intrinsicQ A B (hh := hh) (next (familySource A B k j.val))
  weight j := upperRunCoeff A B hh (familySource A B k j.val)
  sourcePos j := familySourcePos A B k j.val
  heading j := familyHeading A B hh k j.val
  gap_pos j := middleExteriorTurn_pos A B _
  turnValue_strict j := abs_intrinsicQ_lt_middleExteriorTurn A B hh _
  source_step j := by
    simpa using familySourcePos_succ A B k j.val
  heading_step j := by
    simpa using familyHeading_succ A B hh k j.val
  source_zero := familySourcePos_zero A B k
  heading_zero := familyHeading_zero A B hh k
  source_last := familySourcePos_full A B k
  weight_nonneg j := upperRunCoeff_nonneg A B hh _
  weight_sum_pos := sum_family_upperRunCoeff_pos A B hh k
  closure_cos := sum_family_upper_cos_sourcePos A B hh k
  closure_sin := sum_family_upper_sin_sourcePos A B hh k

lemma sum_family_lowerRunCoeff_pos
    (k : Fin (MechanismN A B + 1)) :
    0 < ∑ j : Fin (MechanismN A B + 1),
      lowerRunCoeff A B hh (familySource A B k j.val) := by
  let e : Fin (MechanismN A B + 1) ≃ SourceIndex A B :=
    (Equiv.addLeft k).trans (sourceIndexEquiv A B)
  have he : (∑ j : Fin (MechanismN A B + 1),
      lowerRunCoeff A B hh (familySource A B k j.val)) =
      ∑ i : SourceIndex A B, lowerRunCoeff A B hh i := by
    calc
      _ = ∑ j : Fin (MechanismN A B + 1), lowerRunCoeff A B hh (e j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [familySource_eq_add A B k j.val j.isLt]
        simp [e]
      _ = _ := Equiv.sum_comp e (lowerRunCoeff A B hh)
  rw [he]
  exact sum_lowerRunCoeff_pos A B hh

noncomputable def lowerFoldedChain
    (k : Fin (MechanismN A B + 1)) :
    FoldedTurnProjection.Chain (MechanismN A B) where
  gap j := middleExteriorTurn A B (next (familySource A B k j.val))
  turnValue j := intrinsicQ A B (hh := hh) (next (familySource A B k j.val))
  weight j := lowerRunCoeff A B hh (familySource A B k j.val)
  sourcePos j := familySourcePos A B k j.val
  heading j := familyHeading A B hh k j.val
  gap_pos j := middleExteriorTurn_pos A B _
  turnValue_strict j := abs_intrinsicQ_lt_middleExteriorTurn A B hh _
  source_step j := by simpa using familySourcePos_succ A B k j.val
  heading_step j := by simpa using familyHeading_succ A B hh k j.val
  source_zero := familySourcePos_zero A B k
  heading_zero := familyHeading_zero A B hh k
  source_last := familySourcePos_full A B k
  weight_nonneg j := lowerRunCoeff_nonneg A B hh _
  weight_sum_pos := sum_family_lowerRunCoeff_pos A B hh k
  closure_cos := sum_family_lower_cos_sourcePos A B hh k
  closure_sin := sum_family_lower_sin_sourcePos A B hh k

@[simp] lemma lowerFoldedChain_delta
    (k : Fin (MechanismN A B + 1)) :
    (lowerFoldedChain A B hh k).delta = intrinsicDelta A B (hh := hh) := by
  simpa [FoldedTurnProjection.Chain.delta, lowerFoldedChain] using
    familyHeading_full A B hh k

@[simp] lemma upperFoldedChain_delta
    (k : Fin (MechanismN A B + 1)) :
    (upperFoldedChain A B hh k).delta = intrinsicDelta A B (hh := hh) := by
  simpa [FoldedTurnProjection.Chain.delta, upperFoldedChain] using
    familyHeading_full A B hh k

lemma familySource_full (k : Fin (MechanismN A B + 1)) :
    familySource A B k (MechanismN A B + 1) = familySource A B k 0 := by
  simpa [finRotate_apply] using
    familySource_succ_eq_cyclicPerm A B k (Fin.last (MechanismN A B))

lemma intrinsicFaceChart_entryUpper_full (k : Fin (MechanismN A B + 1)) :
    intrinsicFaceChart A B hh (familySource A B k (MechanismN A B + 1))
        (faceEntryUpper A B hh (familySource A B k (MechanismN A B + 1))) =
      intrinsicFaceChart A B hh (familySource A B k 0)
        (faceEntryUpper A B hh (familySource A B k 0)) :=
  congrArg (fun i => intrinsicFaceChart A B hh i (faceEntryUpper A B hh i))
    (familySource_full A B k)

lemma intrinsicFaceChart_entryLower_full (k : Fin (MechanismN A B + 1)) :
    intrinsicFaceChart A B hh (familySource A B k (MechanismN A B + 1))
        (faceEntryLower A B hh (familySource A B k (MechanismN A B + 1))) =
      intrinsicFaceChart A B hh (familySource A B k 0)
        (faceEntryLower A B hh (familySource A B k 0)) :=
  congrArg (fun i => intrinsicFaceChart A B hh i (faceEntryLower A B hh i))
    (familySource_full A B k)

noncomputable def developedLower (k : Fin (MechanismN A B + 1)) (j : ℕ) : Plane :=
  directDevelopedMap A B hh k j
    (faceEntryLower A B hh (familySource A B k j))

noncomputable def developedUpper (k : Fin (MechanismN A B + 1)) (j : ℕ) : Plane :=
  directDevelopedMap A B hh k j
    (faceEntryUpper A B hh (familySource A B k j))

noncomputable def developedForward (k : Fin (MechanismN A B + 1)) (j : ℕ) : Plane :=
  planeRotation (familyHeading A B hh k j) (MixedTurnSafeCut.direction 0)

lemma developedUpper_run (k : Fin (MechanismN A B + 1)) (j : ℕ) :
    directDevelopedMap A B hh k j
          (faceExitUpper A B hh (familySource A B k j)) -
        developedUpper A B hh k j =
      upperRunCoeff A B hh (familySource A B k j) •
        developedForward A B hh k j := by
  rw [developedUpper, directDevelopedMap_apply, directDevelopedMap_apply]
  rw [show
      (planeRotation (familyHeading A B hh k j))
            (intrinsicFaceChart A B hh (familySource A B k j)
              (faceExitUpper A B hh (familySource A B k j))) +
          directTranslation A B hh k j -
        ((planeRotation (familyHeading A B hh k j))
            (intrinsicFaceChart A B hh (familySource A B k j)
              (faceEntryUpper A B hh (familySource A B k j))) +
          directTranslation A B hh k j) =
      planeRotation (familyHeading A B hh k j)
        (intrinsicFaceChart A B hh (familySource A B k j)
            (faceExitUpper A B hh (familySource A B k j)) -
          intrinsicFaceChart A B hh (familySource A B k j)
            (faceEntryUpper A B hh (familySource A B k j))) by rw [map_sub]; abel]
  have hc := (intrinsicFaceChart A B hh (familySource A B k j)).map_vsub
    (faceExitUpper A B hh (familySource A B k j))
    (faceEntryUpper A B hh (familySource A B k j))
  change (intrinsicFaceChart A B hh (familySource A B k j)).linearIsometryEquiv
      (faceExitUpper A B hh (familySource A B k j) -
        faceEntryUpper A B hh (familySource A B k j)) =
    intrinsicFaceChart A B hh (familySource A B k j)
        (faceExitUpper A B hh (familySource A B k j)) -
      intrinsicFaceChart A B hh (familySource A B k j)
        (faceEntryUpper A B hh (familySource A B k j)) at hc
  rw [← hc, ← faceUpperRun, faceUpperRun_decompose, map_smul,
    intrinsicFaceChart_linear_faceUnit, map_smul]
  simp [developedForward, MixedTurnSafeCut.direction]

lemma developedLower_run (k : Fin (MechanismN A B + 1)) (j : ℕ) :
    directDevelopedMap A B hh k j
          (faceExitLower A B hh (familySource A B k j)) -
        developedLower A B hh k j =
      lowerRunCoeff A B hh (familySource A B k j) •
        developedForward A B hh k j := by
  rw [developedLower, directDevelopedMap_apply, directDevelopedMap_apply]
  rw [show
      (planeRotation (familyHeading A B hh k j))
            (intrinsicFaceChart A B hh (familySource A B k j)
              (faceExitLower A B hh (familySource A B k j))) +
          directTranslation A B hh k j -
        ((planeRotation (familyHeading A B hh k j))
            (intrinsicFaceChart A B hh (familySource A B k j)
              (faceEntryLower A B hh (familySource A B k j))) +
          directTranslation A B hh k j) =
      planeRotation (familyHeading A B hh k j)
        (intrinsicFaceChart A B hh (familySource A B k j)
            (faceExitLower A B hh (familySource A B k j)) -
          intrinsicFaceChart A B hh (familySource A B k j)
            (faceEntryLower A B hh (familySource A B k j))) by rw [map_sub]; abel]
  have hc := (intrinsicFaceChart A B hh (familySource A B k j)).map_vsub
    (faceExitLower A B hh (familySource A B k j))
    (faceEntryLower A B hh (familySource A B k j))
  change (intrinsicFaceChart A B hh (familySource A B k j)).linearIsometryEquiv
      (faceExitLower A B hh (familySource A B k j) -
        faceEntryLower A B hh (familySource A B k j)) =
    intrinsicFaceChart A B hh (familySource A B k j)
        (faceExitLower A B hh (familySource A B k j)) -
      intrinsicFaceChart A B hh (familySource A B k j)
        (faceEntryLower A B hh (familySource A B k j)) at hc
  rw [← hc, ← faceLowerRun, faceLowerRun_decompose, map_smul,
    intrinsicFaceChart_linear_faceUnit, map_smul]
  simp [developedForward, MixedTurnSafeCut.direction]

/-- The direct, depth-independent maps glue the entire physical hinge, for
all real hinge parameters and every root cut. -/
theorem directDevelopedMap_exitAt_eq_next_entryAt
    (k : Fin (MechanismN A B + 1)) (j : ℕ) (t : ℝ) :
    directDevelopedMap A B hh k j
        (faceExitAt A B hh t (familySource A B k j)) =
      directDevelopedMap A B hh k (j + 1)
        (faceEntryAt A B hh t (familySource A B k (j + 1))) := by
  rw [directDevelopedMap_apply, directDevelopedMap_apply]
  rw [familySource_succ]
  have hhead := familyHeading_succ A B hh k j
  rw [familySource_succ] at hhead
  have hhead' : familyHeading A B hh k (j + 1) =
      familyHeading A B hh k j +
        intrinsicQ A B (hh := hh) (next (familySource A B k j)) := by
    linarith
  rw [hhead', directTranslation_succ]
  have ht := directTransition_entryAt A B hh t (familySource A B k j)
  have hr := congrArg (planeRotation (familyHeading A B hh k j)) ht
  rw [map_add, planeRotation_comp] at hr
  rw [← hr]
  abel

lemma developedUpper_succ_sub (k : Fin (MechanismN A B + 1)) (j : ℕ) :
    developedUpper A B hh k (j + 1) - developedUpper A B hh k j =
      upperRunCoeff A B hh (familySource A B k j) •
        developedForward A B hh k j := by
  have hg := directDevelopedMap_exitAt_eq_next_entryAt A B hh k j 1
  have hx : faceExitAt A B hh 1 (familySource A B k j) =
      faceExitUpper A B hh (familySource A B k j) := by
    simp [faceExitAt, AffineMap.lineMap_apply_module]
  have he : faceEntryAt A B hh 1 (familySource A B k (j + 1)) =
      faceEntryUpper A B hh (familySource A B k (j + 1)) := by
    rw [faceEntryAt, AffineMap.lineMap_apply_module]
    module
  rw [hx, he] at hg
  have hg' : directDevelopedMap A B hh k j
        (faceExitUpper A B hh (familySource A B k j)) =
      developedUpper A B hh k (j + 1) := by
    exact hg
  rw [← hg']
  exact developedUpper_run A B hh k j

lemma developedLower_succ_sub (k : Fin (MechanismN A B + 1)) (j : ℕ) :
    developedLower A B hh k (j + 1) - developedLower A B hh k j =
      lowerRunCoeff A B hh (familySource A B k j) •
        developedForward A B hh k j := by
  have hg := directDevelopedMap_exitAt_eq_next_entryAt A B hh k j 0
  have hx : faceExitAt A B hh 0 (familySource A B k j) =
      faceExitLower A B hh (familySource A B k j) := by
    simp [faceExitAt, AffineMap.lineMap_apply_module]
  have he : faceEntryAt A B hh 0 (familySource A B k (j + 1)) =
      faceEntryLower A B hh (familySource A B k (j + 1)) := by
    rw [faceEntryAt, AffineMap.lineMap_apply_module]
    module
  rw [hx, he] at hg
  have hg' : directDevelopedMap A B hh k j
        (faceExitLower A B hh (familySource A B k j)) =
      developedLower A B hh k (j + 1) := by
    exact hg
  rw [← hg']
  exact developedLower_run A B hh k j

lemma sum_developedUpper_run (k : Fin (MechanismN A B + 1)) :
    (∑ j : Fin (MechanismN A B + 1),
      upperRunCoeff A B hh (familySource A B k j.val) •
        developedForward A B hh k j.val) =
      developedUpper A B hh k (MechanismN A B + 1) -
        developedUpper A B hh k 0 := by
  calc
    _ = ∑ j : Fin (MechanismN A B + 1),
        (fun r : Fin (MechanismN A B + 1) =>
          developedUpper A B hh k (r.val + 1) -
            developedUpper A B hh k r.val) j := by
      apply Finset.sum_congr rfl
      intro j _
      exact (developedUpper_succ_sub A B hh k j.val).symm
    _ = ∑ j ∈ Finset.range (MechanismN A B + 1),
        (developedUpper A B hh k (j + 1) - developedUpper A B hh k j) :=
      Fin.sum_univ_eq_sum_range
        (fun j => developedUpper A B hh k (j + 1) - developedUpper A B hh k j)
        (MechanismN A B + 1)
    _ = _ := Finset.sum_range_sub (developedUpper A B hh k) (MechanismN A B + 1)

lemma sum_developedLower_run (k : Fin (MechanismN A B + 1)) :
    (∑ j : Fin (MechanismN A B + 1),
      lowerRunCoeff A B hh (familySource A B k j.val) •
        developedForward A B hh k j.val) =
      developedLower A B hh k (MechanismN A B + 1) -
        developedLower A B hh k 0 := by
  calc
    _ = ∑ j : Fin (MechanismN A B + 1),
        (fun r : Fin (MechanismN A B + 1) =>
          developedLower A B hh k (r.val + 1) -
            developedLower A B hh k r.val) j := by
      apply Finset.sum_congr rfl
      intro j _
      exact (developedLower_succ_sub A B hh k j.val).symm
    _ = ∑ j ∈ Finset.range (MechanismN A B + 1),
        (developedLower A B hh k (j + 1) - developedLower A B hh k j) :=
      Fin.sum_univ_eq_sum_range
        (fun j => developedLower A B hh k (j + 1) - developedLower A B hh k j)
        (MechanismN A B + 1)
    _ = _ := Finset.sum_range_sub (developedLower A B hh k) (MechanismN A B + 1)

lemma developed_hinge_orientation_neg
    (k : Fin (MechanismN A B + 1)) (j : ℕ) :
    MixedTurnSafeCut.det (developedForward A B hh k j)
      (developedUpper A B hh k j - developedLower A B hh k j) < 0 := by
  rw [developedForward, developedUpper, developedLower]
  simp only [directDevelopedMap_apply]
  rw [show
      (planeRotation (familyHeading A B hh k j))
            (intrinsicFaceChart A B hh (familySource A B k j)
              (faceEntryUpper A B hh (familySource A B k j))) +
          directTranslation A B hh k j -
        ((planeRotation (familyHeading A B hh k j))
            (intrinsicFaceChart A B hh (familySource A B k j)
              (faceEntryLower A B hh (familySource A B k j))) +
          directTranslation A B hh k j) =
      planeRotation (familyHeading A B hh k j)
        (intrinsicFaceChart A B hh (familySource A B k j)
            (faceEntryUpper A B hh (familySource A B k j)) -
          intrinsicFaceChart A B hh (familySource A B k j)
            (faceEntryLower A B hh (familySource A B k j))) by
      rw [map_sub]; abel]
  rw [planeRotation_det]
  rw [show intrinsicFaceChart A B hh (familySource A B k j)
          (faceEntryUpper A B hh (familySource A B k j)) -
        intrinsicFaceChart A B hh (familySource A B k j)
          (faceEntryLower A B hh (familySource A B k j)) =
      localD A B hh 0 (familySource A B k j) by
        rw [localD, localB]
        congr 1 <;> simp [faceEntryAt, AffineMap.lineMap_apply_module]]
  rw [localD_eq]
  simp [MixedTurnSafeCut.direction, MixedTurnSafeCut.det]
  exact faceS_pos A B hh (familySource A B k j)

lemma developedForward_ne_zero (k : Fin (MechanismN A B + 1)) (j : ℕ) :
    developedForward A B hh k j ≠ 0 := by
  intro hz
  have hn := (planeRotation (familyHeading A B hh k j)).norm_map
    (MixedTurnSafeCut.direction 0)
  change ‖developedForward A B hh k j‖ = ‖MixedTurnSafeCut.direction 0‖ at hn
  rw [hz, norm_zero] at hn
  have hdir : MixedTurnSafeCut.direction 0 = 0 := norm_eq_zero.mp hn.symm
  have hc := congrArg (fun x : Plane => x 0) hdir
  norm_num [MixedTurnSafeCut.direction] at hc

/-- The actual complete affine circuit in a direct root frame.  Its translation
is the full accumulated `directTranslation`, not discarded. -/
noncomputable def fullCircuit (k : Fin (MechanismN A B + 1)) : Plane →ᵃⁱ[ℝ] Plane :=
  planarPlacement (intrinsicDelta A B (hh := hh)) 0
    (directTranslation A B hh k (MechanismN A B + 1))

@[simp] lemma fullCircuit_apply (k : Fin (MechanismN A B + 1)) (x : Plane) :
    fullCircuit A B hh k x =
      planeRotation (intrinsicDelta A B (hh := hh)) x +
        directTranslation A B hh k (MechanismN A B + 1) := by
  simp [fullCircuit, planarPlacement_apply]
  abel

lemma developedUpper_full (k : Fin (MechanismN A B + 1)) :
    developedUpper A B hh k (MechanismN A B + 1) =
      fullCircuit A B hh k (developedUpper A B hh k 0) := by
  unfold developedUpper
  rw [directDevelopedMap_apply, directDevelopedMap_apply,
    intrinsicFaceChart_entryUpper_full A B hh k,
    familyHeading_full A B hh]
  simp [familyHeading_zero, fullCircuit_apply]

lemma developedLower_full (k : Fin (MechanismN A B + 1)) :
    developedLower A B hh k (MechanismN A B + 1) =
      fullCircuit A B hh k (developedLower A B hh k 0) := by
  unfold developedLower
  rw [directDevelopedMap_apply, directDevelopedMap_apply,
    intrinsicFaceChart_entryLower_full A B hh k,
    familyHeading_full A B hh]
  simp [familyHeading_zero, fullCircuit_apply]

lemma sum_developedUpper_run_eq_circuit (k : Fin (MechanismN A B + 1)) :
    (∑ j : Fin (MechanismN A B + 1),
      upperRunCoeff A B hh (familySource A B k j.val) •
        developedForward A B hh k j.val) =
      fullCircuit A B hh k (developedUpper A B hh k 0) -
        developedUpper A B hh k 0 := by
  rw [sum_developedUpper_run, developedUpper_full]

lemma sum_developedLower_run_eq_circuit (k : Fin (MechanismN A B + 1)) :
    (∑ j : Fin (MechanismN A B + 1),
      lowerRunCoeff A B hh (familySource A B k j.val) •
        developedForward A B hh k j.val) =
      fullCircuit A B hh k (developedLower A B hh k 0) -
        developedLower A B hh k 0 := by
  rw [sum_developedLower_run, developedLower_full]

lemma inner_developedForward (k : Fin (MechanismN A B + 1)) (j : ℕ) :
    inner ℝ
        (planeRotation (intrinsicDelta A B (hh := hh) / 2)
          (developedForward A B hh k 0))
        (developedForward A B hh k j) =
      Real.cos (familyHeading A B hh k j -
        intrinsicDelta A B (hh := hh) / 2) := by
  rw [developedForward, developedForward, familyHeading_zero,
    planeRotation_zero_angle]
  simp [planeRotation, planeRotationLinear, MixedTurnSafeCut.direction,
    inner, Fin.sum_univ_two, Real.cos_sub]

lemma upper_projection_sum_eq_circuit (k : Fin (MechanismN A B + 1)) :
    (∑ j : Fin (MechanismN A B + 1),
      upperRunCoeff A B hh (familySource A B k j.val) *
        Real.cos (familyHeading A B hh k j.val -
          intrinsicDelta A B (hh := hh) / 2)) =
      inner ℝ
        (planeRotation (intrinsicDelta A B (hh := hh) / 2)
          (developedForward A B hh k 0))
        (fullCircuit A B hh k (developedUpper A B hh k 0) -
          developedUpper A B hh k 0) := by
  rw [← sum_developedUpper_run_eq_circuit]
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [inner_smul_right, inner_developedForward]

lemma lower_projection_sum_eq_circuit (k : Fin (MechanismN A B + 1)) :
    (∑ j : Fin (MechanismN A B + 1),
      lowerRunCoeff A B hh (familySource A B k j.val) *
        Real.cos (familyHeading A B hh k j.val -
          intrinsicDelta A B (hh := hh) / 2)) =
      inner ℝ
        (planeRotation (intrinsicDelta A B (hh := hh) / 2)
          (developedForward A B hh k 0))
        (fullCircuit A B hh k (developedLower A B hh k 0) -
          developedLower A B hh k 0) := by
  rw [← sum_developedLower_run_eq_circuit]
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [inner_smul_right, inner_developedForward]

theorem upper_circuit_projection_pos_of_circular_contraction
    (k : Fin (MechanismN A B + 1)) (α : ℝ)
    (hα : α ∈ Set.Icc (0 : ℝ) (2 * Real.pi))
    (hfold : ∀ j : Fin (MechanismN A B + 1),
      |(upperFoldedChain A B hh k).heading j.castSucc -
          (upperFoldedChain A B hh k).delta / 2| ≤
        FoldedTurnProjection.circularDist
          ((upperFoldedChain A B hh k).sourcePos j.castSucc) α)
    (hstrict : ∃ j : Fin (MechanismN A B + 1),
      0 < (upperFoldedChain A B hh k).weight j ∧
      |(upperFoldedChain A B hh k).heading j.castSucc -
          (upperFoldedChain A B hh k).delta / 2| <
        FoldedTurnProjection.circularDist
          ((upperFoldedChain A B hh k).sourcePos j.castSucc) α) :
    0 < inner ℝ
      (planeRotation (intrinsicDelta A B (hh := hh) / 2)
        (developedForward A B hh k 0))
      (fullCircuit A B hh k (developedUpper A B hh k 0) -
        developedUpper A B hh k 0) := by
  rw [← upper_projection_sum_eq_circuit]
  have hp := FoldedTurnProjection.projection_pos_of_circular_contraction
    (upperFoldedChain A B hh k) α hα hfold hstrict
  rw [upperFoldedChain_delta] at hp
  simpa [upperFoldedChain] using hp

theorem upper_circuit_projection_pos
    (k : Fin (MechanismN A B + 1)) :
    0 < inner ℝ
      (planeRotation (intrinsicDelta A B (hh := hh) / 2)
        (developedForward A B hh k 0))
      (fullCircuit A B hh k (developedUpper A B hh k 0) -
        developedUpper A B hh k 0) := by
  rw [← upper_projection_sum_eq_circuit]
  have hp := FoldedTurnProjection.projection_pos (upperFoldedChain A B hh k)
  rw [upperFoldedChain_delta] at hp
  simpa [upperFoldedChain] using hp

theorem lower_circuit_projection_pos
    (k : Fin (MechanismN A B + 1)) :
    0 < inner ℝ
      (planeRotation (intrinsicDelta A B (hh := hh) / 2)
        (developedForward A B hh k 0))
      (fullCircuit A B hh k (developedLower A B hh k 0) -
        developedLower A B hh k 0) := by
  rw [← lower_projection_sum_eq_circuit]
  have hp := FoldedTurnProjection.projection_pos (lowerFoldedChain A B hh k)
  rw [lowerFoldedChain_delta] at hp
  simpa [lowerFoldedChain] using hp

lemma intrinsicDelta_cos_ne_one
    (hΔ : intrinsicDelta A B (hh := hh) ≠ 0) :
    Real.cos (intrinsicDelta A B (hh := hh)) ≠ 1 := by
  intro hc
  have habs := abs_intrinsicDelta_lt_two_pi A B hh
  have hlo : -(2 * Real.pi) < intrinsicDelta A B (hh := hh) :=
    (abs_lt.mp habs).1
  have hhi : intrinsicDelta A B (hh := hh) < 2 * Real.pi :=
    (abs_lt.mp habs).2
  exact hΔ ((Real.cos_eq_one_iff_of_lt_of_lt hlo hhi).mp hc)

/-- The visible denominator of the coordinate inverse of `I - Rot Δ`. -/
def circuitDenom : ℝ :=
  (1 - Real.cos (intrinsicDelta A B (hh := hh))) ^ 2 +
    Real.sin (intrinsicDelta A B (hh := hh)) ^ 2

lemma circuitDenom_ne_zero
    (hΔ : intrinsicDelta A B (hh := hh) ≠ 0) :
    circuitDenom A B hh ≠ 0 := by
  have hc := intrinsicDelta_cos_ne_one A B hh hΔ
  have ht := Real.sin_sq_add_cos_sq (intrinsicDelta A B (hh := hh))
  dsimp [circuitDenom]
  intro hz
  have ha : 1 - Real.cos (intrinsicDelta A B (hh := hh)) = 0 := by
    nlinarith [sq_nonneg (1 - Real.cos (intrinsicDelta A B (hh := hh))),
      sq_nonneg (Real.sin (intrinsicDelta A B (hh := hh)))]
  exact hc (by linarith)

/-- Genuine pole of the complete affine circuit for nonzero real defect. -/
noncomputable def circuitPole (k : Fin (MechanismN A B + 1))
    (_hΔ : intrinsicDelta A B (hh := hh) ≠ 0) : Plane :=
  let Δ := intrinsicDelta A B (hh := hh)
  let t := directTranslation A B hh k (MechanismN A B + 1)
  let D := circuitDenom A B hh
  WithLp.toLp 2 ![((1 - Real.cos Δ) * t 0 - Real.sin Δ * t 1) / D,
    (Real.sin Δ * t 0 + (1 - Real.cos Δ) * t 1) / D]

/-- The pole fixes the actual affine circuit, including its translation. -/
theorem circuitPole_fixed (k : Fin (MechanismN A B + 1))
    (hΔ : intrinsicDelta A B (hh := hh) ≠ 0) :
    fullCircuit A B hh k (circuitPole A B hh k hΔ) =
      circuitPole A B hh k hΔ := by
  have hD := circuitDenom_ne_zero A B hh hΔ
  change (1 - Real.cos (intrinsicDelta A B (hh := hh))) ^ 2 +
      Real.sin (intrinsicDelta A B (hh := hh)) ^ 2 ≠ 0 at hD
  have ht := Real.sin_sq_add_cos_sq (intrinsicDelta A B (hh := hh))
  rw [fullCircuit_apply]
  ext i
  fin_cases i
  · simp [circuitPole, circuitDenom, planeRotation, planeRotationLinear]
    field_simp [hD]
    ring_nf
  · simp [circuitPole, circuitDenom, planeRotation, planeRotationLinear]
    field_simp [hD]
    ring_nf

/-- Displacement under the circuit is purely rotational around its genuine
pole. -/
theorem fullCircuit_sub_eq_rotation_sub (k : Fin (MechanismN A B + 1))
    (hΔ : intrinsicDelta A B (hh := hh) ≠ 0) (x : Plane) :
    fullCircuit A B hh k x - x =
      planeRotation (intrinsicDelta A B (hh := hh))
          (x - circuitPole A B hh k hΔ) -
        (x - circuitPole A B hh k hΔ) := by
  have hp := circuitPole_fixed A B hh k hΔ
  rw [fullCircuit_apply] at hp ⊢
  have ht : directTranslation A B hh k (MechanismN A B + 1) =
      circuitPole A B hh k hΔ -
        planeRotation (intrinsicDelta A B (hh := hh))
          (circuitPole A B hh k hΔ) := by
    calc
      _ = (planeRotation (intrinsicDelta A B (hh := hh))
            (circuitPole A B hh k hΔ) +
          directTranslation A B hh k (MechanismN A B + 1)) -
            planeRotation (intrinsicDelta A B (hh := hh))
              (circuitPole A B hh k hΔ) := by abel
      _ = _ := by rw [hp]
  rw [ht, map_sub]
  abel

lemma planeRotation_fixed_eq_zero
    (hΔ : intrinsicDelta A B (hh := hh) ≠ 0) {z : Plane}
    (hz : planeRotation (intrinsicDelta A B (hh := hh)) z = z) : z = 0 := by
  have hD := circuitDenom_ne_zero A B hh hΔ
  change (1 - Real.cos (intrinsicDelta A B (hh := hh))) ^ 2 +
      Real.sin (intrinsicDelta A B (hh := hh)) ^ 2 ≠ 0 at hD
  have h0 := congrArg (fun x : Plane => x 0) hz
  have h1 := congrArg (fun x : Plane => x 1) hz
  simp [planeRotation, planeRotationLinear] at h0 h1
  have hx : ((1 - Real.cos (intrinsicDelta A B (hh := hh))) ^ 2 +
      Real.sin (intrinsicDelta A B (hh := hh)) ^ 2) * z 0 = 0 := by
    linear_combination
      -(1 - Real.cos (intrinsicDelta A B (hh := hh))) * h0 +
        Real.sin (intrinsicDelta A B (hh := hh)) * h1
  have hy : ((1 - Real.cos (intrinsicDelta A B (hh := hh))) ^ 2 +
      Real.sin (intrinsicDelta A B (hh := hh)) ^ 2) * z 1 = 0 := by
    linear_combination
      -Real.sin (intrinsicDelta A B (hh := hh)) * h0 -
        (1 - Real.cos (intrinsicDelta A B (hh := hh))) * h1
  ext i
  fin_cases i
  · exact (mul_eq_zero.mp hx).resolve_left hD
  · exact (mul_eq_zero.mp hy).resolve_left hD

/-- The nonzero-defect affine circuit has exactly one pole. -/
theorem circuitPole_unique (k : Fin (MechanismN A B + 1))
    (hΔ : intrinsicDelta A B (hh := hh) ≠ 0) {x : Plane}
    (hx : fullCircuit A B hh k x = x) :
    x = circuitPole A B hh k hΔ := by
  have hd := fullCircuit_sub_eq_rotation_sub A B hh k hΔ x
  rw [hx, sub_self] at hd
  have hfix : planeRotation (intrinsicDelta A B (hh := hh))
      (x - circuitPole A B hh k hΔ) =
      x - circuitPole A B hh k hΔ := by
    rw [← sub_eq_zero]
    exact hd.symm
  have hz := planeRotation_fixed_eq_zero A B hh hΔ hfix
  exact sub_eq_zero.mp hz

/-- Exact projection-to-radial-support identity for the genuine affine circuit. -/
theorem circuit_projection_eq_support (k : Fin (MechanismN A B + 1))
    (hΔ : intrinsicDelta A B (hh := hh) ≠ 0) (Y v : Plane) :
    inner ℝ
        (planeRotation (intrinsicDelta A B (hh := hh) / 2) v)
        (fullCircuit A B hh k Y - Y) =
      2 * Real.sin (intrinsicDelta A B (hh := hh) / 2) *
        MixedTurnSafeCut.det
          (Y - circuitPole A B hh k hΔ) v := by
  rw [fullCircuit_sub_eq_rotation_sub A B hh k hΔ]
  rw [planeRotation_sub_identity]
  rw [inner_smul_right]
  have hi := (planeRotation (intrinsicDelta A B (hh := hh) / 2)).inner_map_map
    v (planeRotation (Real.pi / 2) (Y - circuitPole A B hh k hΔ))
  rw [hi, inner_quarterTurn_eq_det]

lemma lower_support_neg_of_upper_support_neg
    {O L U v : Plane}
    (horient : MixedTurnSafeCut.det v (U - L) < 0)
    (hupper : MixedTurnSafeCut.det (U - O) v < 0) :
    MixedTurnSafeCut.det (L - O) v < 0 := by
  simp [MixedTurnSafeCut.det] at horient hupper ⊢
  nlinarith

lemma upper_support_pos_of_lower_support_pos
    {O L U v : Plane}
    (horient : MixedTurnSafeCut.det v (U - L) < 0)
    (hlower : 0 < MixedTurnSafeCut.det (L - O) v) :
    0 < MixedTurnSafeCut.det (U - O) v := by
  simp [MixedTurnSafeCut.det] at horient hlower ⊢
  nlinarith

lemma sin_half_neg_of_delta_neg
    (hΔ : intrinsicDelta A B (hh := hh) < 0) :
    Real.sin (intrinsicDelta A B (hh := hh) / 2) < 0 := by
  apply Real.sin_neg_of_neg_of_neg_pi_lt
  · linarith
  · have habs := abs_intrinsicDelta_lt_two_pi A B hh
    have hlo := (abs_lt.mp habs).1
    linarith

lemma sin_half_pos_of_delta_pos
    (hΔ : 0 < intrinsicDelta A B (hh := hh)) :
    0 < Real.sin (intrinsicDelta A B (hh := hh) / 2) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith
  · have habs := abs_intrinsicDelta_lt_two_pi A B hh
    have hhi := (abs_lt.mp habs).2
    linarith

/-- Positive circuit projection gives negative radial support in the negative
real-defect branch. -/
theorem radialSupport_neg_of_projection_pos
    (k : Fin (MechanismN A B + 1))
    (hΔ : intrinsicDelta A B (hh := hh) < 0) (Y v : Plane)
    (hproj : 0 < inner ℝ
      (planeRotation (intrinsicDelta A B (hh := hh) / 2) v)
      (fullCircuit A B hh k Y - Y)) :
    MixedTurnSafeCut.det
      (Y - circuitPole A B hh k (ne_of_lt hΔ)) v < 0 := by
  rw [circuit_projection_eq_support A B hh k (ne_of_lt hΔ)] at hproj
  have hs := sin_half_neg_of_delta_neg A B hh hΔ
  rcases (mul_pos_iff.mp hproj) with hbad | hgood
  · nlinarith [hbad.1]
  · exact hgood.2

/-- Upper-rim folded projection simultaneously supplies both RF inequalities
at every actual cyclic root in the negative-defect branch. -/
theorem physical_negative_RF_of_upper_projections
    (hΔ : intrinsicDelta A B (hh := hh) < 0)
    (hproj : ∀ k : Fin (MechanismN A B + 1),
      0 < inner ℝ
        (planeRotation (intrinsicDelta A B (hh := hh) / 2)
          (developedForward A B hh k 0))
        (fullCircuit A B hh k (developedUpper A B hh k 0) -
          developedUpper A B hh k 0)) :
    ∀ k : Fin (MechanismN A B + 1),
      MixedTurnSafeCut.det
          (developedUpper A B hh k 0 -
            circuitPole A B hh k (ne_of_lt hΔ))
          (developedForward A B hh k 0) < 0 ∧
        MixedTurnSafeCut.det
          (developedLower A B hh k 0 -
            circuitPole A B hh k (ne_of_lt hΔ))
          (developedForward A B hh k 0) < 0 := by
  intro k
  have hu := radialSupport_neg_of_projection_pos A B hh k hΔ
    (developedUpper A B hh k 0) (developedForward A B hh k 0) (hproj k)
  refine ⟨hu, ?_⟩
  exact lower_support_neg_of_upper_support_neg
    (developed_hinge_orientation_neg A B hh k 0) hu

/-- Premise-free physical RF package for every root in the negative-defect
branch, obtained from the actual upper polygonal closure. -/
theorem physical_negative_RF
    (hΔ : intrinsicDelta A B (hh := hh) < 0) :
    ∀ k : Fin (MechanismN A B + 1),
      MixedTurnSafeCut.det
          (developedUpper A B hh k 0 -
            circuitPole A B hh k (ne_of_lt hΔ))
          (developedForward A B hh k 0) < 0 ∧
        MixedTurnSafeCut.det
          (developedLower A B hh k 0 -
            circuitPole A B hh k (ne_of_lt hΔ))
          (developedForward A B hh k 0) < 0 :=
  physical_negative_RF_of_upper_projections A B hh hΔ
    (upper_circuit_projection_pos A B hh)

/-- Positive circuit projection gives positive radial support in the positive
real-defect branch. -/
theorem radialSupport_pos_of_projection_pos
    (k : Fin (MechanismN A B + 1))
    (hΔ : 0 < intrinsicDelta A B (hh := hh)) (Y v : Plane)
    (hproj : 0 < inner ℝ
      (planeRotation (intrinsicDelta A B (hh := hh) / 2) v)
      (fullCircuit A B hh k Y - Y)) :
    0 < MixedTurnSafeCut.det
      (Y - circuitPole A B hh k (ne_of_gt hΔ)) v := by
  rw [circuit_projection_eq_support A B hh k (ne_of_gt hΔ)] at hproj
  have hs := sin_half_pos_of_delta_pos A B hh hΔ
  rcases (mul_pos_iff.mp hproj) with hgood | hbad
  · exact hgood.2
  · nlinarith [hbad.1]

/-- Lower-rim folded projection simultaneously supplies both positive RF
inequalities at every actual cyclic root.  `reflectSwap` in
`RadialExtremalSafety` converts these to the common negative convention. -/
theorem physical_positive_RF_of_lower_projections
    (hΔ : 0 < intrinsicDelta A B (hh := hh))
    (hproj : ∀ k : Fin (MechanismN A B + 1),
      0 < inner ℝ
        (planeRotation (intrinsicDelta A B (hh := hh) / 2)
          (developedForward A B hh k 0))
        (fullCircuit A B hh k (developedLower A B hh k 0) -
          developedLower A B hh k 0)) :
    ∀ k : Fin (MechanismN A B + 1),
      0 < MixedTurnSafeCut.det
          (developedLower A B hh k 0 -
            circuitPole A B hh k (ne_of_gt hΔ))
          (developedForward A B hh k 0) ∧
        0 < MixedTurnSafeCut.det
          (developedUpper A B hh k 0 -
            circuitPole A B hh k (ne_of_gt hΔ))
          (developedForward A B hh k 0) := by
  intro k
  have hl := radialSupport_pos_of_projection_pos A B hh k hΔ
    (developedLower A B hh k 0) (developedForward A B hh k 0) (hproj k)
  refine ⟨hl, ?_⟩
  exact upper_support_pos_of_lower_support_pos
    (developed_hinge_orientation_neg A B hh k 0) hl

/-- Premise-free physical RF package for every root in the positive-defect
branch, obtained from the actual lower polygonal closure. -/
theorem physical_positive_RF
    (hΔ : 0 < intrinsicDelta A B (hh := hh)) :
    ∀ k : Fin (MechanismN A B + 1),
      0 < MixedTurnSafeCut.det
          (developedLower A B hh k 0 -
            circuitPole A B hh k (ne_of_gt hΔ))
          (developedForward A B hh k 0) ∧
        0 < MixedTurnSafeCut.det
          (developedUpper A B hh k 0 -
            circuitPole A B hh k (ne_of_gt hΔ))
          (developedForward A B hh k 0) :=
  physical_positive_RF_of_lower_projections A B hh hΔ
    (lower_circuit_projection_pos A B hh)

end Raw
end
end PhysicalMixedTurnSource
