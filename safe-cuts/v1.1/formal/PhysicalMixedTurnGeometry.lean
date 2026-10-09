import PhysicalMixedTurnEndpointTransport

/-!
Physical facet and unfolding layer for the intrinsic T-mixed source bridge.
-/

open Set
open scoped BigOperators Classical NNReal
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CommonSupportMerge OriginalFacetCertificates NormalFanSplice MaximalSupportCells
open CyclicCutOrders EuclideanPrismatoidCoordinates PolyhedralInputBridge
open TrimmedFacetWitnesses BandGeometryAssembly FiniteWitnessClosure
open CutSurfaceQuotient MixedTurnSafeCut PolygonSetReconstruction ConvexPolygonTurning
open SingleCutRecovery NestedBandExternalApplication

namespace PhysicalMixedTurnSource
noncomputable section
set_option maxHeartbeats 2000000

/-- Counterclockwise Euclidean rotation in the developed plane. -/
def planeRotationLinear (θ : ℝ) : Plane →ₗ[ℝ] Plane where
  toFun z := WithLp.toLp 2 ![
    Real.cos θ * z 0 - Real.sin θ * z 1,
    Real.sin θ * z 0 + Real.cos θ * z 1]
  map_add' := by
    intro x y
    ext k
    fin_cases k <;> simp <;> ring
  map_smul' := by
    intro r x
    ext k
    fin_cases k <;> simp <;> ring

noncomputable def planeRotation (θ : ℝ) : Plane →ₗᵢ[ℝ] Plane :=
  (planeRotationLinear θ).isometryOfInner (by
    intro x y
    simp [planeRotationLinear, inner, Fin.sum_univ_two]
    have hs := Real.sin_sq_add_cos_sq θ
    linear_combination (y 0 * x 0 + y 1 * x 1) * hs)

@[simp] lemma planeRotation_apply_zero (θ : ℝ) : planeRotation θ 0 = 0 := map_zero _

lemma planeRotation_direction (θ φ : ℝ) :
    planeRotation θ (direction φ) = direction (θ + φ) := by
  ext k
  fin_cases k
  · simp [planeRotation, planeRotationLinear, direction, Real.cos_add]
  · simp [planeRotation, planeRotationLinear, direction, Real.sin_add]

lemma planeRotation_add (θ : ℝ) (x y : Plane) :
    planeRotation θ (x + y) = planeRotation θ x + planeRotation θ y := map_add _ _ _

lemma planeRotation_comp (θ φ : ℝ) (x : Plane) :
    planeRotation θ (planeRotation φ x) = planeRotation (θ + φ) x := by
  ext k
  fin_cases k <;>
    simp [planeRotation, planeRotationLinear, Real.cos_add, Real.sin_add] <;> ring

lemma planeRotation_det (θ : ℝ) (x y : Plane) :
    MixedTurnSafeCut.det (planeRotation θ x) (planeRotation θ y) =
      MixedTurnSafeCut.det x y := by
  simp [planeRotation, planeRotationLinear, MixedTurnSafeCut.det]
  have hs := Real.sin_sq_add_cos_sq θ
  linear_combination (x 0 * y 1 - x 1 * y 0) * hs

section Raw
variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

/-- The selected source entry edge has exactly the canonical physical endpoints. -/
theorem selectedEntryEdge_lower_eq (i : SourceIndex A B) :
    let ed : OriginalEdge
      (certificate A B hh (cycle A B (prev i)))
      (certificate A B hh
        (cycle A B (finRotate (sideCount A B) (prev i)))) := entryEdge A B hh i
    (certificate A B hh (cycle A B (prev i))).chart ed.aL = lowerEndpoint A B hh i := by
  exact (selectedEntryEdge_endpoints_eq A B hh i).1

/-- The selected source entry edge has exactly the canonical physical endpoints. -/
theorem selectedEntryEdge_upper_eq (i : SourceIndex A B) :
    let ed : OriginalEdge
      (certificate A B hh (cycle A B (prev i)))
      (certificate A B hh
        (cycle A B (finRotate (sideCount A B) (prev i)))) := entryEdge A B hh i
    (certificate A B hh (cycle A B (prev i))).chart ed.bL = upperEndpoint A B hh i := by
  exact (selectedEntryEdge_endpoints_eq A B hh i).2

lemma face_inner_smul_right (_hh : 0 < h) (i : SourceIndex A B)
    (x y : FaceSpace A B h (cycle A B i)) (r : ℝ) :
    inner ℝ x (r • y) = r * inner ℝ x y := by
  change inner ℝ (x : PhysicalAmbient) (r • (y : PhysicalAmbient)) =
    r * inner ℝ (x : PhysicalAmbient) (y : PhysicalAmbient)
  exact real_inner_smul_right _ _ _

lemma face_inner_smul_left (_hh : 0 < h) (i : SourceIndex A B)
    (x y : FaceSpace A B h (cycle A B i)) (r : ℝ) :
    inner ℝ (r • x) y = r * inner ℝ x y := by
  rw [real_inner_comm, face_inner_smul_right A B _hh i, real_inner_comm]

@[simp] lemma faceUnit_inner_self (i : SourceIndex A B) :
    inner ℝ (faceUnit A B hh i) (faceUnit A B hh i) = 1 := by
  rw [real_inner_self_eq_norm_sq, faceUnit_norm]
  norm_num

@[simp] lemma faceTransverse_inner_self (i : SourceIndex A B) :
    inner ℝ (faceTransverse A B hh i) (faceTransverse A B hh i) = 1 := by
  rw [real_inner_self_eq_norm_sq, faceTransverse_norm]
  norm_num

@[simp] lemma faceTransverse_unit_inner (i : SourceIndex A B) :
    inner ℝ (faceTransverse A B hh i) (faceUnit A B hh i) = 0 := by
  rw [real_inner_comm]
  exact faceUnit_transverse_orthogonal A B hh i

@[simp] lemma faceUnit_transverse_inner (i : SourceIndex A B) :
    inner ℝ (faceUnit A B hh i) (faceTransverse A B hh i) = 0 := by
  rw [real_inner_comm, faceTransverse_unit_inner]

@[simp] lemma faceUnit_hinge_inner (i : SourceIndex A B) :
    inner ℝ (faceUnit A B hh i) (faceHingeVector A B hh i) = faceC A B hh i := rfl

@[simp] lemma faceTransverse_hinge_inner (i : SourceIndex A B) :
    inner ℝ (faceTransverse A B hh i) (faceHingeVector A B hh i) = faceS A B hh i := by
  calc
    _ = inner ℝ (faceTransverse A B hh i)
        (faceC A B hh i • faceUnit A B hh i +
          faceS A B hh i • faceTransverse A B hh i) := by
      rw [← faceHingeVector_decompose A B hh i]
    _ = inner ℝ (faceTransverse A B hh i) (faceC A B hh i • faceUnit A B hh i) +
        inner ℝ (faceTransverse A B hh i)
          (faceS A B hh i • faceTransverse A B hh i) := inner_add_right _ _ _
    _ = faceC A B hh i * inner ℝ (faceTransverse A B hh i) (faceUnit A B hh i) +
        faceS A B hh i * inner ℝ (faceTransverse A B hh i)
          (faceTransverse A B hh i) := by
      rw [face_inner_smul_right A B hh i, face_inner_smul_right A B hh i]
    _ = faceS A B hh i := by rw [faceTransverse_unit_inner, faceTransverse_inner_self]; ring

@[simp] theorem intrinsicFaceChart_exitMidpoint (i : SourceIndex A B) :
    intrinsicFaceChart A B hh i (faceExitMidpoint A B hh i) =
      WithLp.toLp 2 ![middleLength A B hh i, 0] := by
  rw [intrinsicFaceChart_apply]
  have hs : faceExitMidpoint A B hh i - faceEntryMidpoint A B hh i =
      faceMiddleStep A B hh i := rfl
  rw [hs, faceMiddleStep_decompose, map_smul]
  ext k
  fin_cases k
  · change middleLength A B hh i *
      ((faceBasis A B hh i).repr (faceUnit A B hh i)) 0 = middleLength A B hh i
    rw [(faceBasis A B hh i).repr_apply_apply, faceBasis_zero,
      real_inner_self_eq_norm_sq, faceUnit_norm]
    ring
  · change middleLength A B hh i *
      ((faceBasis A B hh i).repr (faceUnit A B hh i)) 1 = 0
    rw [(faceBasis A B hh i).repr_apply_apply, faceBasis_one]
    have hvu : inner ℝ (faceTransverse A B hh i) (faceUnit A B hh i) = 0 := by
      rw [real_inner_comm]
      exact faceUnit_transverse_orthogonal A B hh i
    simp [hvu]

@[simp] theorem intrinsicFaceChart_entryUpper (i : SourceIndex A B) :
    intrinsicFaceChart A B hh i (faceEntryUpper A B hh i) =
      WithLp.toLp 2 ![(1/2 : ℝ) * faceC A B hh i,
        -(1/2 : ℝ) * faceS A B hh i] := by
  rw [intrinsicFaceChart_apply, faceEntryUpper_sub_midpoint]
  ext k
  fin_cases k
  · change ((faceBasis A B hh i).repr
      ((1 / 2 : ℝ) • faceHingeVector A B hh i)) 0 =
        (1 / 2 : ℝ) * faceC A B hh i
    rw [(faceBasis A B hh i).repr_apply_apply, faceBasis_zero]
    calc
      inner ℝ (faceUnit A B hh i) ((1 / 2 : ℝ) • faceHingeVector A B hh i) =
          (1 / 2 : ℝ) * inner ℝ (faceUnit A B hh i) (faceHingeVector A B hh i) :=
        face_inner_smul_right A B hh i _ _ _
      _ = _ := by rw [faceUnit_hinge_inner]
  · change ((faceBasis A B hh i).repr
      ((1 / 2 : ℝ) • faceHingeVector A B hh i)) 1 =
        -(1 / 2 : ℝ) * faceS A B hh i
    rw [(faceBasis A B hh i).repr_apply_apply, faceBasis_one]
    calc
      inner ℝ (-faceTransverse A B hh i) ((1 / 2 : ℝ) • faceHingeVector A B hh i) =
          (1 / 2 : ℝ) * inner ℝ (-faceTransverse A B hh i)
            (faceHingeVector A B hh i) := face_inner_smul_right A B hh i _ _ _
      _ = (1 / 2 : ℝ) * -faceS A B hh i := by rw [inner_neg_left, faceTransverse_hinge_inner]
      _ = _ := by ring

@[simp] theorem intrinsicFaceChart_entryLower (i : SourceIndex A B) :
    intrinsicFaceChart A B hh i (faceEntryLower A B hh i) =
      WithLp.toLp 2 ![-(1/2 : ℝ) * faceC A B hh i,
        (1/2 : ℝ) * faceS A B hh i] := by
  rw [intrinsicFaceChart_apply, faceEntryLower_sub_midpoint]
  ext k
  fin_cases k
  · change ((faceBasis A B hh i).repr
      (-(1 / 2 : ℝ) • faceHingeVector A B hh i)) 0 =
        -(1 / 2 : ℝ) * faceC A B hh i
    rw [(faceBasis A B hh i).repr_apply_apply, faceBasis_zero]
    calc
      inner ℝ (faceUnit A B hh i) (-(1 / 2 : ℝ) • faceHingeVector A B hh i) =
          -(1 / 2 : ℝ) * inner ℝ (faceUnit A B hh i) (faceHingeVector A B hh i) :=
        face_inner_smul_right A B hh i _ _ _
      _ = _ := by rw [faceUnit_hinge_inner]
  · change ((faceBasis A B hh i).repr
      (-(1 / 2 : ℝ) • faceHingeVector A B hh i)) 1 =
        (1 / 2 : ℝ) * faceS A B hh i
    rw [(faceBasis A B hh i).repr_apply_apply, faceBasis_one]
    calc
      inner ℝ (-faceTransverse A B hh i) (-(1 / 2 : ℝ) • faceHingeVector A B hh i) =
          -(1 / 2 : ℝ) * inner ℝ (-faceTransverse A B hh i)
            (faceHingeVector A B hh i) := face_inner_smul_right A B hh i _ _ _
      _ = -(1 / 2 : ℝ) * -faceS A B hh i := by rw [inner_neg_left, faceTransverse_hinge_inner]
      _ = _ := by ring

noncomputable def faceExitHingeVector (i : SourceIndex A B) :
    FaceSpace A B h (cycle A B i) := faceExitUpper A B hh i - faceExitLower A B hh i

lemma chartLinear_faceExitHingeVector (i : SourceIndex A B) :
    (certificate A B hh (cycle A B i)).chart.linearIsometry
      (faceExitHingeVector A B hh i) = hingeVector A B hh (next i) := by
  rw [faceExitHingeVector]
  calc
    _ = (certificate A B hh (cycle A B i)).chart (faceExitUpper A B hh i) -
        (certificate A B hh (cycle A B i)).chart (faceExitLower A B hh i) :=
      (certificate A B hh (cycle A B i)).chart.map_vsub _ _
    _ = _ := by rw [chart_faceExitUpper, chart_faceExitLower, hingeVector]

lemma faceExitHingeVector_ne_zero (i : SourceIndex A B) :
    faceExitHingeVector A B hh i ≠ 0 := by
  intro hz
  have hm := congrArg
    (certificate A B hh (cycle A B i)).chart.linearIsometry hz
  rw [map_zero, chartLinear_faceExitHingeVector] at hm
  exact hingeVector_ne_zero A B hh (next i) hm

noncomputable def faceLowerRun (i : SourceIndex A B) : FaceSpace A B h (cycle A B i) :=
  faceExitLower A B hh i - faceEntryLower A B hh i

noncomputable def faceUpperRun (i : SourceIndex A B) : FaceSpace A B h (cycle A B i) :=
  faceExitUpper A B hh i - faceEntryUpper A B hh i

def lowerRunCoeff (i : SourceIndex A B) : ℝ :=
  inner ℝ (faceUnit A B hh i) (faceLowerRun A B hh i)

def upperRunCoeff (i : SourceIndex A B) : ℝ :=
  inner ℝ (faceUnit A B hh i) (faceUpperRun A B hh i)

lemma faceLowerRun_add_faceUpperRun (i : SourceIndex A B) :
    faceLowerRun A B hh i + faceUpperRun A B hh i =
      (2 : ℝ) • faceMiddleStep A B hh i := by
  rw [faceLowerRun, faceUpperRun, faceMiddleStep, faceEntryMidpoint, faceExitMidpoint,
    AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
  module

lemma chartLinear_faceLowerRun_height (i : SourceIndex A B) :
    heightLinear h ((certificate A B hh (cycle A B i)).chart.linearIsometry
      (faceLowerRun A B hh i)) = 0 := by
  rw [faceLowerRun]
  calc
    _ = heightLinear h
        ((certificate A B hh (cycle A B i)).chart (faceExitLower A B hh i) -
          (certificate A B hh (cycle A B i)).chart (faceEntryLower A B hh i)) := by
      congr 1
      exact (certificate A B hh (cycle A B i)).chart.map_vsub _ _
    _ = heightLinear h (lowerEndpoint A B hh (next i) - lowerEndpoint A B hh i) := by
      rw [chart_faceExitLower, chart_faceEntryLower]
    _ = 0 := by rw [map_sub, lowerEndpoint_height, lowerEndpoint_height]; ring

lemma chartLinear_faceUpperRun_height (i : SourceIndex A B) :
    heightLinear h ((certificate A B hh (cycle A B i)).chart.linearIsometry
      (faceUpperRun A B hh i)) = 0 := by
  rw [faceUpperRun]
  calc
    _ = heightLinear h
        ((certificate A B hh (cycle A B i)).chart (faceExitUpper A B hh i) -
          (certificate A B hh (cycle A B i)).chart (faceEntryUpper A B hh i)) := by
      congr 1
      exact (certificate A B hh (cycle A B i)).chart.map_vsub _ _
    _ = heightLinear h (upperEndpoint A B hh (next i) - upperEndpoint A B hh i) := by
      rw [chart_faceExitUpper, chart_faceEntryUpper]
    _ = 0 := by rw [map_sub, upperEndpoint_height, upperEndpoint_height]; ring

lemma chartLinear_faceResidual_height (i : SourceIndex A B) :
    heightLinear h ((certificate A B hh (cycle A B i)).chart.linearIsometry
      (faceResidual A B hh i)) = 1 := by
  rw [faceResidual, map_sub, map_smul, chartLinear_faceHingeVector,
    chartLinear_faceUnit, map_sub, map_smul, hingeVector_height,
    middleDirection_height]
  ring

lemma chartLinear_faceUnit_height (i : SourceIndex A B) :
    heightLinear h ((certificate A B hh (cycle A B i)).chart.linearIsometry
      (faceUnit A B hh i)) = 0 := by
  rw [chartLinear_faceUnit, middleDirection_height]

lemma chartLinear_faceTransverse_height (i : SourceIndex A B) :
    heightLinear h ((certificate A B hh (cycle A B i)).chart.linearIsometry
      (faceTransverse A B hh i)) = ‖faceResidual A B hh i‖⁻¹ := by
  rw [faceTransverse, NormedSpace.normalize, map_smul, map_smul,
    chartLinear_faceResidual_height]
  ring

def lowerPlanarRun (i : SourceIndex A B) : Plane :=
  B.vertex (gapB A B (entryGap A B (next i))) -
    B.vertex (gapB A B (entryGap A B i))

def upperPlanarRun (i : SourceIndex A B) : Plane :=
  A.vertex (entryGap A B (next i)).1 - A.vertex (entryGap A B i).1

lemma chartLinear_faceLowerRun (i : SourceIndex A B) :
    (certificate A B hh (cycle A B i)).chart.linearIsometry (faceLowerRun A B hh i) =
      horizontalIsometry (lowerPlanarRun A B i) := by
  rw [faceLowerRun]
  calc
    _ = (certificate A B hh (cycle A B i)).chart (faceExitLower A B hh i) -
        (certificate A B hh (cycle A B i)).chart (faceEntryLower A B hh i) :=
      (certificate A B hh (cycle A B i)).chart.map_vsub _ _
    _ = lowerEndpoint A B hh (next i) - lowerEndpoint A B hh i := by
      rw [chart_faceExitLower, chart_faceEntryLower]
    _ = _ := by
      ext k
      fin_cases k <;>
        simp [lowerEndpoint, lowerPlanarRun, horizontalIsometry, horizontalLinear,
          pack, lowerLift]

lemma chartLinear_faceUpperRun (i : SourceIndex A B) :
    (certificate A B hh (cycle A B i)).chart.linearIsometry (faceUpperRun A B hh i) =
      horizontalIsometry (upperPlanarRun A B i) := by
  rw [faceUpperRun]
  calc
    _ = (certificate A B hh (cycle A B i)).chart (faceExitUpper A B hh i) -
        (certificate A B hh (cycle A B i)).chart (faceEntryUpper A B hh i) :=
      (certificate A B hh (cycle A B i)).chart.map_vsub _ _
    _ = upperEndpoint A B hh (next i) - upperEndpoint A B hh i := by
      rw [chart_faceExitUpper, chart_faceEntryUpper]
    _ = _ := by
      ext k
      fin_cases k <;>
        simp [upperEndpoint, upperPlanarRun, horizontalIsometry, horizontalLinear,
          pack, upperLift]

lemma nextNormal_middleEdge_pos (i : SourceIndex A B) :
    0 < inner ℝ (cycle A B (next i)).val
      (edgeVector (middlePolygon A B).vertex i) := by
  have hle := section_support_le A B (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)
    (cycle A B (next i)).val (middleVertex_mem_section A B i)
  have htight := middleVertex_exit_tight A B (next i)
  have hne : inner ℝ (cycle A B (next i)).val (middleVertex A B i) ≠
      rowBound A B (1 / 2 : ℝ) (cycle A B (next i)).val := by
    intro he
    rcases (middleVertex_tight_iff A B (next i) i).mp he with hbad | hbad
    · exact (next_ne (by have := three_le_sideCount A B; omega) i) hbad.symm
    · exact (self_ne_next_next (three_le_sideCount A B) i) hbad
  have hlt : inner ℝ (cycle A B (next i)).val (middleVertex A B i) <
      rowBound A B (1 / 2 : ℝ) (cycle A B (next i)).val :=
    lt_of_le_of_ne hle hne
  change 0 < inner ℝ (cycle A B (next i)).val
    (middleVertex A B (next i) - middleVertex A B i)
  rw [inner_sub_right, htight]
  linarith

lemma prevNormal_middleEdge_neg (i : SourceIndex A B) :
    inner ℝ (cycle A B (prev i)).val
      (edgeVector (middlePolygon A B).vertex i) < 0 := by
  have hle := section_support_le A B (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)
    (cycle A B (prev i)).val (middleVertex_mem_section A B (next i))
  have htight := nextMiddleVertex_exit_tight A B (prev i)
  rw [next_prev] at htight
  have hne : inner ℝ (cycle A B (prev i)).val (middleVertex A B (next i)) ≠
      rowBound A B (1 / 2 : ℝ) (cycle A B (prev i)).val := by
    intro he
    rcases (middleVertex_tight_iff A B (prev i) (next i)).mp he with hbad | hbad
    · exact (prev_ne_next (three_le_sideCount A B) i) hbad.symm
    · rw [next_prev] at hbad
      exact (next_ne (by have := three_le_sideCount A B; omega) i) hbad
  have hlt : inner ℝ (cycle A B (prev i)).val (middleVertex A B (next i)) <
      rowBound A B (1 / 2 : ℝ) (cycle A B (prev i)).val :=
    lt_of_le_of_ne hle hne
  change inner ℝ (cycle A B (prev i)).val
    (middleVertex A B (next i) - middleVertex A B i) < 0
  rw [inner_sub_right, htight]
  linarith

lemma prevNormal_middleDirection_neg (i : SourceIndex A B) :
    inner ℝ (horizontalIsometry (cycle A B (prev i)).val)
      (middleDirection A B hh i) < 0 := by
  rw [middleDirection, middleLength]
  calc
    inner ℝ (horizontalIsometry (cycle A B (prev i)).val)
        (‖middleStep A B hh i‖⁻¹ • middleStep A B hh i) =
      ‖middleStep A B hh i‖⁻¹ *
        inner ℝ (horizontalIsometry (cycle A B (prev i)).val) (middleStep A B hh i) :=
      real_inner_smul_right _ _ _
    _ = ‖edgeVector (middlePolygon A B).vertex i‖⁻¹ *
        inner ℝ (cycle A B (prev i)).val (edgeVector (middlePolygon A B).vertex i) := by
      rw [middleStep_eq_horizontal, horizontalIsometry.norm_map,
        horizontalIsometry.inner_map_map]
    _ < 0 := mul_neg_of_pos_of_neg (inv_pos.mpr (norm_pos_iff.mpr
      (outgoing_ne_zero (middlePolygon A B) i))) (prevNormal_middleEdge_neg A B i)

lemma nextNormal_middleDirection_pos (i : SourceIndex A B) :
    0 < inner ℝ (horizontalIsometry (cycle A B (next i)).val)
      (middleDirection A B hh i) := by
  rw [middleDirection, middleLength]
  calc
    inner ℝ (horizontalIsometry (cycle A B (next i)).val)
        (‖middleStep A B hh i‖⁻¹ • middleStep A B hh i) =
      ‖middleStep A B hh i‖⁻¹ *
        inner ℝ (horizontalIsometry (cycle A B (next i)).val) (middleStep A B hh i) :=
      real_inner_smul_right _ _ _
    _ = ‖edgeVector (middlePolygon A B).vertex i‖⁻¹ *
        inner ℝ (cycle A B (next i)).val (edgeVector (middlePolygon A B).vertex i) := by
      rw [middleStep_eq_horizontal, horizontalIsometry.norm_map,
        horizontalIsometry.inner_map_map]
    _ > 0 := mul_pos (inv_pos.mpr (norm_pos_iff.mpr
      (outgoing_ne_zero (middlePolygon A B) i))) (nextNormal_middleEdge_pos A B i)

lemma lowerPlanarRun_nextSupport_nonneg (i : SourceIndex A B) :
    0 ≤ inner ℝ (cycle A B (next i)).val (lowerPlanarRun A B i) := by
  let q := entryGap A B (next i)
  have hq : Maximizes B (cycle A B (next i)).val (gapB A B q) :=
    ((side_supports_pair_iff A B q (cycle A B (next i))).mpr
      (Or.inr (entryGap_right A B (next i)).symm)).2
  dsimp [lowerPlanarRun, q]
  rw [inner_sub_right]
  exact sub_nonneg.mpr (hq _ (B.vertex_mem_body _))

lemma upperPlanarRun_nextSupport_nonneg (i : SourceIndex A B) :
    0 ≤ inner ℝ (cycle A B (next i)).val (upperPlanarRun A B i) := by
  let q := entryGap A B (next i)
  have hq : Maximizes A (cycle A B (next i)).val q.1 :=
    ((side_supports_pair_iff A B q (cycle A B (next i))).mpr
      (Or.inr (entryGap_right A B (next i)).symm)).1
  dsimp [upperPlanarRun, q]
  rw [inner_sub_right]
  exact sub_nonneg.mpr (hq _ (A.vertex_mem_body _))

lemma lowerRunCoeff_add_upperRunCoeff (i : SourceIndex A B) :
    lowerRunCoeff A B hh i + upperRunCoeff A B hh i =
      2 * middleLength A B hh i := by
  have he := congrArg (fun z => inner ℝ (faceUnit A B hh i) z)
    (faceLowerRun_add_faceUpperRun A B hh i)
  rw [inner_add_right, face_inner_smul_right A B hh i,
    faceMiddleStep_decompose, face_inner_smul_right A B hh i,
    faceUnit_inner_self] at he
  simpa [lowerRunCoeff, upperRunCoeff] using he

lemma eq_inner_smul_faceUnit_of_height_zero (i : SourceIndex A B)
    (x : FaceSpace A B h (cycle A B i))
    (hx : heightLinear h ((certificate A B hh (cycle A B i)).chart.linearIsometry x) = 0) :
    x = inner ℝ (faceUnit A B hh i) x • faceUnit A B hh i := by
  have hsum := (faceBasis A B hh i).sum_repr' x
  rw [Fin.sum_univ_two, faceBasis_zero, faceBasis_one] at hsum
  have hheight := congrArg
    (fun z => heightLinear h
      ((certificate A B hh (cycle A B i)).chart.linearIsometry z)) hsum
  simp only [map_add, map_smul, map_neg] at hheight
  rw [chartLinear_faceUnit_height, chartLinear_faceTransverse_height, hx] at hheight
  have hinv : ‖faceResidual A B hh i‖⁻¹ ≠ 0 :=
    inv_ne_zero (norm_ne_zero_iff.mpr (faceResidual_ne_zero A B hh i))
  have hc : inner ℝ (-faceTransverse A B hh i) x = 0 := by
    rcases mul_eq_zero.mp (by simpa only [smul_eq_mul, mul_zero, zero_add, neg_eq_zero] using hheight) with hz | hz
    · exact hz
    · exact False.elim (hinv (neg_eq_zero.mp hz))
  rw [hc, zero_smul, add_zero] at hsum
  exact hsum.symm

lemma faceLowerRun_decompose (i : SourceIndex A B) :
    faceLowerRun A B hh i = lowerRunCoeff A B hh i • faceUnit A B hh i := by
  simpa [lowerRunCoeff] using eq_inner_smul_faceUnit_of_height_zero A B hh i
    (faceLowerRun A B hh i) (chartLinear_faceLowerRun_height A B hh i)

lemma faceUpperRun_decompose (i : SourceIndex A B) :
    faceUpperRun A B hh i = upperRunCoeff A B hh i • faceUnit A B hh i := by
  simpa [upperRunCoeff] using eq_inner_smul_faceUnit_of_height_zero A B hh i
    (faceUpperRun A B hh i) (chartLinear_faceUpperRun_height A B hh i)

lemma lowerRunCoeff_nonneg (i : SourceIndex A B) : 0 ≤ lowerRunCoeff A B hh i := by
  have he := congrArg
    (certificate A B hh (cycle A B i)).chart.linearIsometry
    (faceLowerRun_decompose A B hh i)
  rw [map_smul, chartLinear_faceLowerRun, chartLinear_faceUnit] at he
  have hd := congrArg
    (fun z => inner ℝ (horizontalIsometry (cycle A B (next i)).val) z) he
  rw [inner_smul_right] at hd
  have hl : 0 ≤ inner ℝ (horizontalIsometry (cycle A B (next i)).val)
      (horizontalIsometry (lowerPlanarRun A B i)) := by
    rw [horizontalIsometry.inner_map_map]
    exact lowerPlanarRun_nextSupport_nonneg A B i
  have hp := nextNormal_middleDirection_pos A B hh i
  nlinarith

lemma upperRunCoeff_nonneg (i : SourceIndex A B) : 0 ≤ upperRunCoeff A B hh i := by
  have he := congrArg
    (certificate A B hh (cycle A B i)).chart.linearIsometry
    (faceUpperRun_decompose A B hh i)
  rw [map_smul, chartLinear_faceUpperRun, chartLinear_faceUnit] at he
  have hd := congrArg
    (fun z => inner ℝ (horizontalIsometry (cycle A B (next i)).val) z) he
  rw [inner_smul_right] at hd
  have hl : 0 ≤ inner ℝ (horizontalIsometry (cycle A B (next i)).val)
      (horizontalIsometry (upperPlanarRun A B i)) := by
    rw [horizontalIsometry.inner_map_map]
    exact upperPlanarRun_nextSupport_nonneg A B i
  have hp := nextNormal_middleDirection_pos A B hh i
  nlinarith

lemma lowerRunCoeff_add_upperRunCoeff_pos (i : SourceIndex A B) :
    0 < lowerRunCoeff A B hh i + upperRunCoeff A B hh i := by
  rw [lowerRunCoeff_add_upperRunCoeff]
  exact mul_pos (by norm_num) (middleLength_pos A B hh i)

noncomputable def faceEntryAt (t : ℝ) (i : SourceIndex A B) :
    FaceSpace A B h (cycle A B i) :=
  AffineMap.lineMap (faceEntryLower A B hh i) (faceEntryUpper A B hh i) t

noncomputable def faceExitAt (t : ℝ) (i : SourceIndex A B) :
    FaceSpace A B h (cycle A B i) :=
  AffineMap.lineMap (faceExitLower A B hh i) (faceExitUpper A B hh i) t

noncomputable def faceRunAt (t : ℝ) (i : SourceIndex A B) :
    FaceSpace A B h (cycle A B i) := faceExitAt A B hh t i - faceEntryAt A B hh t i

@[simp] lemma intrinsicFaceChart_entryAt (t : ℝ) (i : SourceIndex A B) :
    intrinsicFaceChart A B hh i (faceEntryAt A B hh t i) =
      WithLp.toLp 2 ![(t - (1/2 : ℝ)) * faceC A B hh i,
        -(t - (1/2 : ℝ)) * faceS A B hh i] := by
  rw [faceEntryAt]
  change (intrinsicFaceChart A B hh i).toAffineEquiv.toAffineMap
      (AffineMap.lineMap (faceEntryLower A B hh i) (faceEntryUpper A B hh i) t) = _
  rw [(intrinsicFaceChart A B hh i).toAffineEquiv.toAffineMap.apply_lineMap]
  change AffineMap.lineMap
      (intrinsicFaceChart A B hh i (faceEntryLower A B hh i))
      (intrinsicFaceChart A B hh i (faceEntryUpper A B hh i)) t = _
  rw [intrinsicFaceChart_entryLower, intrinsicFaceChart_entryUpper]
  ext k
  fin_cases k <;> simp [AffineMap.lineMap_apply_module] <;> ring

lemma intrinsicFaceChart_linear_faceUnit (i : SourceIndex A B) :
    (intrinsicFaceChart A B hh i).linearIsometryEquiv (faceUnit A B hh i) =
      WithLp.toLp 2 ![1, 0] := by
  change (faceBasis A B hh i).repr (faceUnit A B hh i) = _
  ext k
  fin_cases k
  · change ((faceBasis A B hh i).repr (faceUnit A B hh i)) 0 = 1
    rw [(faceBasis A B hh i).repr_apply_apply, faceBasis_zero, faceUnit_inner_self]
  · change ((faceBasis A B hh i).repr (faceUnit A B hh i)) 1 = 0
    rw [(faceBasis A B hh i).repr_apply_apply, faceBasis_one]
    rw [inner_neg_left, faceTransverse_unit_inner]
    ring

lemma faceRunAt_eq_runs (t : ℝ) (i : SourceIndex A B) :
    faceRunAt A B hh t i = (1 - t) • faceLowerRun A B hh i + t • faceUpperRun A B hh i := by
  rw [faceRunAt, faceEntryAt, faceExitAt, faceLowerRun, faceUpperRun,
    AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
  module

def retainedLowerRunCoeff (d : ℝ) (i : SourceIndex A B) : ℝ :=
  (1 - d) * lowerRunCoeff A B hh i + d * upperRunCoeff A B hh i

def retainedUpperRunCoeff (d : ℝ) (i : SourceIndex A B) : ℝ :=
  d * lowerRunCoeff A B hh i + (1 - d) * upperRunCoeff A B hh i

lemma faceRunAt_decompose (t : ℝ) (i : SourceIndex A B) :
    faceRunAt A B hh t i = retainedLowerRunCoeff A B hh t i • faceUnit A B hh i := by
  rw [faceRunAt_eq_runs, faceLowerRun_decompose, faceUpperRun_decompose,
    retainedLowerRunCoeff]
  module

@[simp] lemma intrinsicFaceChart_exitAt (t : ℝ) (i : SourceIndex A B) :
    intrinsicFaceChart A B hh i (faceExitAt A B hh t i) =
      WithLp.toLp 2 ![(t - (1/2 : ℝ)) * faceC A B hh i +
          retainedLowerRunCoeff A B hh t i,
        -(t - (1/2 : ℝ)) * faceS A B hh i] := by
  have hv : faceRunAt A B hh t i + faceEntryAt A B hh t i = faceExitAt A B hh t i := by
    rw [faceRunAt]
    abel
  calc
    _ = intrinsicFaceChart A B hh i
        (faceRunAt A B hh t i + faceEntryAt A B hh t i) := by rw [hv]
    _ = (intrinsicFaceChart A B hh i).linearIsometryEquiv (faceRunAt A B hh t i) +
        intrinsicFaceChart A B hh i (faceEntryAt A B hh t i) := by
      simpa only [vadd_eq_add] using
        (intrinsicFaceChart A B hh i).map_vadd
          (faceEntryAt A B hh t i) (faceRunAt A B hh t i)
    _ = _ := by
      rw [faceRunAt_decompose, map_smul, intrinsicFaceChart_linear_faceUnit,
        intrinsicFaceChart_entryAt]
      ext k
      fin_cases k <;> simp <;> ring

lemma retainedLowerRunCoeff_pos {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ) / 2)
    (i : SourceIndex A B) : 0 < retainedLowerRunCoeff A B hh d i := by
  have hb := lowerRunCoeff_nonneg A B hh i
  have ha := upperRunCoeff_nonneg A B hh i
  have hs := lowerRunCoeff_add_upperRunCoeff_pos A B hh i
  unfold retainedLowerRunCoeff
  nlinarith

lemma retainedUpperRunCoeff_pos {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ) / 2)
    (i : SourceIndex A B) : 0 < retainedUpperRunCoeff A B hh d i := by
  have hb := lowerRunCoeff_nonneg A B hh i
  have ha := upperRunCoeff_nonneg A B hh i
  have hs := lowerRunCoeff_add_upperRunCoeff_pos A B hh i
  unfold retainedUpperRunCoeff
  nlinarith

lemma retainedLowerRunCoeff_one_sub (d : ℝ) (i : SourceIndex A B) :
    retainedLowerRunCoeff A B hh (1 - d) i = retainedUpperRunCoeff A B hh d i := by
  simp [retainedLowerRunCoeff, retainedUpperRunCoeff]

lemma retainedRunCoeff_sum (d : ℝ) (i : SourceIndex A B) :
    retainedLowerRunCoeff A B hh d i + retainedUpperRunCoeff A B hh d i =
      2 * middleLength A B hh i := by
  rw [retainedLowerRunCoeff, retainedUpperRunCoeff,
    ← lowerRunCoeff_add_upperRunCoeff A B hh i]
  ring

noncomputable def localB (d : ℝ) (i : SourceIndex A B) : Plane :=
  intrinsicFaceChart A B hh i (faceEntryAt A B hh d i)

noncomputable def localE (d : ℝ) (i : SourceIndex A B) : Plane :=
  intrinsicFaceChart A B hh i (faceExitAt A B hh d i) - localB A B hh d i

noncomputable def localD (d : ℝ) (i : SourceIndex A B) : Plane :=
  intrinsicFaceChart A B hh i (faceEntryAt A B hh (1 - d) i) - localB A B hh d i

noncomputable def localRatio (d : ℝ) (i : SourceIndex A B) : ℝ :=
  retainedUpperRunCoeff A B hh d i / retainedLowerRunCoeff A B hh d i

lemma localE_eq (d : ℝ) (i : SourceIndex A B) :
    localE A B hh d i = WithLp.toLp 2 ![retainedLowerRunCoeff A B hh d i, 0] := by
  rw [localE, localB, intrinsicFaceChart_exitAt, intrinsicFaceChart_entryAt]
  ext k
  fin_cases k <;> simp <;> ring

def faceExitC (i : SourceIndex A B) : ℝ :=
  inner ℝ (faceUnit A B hh i) (faceExitHingeVector A B hh i)

def faceExitS (i : SourceIndex A B) : ℝ :=
  inner ℝ (faceTransverse A B hh i) (faceExitHingeVector A B hh i)

def faceExitAlpha (i : SourceIndex A B) : ℝ :=
  InnerProductGeometry.angle (faceUnit A B hh i) (faceExitHingeVector A B hh i)

lemma faceExitHingeVector_decompose (i : SourceIndex A B) :
    faceExitHingeVector A B hh i =
      faceExitC A B hh i • faceUnit A B hh i +
        faceExitS A B hh i • faceTransverse A B hh i := by
  have hs := (faceBasis A B hh i).sum_repr' (faceExitHingeVector A B hh i)
  rw [Fin.sum_univ_two, faceBasis_zero, faceBasis_one, inner_neg_left] at hs
  simpa [faceExitC, faceExitS, smul_neg, neg_smul] using hs.symm

def faceAlpha (i : SourceIndex A B) : ℝ :=
  InnerProductGeometry.angle (faceUnit A B hh i) (faceHingeVector A B hh i)

lemma faceHingeVector_ne_zero_local (i : SourceIndex A B) :
    faceHingeVector A B hh i ≠ 0 := by
  intro hz
  have hm := congrArg
    (certificate A B hh (cycle A B i)).chart.linearIsometry hz
  rw [map_zero, chartLinear_faceHingeVector] at hm
  exact hingeVector_ne_zero A B hh i hm

lemma faceHinge_norm_sq (i : SourceIndex A B) :
    ‖faceHingeVector A B hh i‖ ^ 2 =
      faceC A B hh i ^ 2 + faceS A B hh i ^ 2 := by
  have he := congrArg (fun z => inner ℝ z z) (faceHingeVector_decompose A B hh i)
  rw [inner_add_left, inner_add_right, inner_add_right] at he
  simp only [face_inner_smul_left A B hh i, face_inner_smul_right A B hh i,
    faceUnit_inner_self, faceTransverse_inner_self,
    faceUnit_transverse_inner, faceTransverse_unit_inner, mul_zero, add_zero,
    real_inner_self_eq_norm_sq, faceUnit_norm, faceTransverse_norm, one_pow] at he
  nlinarith

lemma faceC_eq_norm_mul_cos_alpha (i : SourceIndex A B) :
    faceC A B hh i = ‖faceHingeVector A B hh i‖ * Real.cos (faceAlpha A B hh i) := by
  have hc := InnerProductGeometry.cos_angle (faceUnit A B hh i) (faceHingeVector A B hh i)
  rw [faceUnit_norm, one_mul, faceUnit_hinge_inner] at hc
  have hn := (norm_pos_iff.mpr (faceHingeVector_ne_zero_local A B hh i)).ne'
  rw [faceAlpha]
  have he := (eq_div_iff hn).mp hc
  calc
    faceC A B hh i = Real.cos (faceAlpha A B hh i) *
        ‖faceHingeVector A B hh i‖ := he.symm
    _ = _ := mul_comm _ _

lemma faceS_eq_norm_mul_sin_alpha (i : SourceIndex A B) :
    faceS A B hh i = ‖faceHingeVector A B hh i‖ * Real.sin (faceAlpha A B hh i) := by
  have htrig := Real.sin_sq_add_cos_sq (faceAlpha A B hh i)
  have hc := faceC_eq_norm_mul_cos_alpha A B hh i
  have hnorm := faceHinge_norm_sq A B hh i
  have hR := norm_pos_iff.mpr (faceHingeVector_ne_zero_local A B hh i)
  have hs0 : 0 ≤ Real.sin (faceAlpha A B hh i) :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      (InnerProductGeometry.angle_nonneg _ _)
      (InnerProductGeometry.angle_le_pi _ _)
  have hS := faceS_pos A B hh i
  have hsq : (‖faceHingeVector A B hh i‖ *
      Real.sin (faceAlpha A B hh i)) ^ 2 = faceS A B hh i ^ 2 := by
    rw [hc] at hnorm
    linear_combination hnorm + ‖faceHingeVector A B hh i‖ ^ 2 * htrig
  have hx0 : 0 ≤ ‖faceHingeVector A B hh i‖ *
      Real.sin (faceAlpha A B hh i) := mul_nonneg hR.le hs0
  nlinarith

lemma faceExitS_pos (i : SourceIndex A B) : 0 < faceExitS A B hh i := by
  have hhgt : heightLinear h
      ((certificate A B hh (cycle A B i)).chart.linearIsometry
        (faceExitHingeVector A B hh i)) = 1 := by
    rw [chartLinear_faceExitHingeVector, hingeVector_height]
  have hd := congrArg (fun z => heightLinear h
    ((certificate A B hh (cycle A B i)).chart.linearIsometry z))
    (faceExitHingeVector_decompose A B hh i)
  simp only [map_add, map_smul] at hd
  rw [chartLinear_faceUnit_height, chartLinear_faceTransverse_height, hhgt] at hd
  have hp : 0 < ‖faceResidual A B hh i‖⁻¹ :=
    inv_pos.mpr (norm_pos_iff.mpr (faceResidual_ne_zero A B hh i))
  simp only [smul_eq_mul, mul_zero, zero_add] at hd
  have hprod : 0 < faceExitS A B hh i * ‖faceResidual A B hh i‖⁻¹ := by
    rw [← hd]
    norm_num
  exact pos_of_mul_pos_right (by simpa [mul_comm] using hprod) hp.le

lemma faceExitHinge_norm_sq (i : SourceIndex A B) :
    ‖faceExitHingeVector A B hh i‖ ^ 2 =
      faceExitC A B hh i ^ 2 + faceExitS A B hh i ^ 2 := by
  have he := congrArg (fun z => inner ℝ z z)
    (faceExitHingeVector_decompose A B hh i)
  rw [inner_add_left, inner_add_right, inner_add_right] at he
  simp only [face_inner_smul_left A B hh i, face_inner_smul_right A B hh i,
    faceUnit_inner_self, faceTransverse_inner_self,
    faceUnit_transverse_inner, faceTransverse_unit_inner, mul_zero, add_zero,
    real_inner_self_eq_norm_sq, faceUnit_norm, faceTransverse_norm, one_pow] at he
  nlinarith

lemma faceExitC_eq_norm_mul_cos (i : SourceIndex A B) :
    faceExitC A B hh i =
      ‖faceExitHingeVector A B hh i‖ * Real.cos (faceExitAlpha A B hh i) := by
  have hc := InnerProductGeometry.cos_angle
    (faceUnit A B hh i) (faceExitHingeVector A B hh i)
  rw [faceUnit_norm, one_mul] at hc
  have hn := (norm_pos_iff.mpr (faceExitHingeVector_ne_zero A B hh i)).ne'
  rw [faceExitAlpha, faceExitC]
  have he := (eq_div_iff hn).mp hc
  calc
    inner ℝ (faceUnit A B hh i) (faceExitHingeVector A B hh i) =
        Real.cos (faceExitAlpha A B hh i) * ‖faceExitHingeVector A B hh i‖ := he.symm
    _ = _ := mul_comm _ _

lemma faceExitS_eq_norm_mul_sin (i : SourceIndex A B) :
    faceExitS A B hh i =
      ‖faceExitHingeVector A B hh i‖ * Real.sin (faceExitAlpha A B hh i) := by
  have htrig := Real.sin_sq_add_cos_sq (faceExitAlpha A B hh i)
  have hc := faceExitC_eq_norm_mul_cos A B hh i
  have hnorm := faceExitHinge_norm_sq A B hh i
  have hR := norm_pos_iff.mpr (faceExitHingeVector_ne_zero A B hh i)
  have hs0 : 0 ≤ Real.sin (faceExitAlpha A B hh i) :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      (InnerProductGeometry.angle_nonneg _ _)
      (InnerProductGeometry.angle_le_pi _ _)
  have hS := faceExitS_pos A B hh i
  have hsq : (‖faceExitHingeVector A B hh i‖ *
      Real.sin (faceExitAlpha A B hh i)) ^ 2 = faceExitS A B hh i ^ 2 := by
    rw [hc] at hnorm
    linear_combination hnorm + ‖faceExitHingeVector A B hh i‖ ^ 2 * htrig
  have hx0 : 0 ≤ ‖faceExitHingeVector A B hh i‖ *
      Real.sin (faceExitAlpha A B hh i) := mul_nonneg hR.le hs0
  nlinarith

lemma localD_eq (d : ℝ) (i : SourceIndex A B) :
    localD A B hh d i = (1 - 2*d) • WithLp.toLp 2 ![
      faceC A B hh i, -faceS A B hh i] := by
  rw [localD, localB, intrinsicFaceChart_entryAt, intrinsicFaceChart_entryAt]
  ext k
  fin_cases k <;> simp <;> ring

lemma faceAlpha_eq_physical (i : SourceIndex A B) :
    faceAlpha A B hh i =
      InnerProductGeometry.angle (middleDirection A B hh i) (hingeVector A B hh i) := by
  unfold faceAlpha InnerProductGeometry.angle
  have hi := (certificate A B hh (cycle A B i)).chart.linearIsometry.inner_map_map
    (faceUnit A B hh i) (faceHingeVector A B hh i)
  rw [chartLinear_faceUnit, chartLinear_faceHingeVector] at hi
  have hu := (certificate A B hh (cycle A B i)).chart.linearIsometry.norm_map
    (faceUnit A B hh i)
  rw [chartLinear_faceUnit] at hu
  have hg := (certificate A B hh (cycle A B i)).chart.linearIsometry.norm_map
    (faceHingeVector A B hh i)
  rw [chartLinear_faceHingeVector] at hg
  rw [hi, hu, hg]

lemma faceExitAlpha_eq_physical (i : SourceIndex A B) :
    faceExitAlpha A B hh i =
      InnerProductGeometry.angle (middleDirection A B hh i) (hingeVector A B hh (next i)) := by
  unfold faceExitAlpha InnerProductGeometry.angle
  have hi := (certificate A B hh (cycle A B i)).chart.linearIsometry.inner_map_map
    (faceUnit A B hh i) (faceExitHingeVector A B hh i)
  rw [chartLinear_faceUnit, chartLinear_faceExitHingeVector] at hi
  have hu := (certificate A B hh (cycle A B i)).chart.linearIsometry.norm_map
    (faceUnit A B hh i)
  rw [chartLinear_faceUnit] at hu
  have hg := (certificate A B hh (cycle A B i)).chart.linearIsometry.norm_map
    (faceExitHingeVector A B hh i)
  rw [chartLinear_faceExitHingeVector] at hg
  rw [hi, hu, hg]

lemma intrinsicQ_eq_alpha_sub_exitAlpha (i : SourceIndex A B) :
    intrinsicQ A B (hh := hh) i = faceAlpha A B hh i - faceExitAlpha A B hh (prev i) := by
  rw [intrinsicQ, faceAlpha_eq_physical, faceExitAlpha_eq_physical, next_prev]

/-- Angle at the retained lower endpoint between the actual retained lower-rim
ray and the upward entry hinge.  The trim parameter is geometric, rather than
phantom: `faceRunAt d` is the actual lower boundary run of the retained facet. -/
noncomputable def retainedLowerEntryAngle (d : ℝ) (i : SourceIndex A B) : ℝ :=
  InnerProductGeometry.angle (faceRunAt A B hh d i) (faceHingeVector A B hh i)

/-- Angle at the retained lower endpoint between the actual retained lower-rim
ray and the upward exit hinge of the same source facet. -/
noncomputable def retainedLowerExitAngle (d : ℝ) (i : SourceIndex A B) : ℝ :=
  InnerProductGeometry.angle (faceRunAt A B hh d i) (faceExitHingeVector A B hh i)

/-- The physical material-sector turn at the retained lower copy of hinge `i`.
It is the entry-face sector plus the supplementary sector in the preceding
face, both measured from actual chart vectors of the retained source facets. -/
noncomputable def physicalBeta (d : ℝ) (i : SourceIndex A B) : ℝ :=
  retainedLowerEntryAngle A B hh d i +
    (Real.pi - retainedLowerExitAngle A B hh d (prev i))

lemma retainedLowerEntryAngle_eq_faceAlpha {d : ℝ} (hd0 : 0 < d)
    (hd1 : d < (1 : ℝ) / 2) (i : SourceIndex A B) :
    retainedLowerEntryAngle A B hh d i = faceAlpha A B hh i := by
  rw [retainedLowerEntryAngle, faceRunAt_decompose,
    InnerProductGeometry.angle_smul_left_of_pos _ _
      (retainedLowerRunCoeff_pos A B hh hd0 hd1 i)]
  rfl

lemma retainedLowerExitAngle_eq_faceExitAlpha {d : ℝ} (hd0 : 0 < d)
    (hd1 : d < (1 : ℝ) / 2) (i : SourceIndex A B) :
    retainedLowerExitAngle A B hh d i = faceExitAlpha A B hh i := by
  rw [retainedLowerExitAngle, faceRunAt_decompose,
    InnerProductGeometry.angle_smul_left_of_pos _ _
      (retainedLowerRunCoeff_pos A B hh hd0 hd1 i)]
  rfl

/-- For every positive trim, the intrinsic physical turn is exactly the
retained lower material-sector excess over a straight angle. -/
theorem intrinsicQ_eq_physicalBeta_sub_pi {d : ℝ} (hd0 : 0 < d)
    (hd1 : d < (1 : ℝ) / 2) (i : SourceIndex A B) :
    intrinsicQ A B (hh := hh) i = physicalBeta A B hh d i - Real.pi := by
  rw [physicalBeta,
    retainedLowerEntryAngle_eq_faceAlpha A B hh hd0 hd1,
    retainedLowerExitAngle_eq_faceExitAlpha A B hh hd0 hd1,
    intrinsicQ_eq_alpha_sub_exitAlpha]
  ring

/-- The physical retained material sector is independent of positive trim. -/
theorem physicalBeta_trim_invariant {d₁ d₂ : ℝ}
    (hd₁0 : 0 < d₁) (hd₁1 : d₁ < (1 : ℝ) / 2)
    (hd₂0 : 0 < d₂) (hd₂1 : d₂ < (1 : ℝ) / 2)
    (i : SourceIndex A B) :
    physicalBeta A B hh d₁ i = physicalBeta A B hh d₂ i := by
  rw [physicalBeta, physicalBeta,
    retainedLowerEntryAngle_eq_faceAlpha A B hh hd₁0 hd₁1,
    retainedLowerExitAngle_eq_faceExitAlpha A B hh hd₁0 hd₁1,
    retainedLowerEntryAngle_eq_faceAlpha A B hh hd₂0 hd₂1,
    retainedLowerExitAngle_eq_faceExitAlpha A B hh hd₂0 hd₂1]

lemma localD_polar (d : ℝ) (i : SourceIndex A B) :
    localD A B hh d i =
      ((1 - 2*d) * ‖faceHingeVector A B hh i‖) •
        direction (-faceAlpha A B hh i) := by
  rw [localD_eq, faceC_eq_norm_mul_cos_alpha, faceS_eq_norm_mul_sin_alpha]
  ext k
  fin_cases k <;> simp [direction, Real.cos_neg, Real.sin_neg] <;> ring

noncomputable def localExitD (d : ℝ) (i : SourceIndex A B) : Plane :=
  intrinsicFaceChart A B hh i (faceExitAt A B hh (1-d) i) -
    intrinsicFaceChart A B hh i (faceExitAt A B hh d i)

lemma intrinsicFaceChart_linear_faceExitHinge (i : SourceIndex A B) :
    (intrinsicFaceChart A B hh i).linearIsometryEquiv
        (faceExitHingeVector A B hh i) =
      WithLp.toLp 2 ![faceExitC A B hh i, -faceExitS A B hh i] := by
  change (faceBasis A B hh i).repr (faceExitHingeVector A B hh i) = _
  ext k
  fin_cases k
  · change ((faceBasis A B hh i).repr (faceExitHingeVector A B hh i)) 0 = _
    rw [(faceBasis A B hh i).repr_apply_apply, faceBasis_zero]
    rfl
  · change ((faceBasis A B hh i).repr (faceExitHingeVector A B hh i)) 1 = _
    rw [(faceBasis A B hh i).repr_apply_apply, faceBasis_one, inner_neg_left]
    rfl

lemma faceExitAt_sub (d : ℝ) (i : SourceIndex A B) :
    faceExitAt A B hh (1-d) i - faceExitAt A B hh d i =
      (1-2*d) • faceExitHingeVector A B hh i := by
  simp only [faceExitAt, faceExitHingeVector, AffineMap.lineMap_apply_module]
  module

lemma localExitD_eq (d : ℝ) (i : SourceIndex A B) :
    localExitD A B hh d i = (1-2*d) •
      WithLp.toLp 2 ![faceExitC A B hh i, -faceExitS A B hh i] := by
  rw [localExitD]
  calc
    _ = (intrinsicFaceChart A B hh i).linearIsometryEquiv
        (faceExitAt A B hh (1-d) i - faceExitAt A B hh d i) :=
      ((intrinsicFaceChart A B hh i).map_vsub _ _).symm
    _ = _ := by rw [faceExitAt_sub, map_smul, intrinsicFaceChart_linear_faceExitHinge]

lemma localExitD_polar (d : ℝ) (i : SourceIndex A B) :
    localExitD A B hh d i =
      ((1-2*d) * ‖faceExitHingeVector A B hh i‖) •
        direction (-faceExitAlpha A B hh i) := by
  rw [localExitD_eq, faceExitC_eq_norm_mul_cos, faceExitS_eq_norm_mul_sin]
  ext k
  fin_cases k <;> simp [direction, Real.cos_neg, Real.sin_neg] <;> ring

lemma faceHinge_norm_eq_prevExit (i : SourceIndex A B) :
    ‖faceHingeVector A B hh i‖ = ‖faceExitHingeVector A B hh (prev i)‖ := by
  calc
    _ = ‖hingeVector A B hh i‖ := by
      rw [← chartLinear_faceHingeVector A B hh i,
        (certificate A B hh (cycle A B i)).chart.linearIsometry.norm_map]
    _ = ‖(certificate A B hh (cycle A B (prev i))).chart.linearIsometry
        (faceExitHingeVector A B hh (prev i))‖ := by
      rw [chartLinear_faceExitHingeVector, next_prev]
    _ = ‖faceExitHingeVector A B hh (prev i)‖ :=
      (certificate A B hh (cycle A B (prev i))).chart.linearIsometry.norm_map _

/-- The physical opposite-side unfolding transition: rotating the next face by
its intrinsic signed turn identifies the entire retained common hinge. -/
theorem planeRotation_localD_eq_prevExitD (d : ℝ) (i : SourceIndex A B) :
    planeRotation (intrinsicQ A B (hh := hh) i) (localD A B hh d i) =
      localExitD A B hh d (prev i) := by
  rw [localD_polar, map_smul, planeRotation_direction, localExitD_polar,
    ← faceHinge_norm_eq_prevExit A B hh i]
  congr 2
  have hq := intrinsicQ_eq_alpha_sub_exitAlpha A B hh i
  congr 1
  linarith

lemma localRatio_pos {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2)
    (i : SourceIndex A B) : 0 < localRatio A B hh d i :=
  div_pos (retainedUpperRunCoeff_pos A B hh hd0 hd1 i)
    (retainedLowerRunCoeff_pos A B hh hd0 hd1 i)

lemma localRatio_smul_localE {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2)
    (i : SourceIndex A B) :
    localRatio A B hh d i • localE A B hh d i =
      WithLp.toLp 2 ![retainedUpperRunCoeff A B hh d i, 0] := by
  rw [localRatio, localE_eq]
  ext k
  fin_cases k
  · simp
    field_simp [(retainedLowerRunCoeff_pos A B hh hd0 hd1 i).ne']
  · simp

lemma localB_add_localE (d : ℝ) (i : SourceIndex A B) :
    localB A B hh d i + localE A B hh d i =
      intrinsicFaceChart A B hh i (faceExitAt A B hh d i) := by
  rw [localE]
  abel

lemma localB_add_localD (d : ℝ) (i : SourceIndex A B) :
    localB A B hh d i + localD A B hh d i =
      intrinsicFaceChart A B hh i (faceEntryAt A B hh (1-d) i) := by
  rw [localD]
  abel

lemma local_exitUpper_vertex {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2)
    (i : SourceIndex A B) :
    localB A B hh d i + localD A B hh d i +
        localRatio A B hh d i • localE A B hh d i =
      intrinsicFaceChart A B hh i (faceExitAt A B hh (1-d) i) := by
  rw [localB_add_localD, localRatio_smul_localE A B hh hd0 hd1,
    intrinsicFaceChart_entryAt, intrinsicFaceChart_exitAt,
    retainedLowerRunCoeff_one_sub]
  ext k
  fin_cases k <;> simp <;> ring

lemma local_hinge_step {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2)
    (i : SourceIndex A B) :
    localExitD A B hh d i = localD A B hh d i +
      (localRatio A B hh d i - 1) • localE A B hh d i := by
  rw [localExitD]
  have hu := local_exitUpper_vertex A B hh hd0 hd1 i
  have hl := localB_add_localE A B hh d i
  rw [← hu, ← hl]
  module

noncomputable def retainedFaceHull (d : ℝ) (i : SourceIndex A B) :
    Set (FaceSpace A B h (cycle A B i)) :=
  convexHull ℝ {faceEntryAt A B hh d i, faceExitAt A B hh d i,
    faceExitAt A B hh (1-d) i, faceEntryAt A B hh (1-d) i}

lemma intrinsicFaceChart_retainedFaceHull {d : ℝ} (hd0 : 0 < d)
    (hd1 : d < (1 : ℝ)/2) (i : SourceIndex A B) :
    intrinsicFaceChart A B hh i '' retainedFaceHull A B hh d i =
      hull (localB A B hh d i) (localE A B hh d i)
        (localD A B hh d i) (localRatio A B hh d i) := by
  rw [retainedFaceHull, hull]
  change (intrinsicFaceChart A B hh i).toAffineEquiv.toAffineMap ''
      convexHull ℝ {faceEntryAt A B hh d i, faceExitAt A B hh d i,
        faceExitAt A B hh (1-d) i, faceEntryAt A B hh (1-d) i} = _
  rw [(intrinsicFaceChart A B hh i).toAffineEquiv.toAffineMap.image_convexHull]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (localB_add_localE A B hh d i).symm)
    · exact Or.inr (Or.inr (Or.inl (local_exitUpper_vertex A B hh hd0 hd1 i).symm))
    · exact Or.inr (Or.inr (Or.inr (localB_add_localD A B hh d i).symm))
  · intro hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr (Or.inl rfl), (localB_add_localE A B hh d i).symm⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)),
        (local_exitUpper_vertex A B hh hd0 hd1 i).symm⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), (localB_add_localD A B hh d i).symm⟩

lemma faceEntryLower_mem_domain (i : SourceIndex A B) :
    faceEntryLower A B hh i ∈ (certificate A B hh (cycle A B i)).domain := by
  exact facePoint_mem A B hh i _ _

lemma faceEntryUpper_mem_domain (i : SourceIndex A B) :
    faceEntryUpper A B hh i ∈ (certificate A B hh (cycle A B i)).domain := by
  exact facePoint_mem A B hh i _ _

lemma faceExitLower_mem_domain (i : SourceIndex A B) :
    faceExitLower A B hh i ∈ (certificate A B hh (cycle A B i)).domain := by
  exact facePoint_mem A B hh i _ _

lemma faceExitUpper_mem_domain (i : SourceIndex A B) :
    faceExitUpper A B hh i ∈ (certificate A B hh (cycle A B i)).domain := by
  exact facePoint_mem A B hh i _ _

@[simp] lemma chart_faceEntryAt (t : ℝ) (i : SourceIndex A B) :
    (certificate A B hh (cycle A B i)).chart (faceEntryAt A B hh t i) =
      mixedPoint A B h t (entryGap A B i) := by
  rw [faceEntryAt]
  change (certificate A B hh (cycle A B i)).chart.toAffineMap
      (AffineMap.lineMap (faceEntryLower A B hh i) (faceEntryUpper A B hh i) t) = _
  rw [(certificate A B hh (cycle A B i)).chart.toAffineMap.apply_lineMap]
  change AffineMap.lineMap
    ((certificate A B hh (cycle A B i)).chart (faceEntryLower A B hh i))
    ((certificate A B hh (cycle A B i)).chart (faceEntryUpper A B hh i)) t = _
  rw [chart_faceEntryLower, chart_faceEntryUpper]
  ext k
  fin_cases k <;>
    simp [AffineMap.lineMap_apply_module, lowerEndpoint, upperEndpoint, mixedPoint,
      pack, lowerLift, upperLift] <;> ring

@[simp] lemma chart_faceExitAt (t : ℝ) (i : SourceIndex A B) :
    (certificate A B hh (cycle A B i)).chart (faceExitAt A B hh t i) =
      mixedPoint A B h t (entryGap A B (next i)) := by
  rw [faceExitAt]
  change (certificate A B hh (cycle A B i)).chart.toAffineMap
      (AffineMap.lineMap (faceExitLower A B hh i) (faceExitUpper A B hh i) t) = _
  rw [(certificate A B hh (cycle A B i)).chart.toAffineMap.apply_lineMap]
  change AffineMap.lineMap
    ((certificate A B hh (cycle A B i)).chart (faceExitLower A B hh i))
    ((certificate A B hh (cycle A B i)).chart (faceExitUpper A B hh i)) t = _
  rw [chart_faceExitLower, chart_faceExitUpper]
  ext k
  fin_cases k <;>
    simp [AffineMap.lineMap_apply_module, lowerEndpoint, upperEndpoint, mixedPoint,
      pack, lowerLift, upperLift] <;> ring

@[simp] lemma faceEntryAt_height (t : ℝ) (i : SourceIndex A B) :
    (certificate A B hh (cycle A B i)).height (faceEntryAt A B hh t i) = t := by
  rw [faceEntryAt]
  apply height_lineMap
  · change heightLinear h
      ((certificate A B hh (cycle A B i)).chart (faceEntryLower A B hh i)) = 0
    rw [chart_faceEntryLower, lowerEndpoint_height]
  · change heightLinear h
      ((certificate A B hh (cycle A B i)).chart (faceEntryUpper A B hh i)) = 1
    rw [chart_faceEntryUpper, upperEndpoint_height]

@[simp] lemma faceExitAt_height (t : ℝ) (i : SourceIndex A B) :
    (certificate A B hh (cycle A B i)).height (faceExitAt A B hh t i) = t := by
  rw [faceExitAt]
  apply height_lineMap
  · change heightLinear h
      ((certificate A B hh (cycle A B i)).chart (faceExitLower A B hh i)) = 0
    rw [chart_faceExitLower, lowerEndpoint_height]
  · change heightLinear h
      ((certificate A B hh (cycle A B i)).chart (faceExitUpper A B hh i)) = 1
    rw [chart_faceExitUpper, upperEndpoint_height]

@[simp] lemma flatLinear_horizontalIsometry (x : Plane) :
    flatLinear (horizontalIsometry x) = x := by
  ext k
  fin_cases k <;> rfl

@[simp] lemma heightLinear_horizontalIsometry (x : Plane) :
    heightLinear h (horizontalIsometry x) = 0 := by
  change h⁻¹ * (horizontalIsometry x) 2 = 0
  change h⁻¹ * 0 = 0
  ring


end Raw
end
end PhysicalMixedTurnSource
