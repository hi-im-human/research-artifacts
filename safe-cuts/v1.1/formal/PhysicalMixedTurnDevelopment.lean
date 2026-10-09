import PhysicalMixedTurnGeometry

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

lemma sideLinear_middleDirection (v : Plane) (i : SourceIndex A B) :
    sideLinear A B h v (middleDirection A B hh i) =
      inner ℝ (horizontalIsometry v) (middleDirection A B hh i) := by
  rw [middleDirection, middleLength, middleStep_eq_horizontal]
  calc
    sideLinear A B h v
        (‖horizontalIsometry (edgeVector (middlePolygon A B).vertex i)‖⁻¹ •
          horizontalIsometry (edgeVector (middlePolygon A B).vertex i)) =
      ‖horizontalIsometry (edgeVector (middlePolygon A B).vertex i)‖⁻¹ *
        sideLinear A B h v
          (horizontalIsometry (edgeVector (middlePolygon A B).vertex i)) := by
      rw [map_smul, smul_eq_mul]
    _ = ‖horizontalIsometry (edgeVector (middlePolygon A B).vertex i)‖⁻¹ *
        inner ℝ (horizontalIsometry v)
          (horizontalIsometry (edgeVector (middlePolygon A B).vertex i)) := by
      congr 1
      rw [sideLinear, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
        flatLinear_horizontalIsometry, heightLinear_horizontalIsometry,
        horizontalIsometry.inner_map_map]
      simp
    _ = inner ℝ (horizontalIsometry v)
        (‖horizontalIsometry (edgeVector (middlePolygon A B).vertex i)‖⁻¹ •
          horizontalIsometry (edgeVector (middlePolygon A B).vertex i)) :=
      (real_inner_smul_right _ _ _).symm

lemma entryAt_prevRow_zero {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (i : SourceIndex A B) :
    sideRow A B h (cycle A B (prev i)).val
      ((certificate A B hh (cycle A B i)).chart (faceEntryAt A B hh t i)) = 0 := by
  rw [chart_faceEntryAt]
  have hm := (canonical_hinge_point_mem_both A B hh i t ht).1
  exact ((mem_materialFace A B hh (cycle A B (prev i)) _).mp hm).2

lemma exitAt_nextRow_zero {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (i : SourceIndex A B) :
    sideRow A B h (cycle A B (next i)).val
      ((certificate A B hh (cycle A B i)).chart (faceExitAt A B hh t i)) = 0 := by
  rw [chart_faceExitAt]
  have hm := (canonical_hinge_point_mem_both A B hh (next i) t ht).2
  have hs : cycle A B (finRotate (sideCount A B) (prev (next i))) = cycle A B (next i) := by
    rw [finRotate_eq_next, next_prev]
  rw [hs] at hm
  exact ((mem_materialFace A B hh (cycle A B (next i)) _).mp hm).2

lemma faceEntryAt_mem_domain {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (i : SourceIndex A B) :
    faceEntryAt A B hh t i ∈ (certificate A B hh (cycle A B i)).domain := by
  exact lineMap_mem_face (certificate A B hh (cycle A B i)).domain_convex
    (faceEntryLower_mem_domain A B hh i) (faceEntryUpper_mem_domain A B hh i) ht

lemma faceExitAt_mem_domain {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (i : SourceIndex A B) :
    faceExitAt A B hh t i ∈ (certificate A B hh (cycle A B i)).domain := by
  exact lineMap_mem_face (certificate A B hh (cycle A B i)).domain_convex
    (faceExitLower_mem_domain A B hh i) (faceExitUpper_mem_domain A B hh i) ht

lemma face_eq_entryAt_add_unit {t : ℝ} (i : SourceIndex A B)
    (x : FaceSpace A B h (cycle A B i))
    (hxt : (certificate A B hh (cycle A B i)).height x = t) :
    ∃ s : ℝ, x = faceEntryAt A B hh t i + s • faceUnit A B hh i := by
  let w := x - faceEntryAt A B hh t i
  have hwheight : heightLinear h
      ((certificate A B hh (cycle A B i)).chart.linearIsometry w) = 0 := by
    calc
      _ = heightLinear h
          ((certificate A B hh (cycle A B i)).chart x -
            (certificate A B hh (cycle A B i)).chart (faceEntryAt A B hh t i)) := by
        congr 1
        exact (certificate A B hh (cycle A B i)).chart.map_vsub _ _
      _ = (certificate A B hh (cycle A B i)).height x -
          (certificate A B hh (cycle A B i)).height (faceEntryAt A B hh t i) := by
        rw [map_sub]
        rfl
      _ = 0 := by rw [hxt, faceEntryAt_height]; ring
  let s := inner ℝ (faceUnit A B hh i) w
  have hw := eq_inner_smul_faceUnit_of_height_zero A B hh i w hwheight
  refine ⟨s, ?_⟩
  dsimp [s] at hw ⊢
  rw [← hw]
  dsimp [w]
  abel

lemma face_horizontal_parameter_bounds {t : ℝ} (i : SourceIndex A B)
    (x : FaceSpace A B h (cycle A B i))
    (hx : x ∈ (certificate A B hh (cycle A B i)).domain)
    (hxt : (certificate A B hh (cycle A B i)).height x = t) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ retainedLowerRunCoeff A B hh t i ∧
      x = faceEntryAt A B hh t i + s • faceUnit A B hh i := by
  obtain ⟨s, hxrep⟩ := face_eq_entryAt_add_unit A B hh i x hxt
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    rw [← hxt]
    exact (certificate A B hh (cycle A B i)).height_bounds hx
  have hchart : (certificate A B hh (cycle A B i)).chart x =
      s • middleDirection A B hh i +
        (certificate A B hh (cycle A B i)).chart (faceEntryAt A B hh t i) := by
    rw [hxrep, add_comm]
    calc
      _ = (certificate A B hh (cycle A B i)).chart.linearIsometry
          (s • faceUnit A B hh i) +ᵥ
          (certificate A B hh (cycle A B i)).chart (faceEntryAt A B hh t i) :=
        (certificate A B hh (cycle A B i)).chart.map_vadd _ _
      _ = _ := by rw [map_smul, chartLinear_faceUnit, vadd_eq_add]
  have hbody : (certificate A B hh (cycle A B i)).chart x ∈
      (halfspaces A B h).body := hx
  have hp := hbody (Sum.inr (cycle A B (prev i)))
  change 0 ≤ sideRow A B h (cycle A B (prev i)).val
    ((certificate A B hh (cycle A B i)).chart x) at hp
  have hp0 := entryAt_prevRow_zero A B hh ht i
  rw [hchart] at hp
  change 0 ≤ supportValue B (cycle A B (prev i)).val -
    sideLinear A B h (cycle A B (prev i)).val
      (s • middleDirection A B hh i +
        (certificate A B hh (cycle A B i)).chart (faceEntryAt A B hh t i)) at hp
  rw [map_add, map_smul, smul_eq_mul, sideLinear_middleDirection] at hp
  change supportValue B (cycle A B (prev i)).val -
    sideLinear A B h (cycle A B (prev i)).val
      ((certificate A B hh (cycle A B i)).chart (faceEntryAt A B hh t i)) = 0 at hp0
  have hs0 : 0 ≤ s := by
    have hn := prevNormal_middleDirection_neg A B hh i
    nlinarith
  let r := retainedLowerRunCoeff A B hh t i
  have hexit : faceExitAt A B hh t i =
      faceEntryAt A B hh t i + r • faceUnit A B hh i := by
    have hr := faceRunAt_decompose A B hh t i
    dsimp [faceRunAt, r] at hr ⊢
    rw [← hr]
    abel
  have hxexit : x = faceExitAt A B hh t i +
      (s-r) • faceUnit A B hh i := by
    rw [hxrep, hexit]
    module
  have hchart' : (certificate A B hh (cycle A B i)).chart x =
      (s-r) • middleDirection A B hh i +
        (certificate A B hh (cycle A B i)).chart (faceExitAt A B hh t i) := by
    rw [hxexit, add_comm]
    calc
      _ = (certificate A B hh (cycle A B i)).chart.linearIsometry
          ((s-r) • faceUnit A B hh i) +ᵥ
          (certificate A B hh (cycle A B i)).chart (faceExitAt A B hh t i) :=
        (certificate A B hh (cycle A B i)).chart.map_vadd _ _
      _ = _ := by rw [map_smul, chartLinear_faceUnit, vadd_eq_add]
  have hnrow := hbody (Sum.inr (cycle A B (next i)))
  change 0 ≤ sideRow A B h (cycle A B (next i)).val
    ((certificate A B hh (cycle A B i)).chart x) at hnrow
  have hn0 := exitAt_nextRow_zero A B hh ht i
  rw [hchart'] at hnrow
  change 0 ≤ supportValue B (cycle A B (next i)).val -
    sideLinear A B h (cycle A B (next i)).val
      ((s-r) • middleDirection A B hh i +
        (certificate A B hh (cycle A B i)).chart (faceExitAt A B hh t i)) at hnrow
  rw [map_add, map_smul, smul_eq_mul, sideLinear_middleDirection] at hnrow
  change supportValue B (cycle A B (next i)).val -
    sideLinear A B h (cycle A B (next i)).val
      ((certificate A B hh (cycle A B i)).chart (faceExitAt A B hh t i)) = 0 at hn0
  have hsr : s ≤ r := by
    have hn := nextNormal_middleDirection_pos A B hh i
    nlinarith
  exact ⟨s, hs0, hsr, hxrep⟩

lemma face_eq_entryAt_of_prevRow_zero {t : ℝ} (i : SourceIndex A B)
    (x : FaceSpace A B h (cycle A B i))
    (hx : x ∈ (certificate A B hh (cycle A B i)).domain)
    (hxt : (certificate A B hh (cycle A B i)).height x = t)
    (hz : sideRow A B h (cycle A B (prev i)).val
      ((certificate A B hh (cycle A B i)).chart x) = 0) :
    x = faceEntryAt A B hh t i := by
  obtain ⟨s, hs0, hsr, hxrep⟩ := face_horizontal_parameter_bounds A B hh i x hx hxt
  have ht : t ∈ Icc (0 : ℝ) 1 := by rw [← hxt]; exact (certificate A B hh _).height_bounds hx
  have hchart : (certificate A B hh (cycle A B i)).chart x =
      s • middleDirection A B hh i +
        (certificate A B hh (cycle A B i)).chart (faceEntryAt A B hh t i) := by
    rw [hxrep, add_comm]
    calc
      _ = (certificate A B hh (cycle A B i)).chart.linearIsometry
          (s • faceUnit A B hh i) +ᵥ
          (certificate A B hh (cycle A B i)).chart (faceEntryAt A B hh t i) :=
        (certificate A B hh (cycle A B i)).chart.map_vadd _ _
      _ = _ := by rw [map_smul, chartLinear_faceUnit, vadd_eq_add]
  have hz0 := entryAt_prevRow_zero A B hh ht i
  rw [hchart] at hz
  change supportValue B (cycle A B (prev i)).val -
    sideLinear A B h (cycle A B (prev i)).val
      (s • middleDirection A B hh i +
        (certificate A B hh (cycle A B i)).chart (faceEntryAt A B hh t i)) = 0 at hz
  rw [map_add, map_smul, smul_eq_mul, sideLinear_middleDirection] at hz
  change supportValue B (cycle A B (prev i)).val -
    sideLinear A B h (cycle A B (prev i)).val
      ((certificate A B hh (cycle A B i)).chart (faceEntryAt A B hh t i)) = 0 at hz0
  have hn := prevNormal_middleDirection_neg A B hh i
  have hs : s = 0 := by nlinarith
  simpa [hs] using hxrep

lemma face_eq_exitAt_of_nextRow_zero {t : ℝ} (i : SourceIndex A B)
    (x : FaceSpace A B h (cycle A B i))
    (hx : x ∈ (certificate A B hh (cycle A B i)).domain)
    (hxt : (certificate A B hh (cycle A B i)).height x = t)
    (hz : sideRow A B h (cycle A B (next i)).val
      ((certificate A B hh (cycle A B i)).chart x) = 0) :
    x = faceExitAt A B hh t i := by
  obtain ⟨s, hs0, hsr, hxrep⟩ := face_horizontal_parameter_bounds A B hh i x hx hxt
  have ht : t ∈ Icc (0 : ℝ) 1 := by rw [← hxt]; exact (certificate A B hh _).height_bounds hx
  let r := retainedLowerRunCoeff A B hh t i
  have hexit : faceExitAt A B hh t i =
      faceEntryAt A B hh t i + r • faceUnit A B hh i := by
    have hr := faceRunAt_decompose A B hh t i
    dsimp [faceRunAt, r] at hr ⊢
    rw [← hr]
    abel
  have hxexit : x = faceExitAt A B hh t i + (s-r) • faceUnit A B hh i := by
    rw [hxrep, hexit]
    module
  have hchart : (certificate A B hh (cycle A B i)).chart x =
      (s-r) • middleDirection A B hh i +
        (certificate A B hh (cycle A B i)).chart (faceExitAt A B hh t i) := by
    rw [hxexit, add_comm]
    calc
      _ = (certificate A B hh (cycle A B i)).chart.linearIsometry
          ((s-r) • faceUnit A B hh i) +ᵥ
          (certificate A B hh (cycle A B i)).chart (faceExitAt A B hh t i) :=
        (certificate A B hh (cycle A B i)).chart.map_vadd _ _
      _ = _ := by rw [map_smul, chartLinear_faceUnit, vadd_eq_add]
  have hz0 := exitAt_nextRow_zero A B hh ht i
  rw [hchart] at hz
  change supportValue B (cycle A B (next i)).val -
    sideLinear A B h (cycle A B (next i)).val
      ((s-r) • middleDirection A B hh i +
        (certificate A B hh (cycle A B i)).chart (faceExitAt A B hh t i)) = 0 at hz
  rw [map_add, map_smul, smul_eq_mul, sideLinear_middleDirection] at hz
  change supportValue B (cycle A B (next i)).val -
    sideLinear A B h (cycle A B (next i)).val
      ((certificate A B hh (cycle A B i)).chart (faceExitAt A B hh t i)) = 0 at hz0
  have hp := nextNormal_middleDirection_pos A B hh i
  have hs : s = r := by nlinarith
  simpa [hs] using hxexit

def trimParameter (d t : ℝ) : ℝ := (t-d) / (1-2*d)

lemma trimParameter_mem_Icc {d t : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2)
    (ht0 : d ≤ t) (ht1 : t ≤ 1-d) : trimParameter d t ∈ Icc (0 : ℝ) 1 := by
  have hp : 0 < 1-2*d := by linarith
  constructor
  · exact div_nonneg (sub_nonneg.mpr ht0) hp.le
  · rw [trimParameter, div_le_one hp]
    linarith

lemma trimParameter_identity {d t : ℝ} (hd : d ≠ (1 : ℝ)/2) :
    d + trimParameter d t * (1-2*d) = t := by
  have hden : 1-d*2 ≠ 0 := by
    intro hz
    apply hd
    nlinarith
  rw [trimParameter]
  field_simp [hden]
  ring

lemma faceEntryAt_eq_retained_lineMap {d t : ℝ} (hd : d ≠ (1 : ℝ)/2)
    (i : SourceIndex A B) :
    faceEntryAt A B hh t i = AffineMap.lineMap
      (faceEntryAt A B hh d i) (faceEntryAt A B hh (1-d) i)
      (trimParameter d t) := by
  have ht := trimParameter_identity (d := d) (t := t) hd
  conv_lhs => rw [← ht]
  simp only [faceEntryAt, AffineMap.lineMap_apply_module]
  module

lemma faceExitAt_eq_retained_lineMap {d t : ℝ} (hd : d ≠ (1 : ℝ)/2)
    (i : SourceIndex A B) :
    faceExitAt A B hh t i = AffineMap.lineMap
      (faceExitAt A B hh d i) (faceExitAt A B hh (1-d) i)
      (trimParameter d t) := by
  have ht := trimParameter_identity (d := d) (t := t) hd
  conv_lhs => rw [← ht]
  simp only [faceExitAt, AffineMap.lineMap_apply_module]
  module

lemma retainedLowerRunCoeff_pos_of_mem_Ioo {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (i : SourceIndex A B) : 0 < retainedLowerRunCoeff A B hh t i := by
  have hb := lowerRunCoeff_nonneg A B hh i
  have ha := upperRunCoeff_nonneg A B hh i
  have hs := lowerRunCoeff_add_upperRunCoeff_pos A B hh i
  unfold retainedLowerRunCoeff
  by_cases hbp : 0 < lowerRunCoeff A B hh i
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht.2) hbp)
      (mul_nonneg ht.1.le ha)
  · have hap : 0 < upperRunCoeff A B hh i := by linarith
    exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2.le) hb)
      (mul_pos ht.1 hap)

lemma local_entryAt_eq (d t : ℝ) (hd : d ≠ (1 : ℝ)/2) (i : SourceIndex A B) :
    intrinsicFaceChart A B hh i (faceEntryAt A B hh t i) =
      localB A B hh d i + trimParameter d t • localD A B hh d i := by
  have hden : 1 - d*2 ≠ 0 := by
    intro hz
    apply hd
    nlinarith
  have htau : d + trimParameter d t * (1-2*d) = t := by
    rw [trimParameter]
    field_simp [hden]
    ring
  rw [localB]
  rw [intrinsicFaceChart_entryAt]
  rw [localD_eq, intrinsicFaceChart_entryAt]
  ext k
  fin_cases k <;> simp
  · linear_combination (-faceC A B hh i) * htau
  · linear_combination faceS A B hh i * htau

lemma retained_width_identity {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2)
    (t : ℝ) (i : SourceIndex A B) :
    rho (localRatio A B hh d i) (trimParameter d t) *
        retainedLowerRunCoeff A B hh d i =
      retainedLowerRunCoeff A B hh t i := by
  have hb := (retainedLowerRunCoeff_pos A B hh hd0 hd1 i).ne'
  have hd : 1-2*d ≠ 0 := by linarith
  have hd' : 1-d*2 ≠ 0 := by linarith
  rw [rho, localRatio, trimParameter]
  field_simp [hb, hd, hd']
  simp only [retainedLowerRunCoeff, retainedUpperRunCoeff]
  ring

lemma intrinsicFaceChart_entry_add_eq_panel {d t : ℝ}
    (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2) (ht0 : d ≤ t) (ht1 : t ≤ 1-d)
    (s : ℝ) (i : SourceIndex A B) :
    intrinsicFaceChart A B hh i
        (faceEntryAt A B hh t i + s • faceUnit A B hh i) =
      panel (localB A B hh d i) (localE A B hh d i) (localD A B hh d i)
        (localRatio A B hh d i)
        (s / retainedLowerRunCoeff A B hh t i) (trimParameter d t) := by
  have hdn : d ≠ (1 : ℝ)/2 := ne_of_lt hd1
  have ht : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_lt_of_le hd0 ht0, by linarith⟩
  have hr := (retainedLowerRunCoeff_pos_of_mem_Ioo A B hh ht i).ne'
  have hwidth := retained_width_identity A B hh hd0 hd1 t i
  have hsc :
      (s / retainedLowerRunCoeff A B hh t i *
        rho (localRatio A B hh d i) (trimParameter d t)) *
          retainedLowerRunCoeff A B hh d i = s := by
    rw [mul_assoc, hwidth, div_mul_cancel₀ s hr]
  have hm := (intrinsicFaceChart A B hh i).map_vadd
    (faceEntryAt A B hh t i) (s • faceUnit A B hh i)
  simp only [vadd_eq_add] at hm
  rw [map_smul, intrinsicFaceChart_linear_faceUnit] at hm
  calc
    _ = intrinsicFaceChart A B hh i
        (s • faceUnit A B hh i + faceEntryAt A B hh t i) := by rw [add_comm]
    _ = s • WithLp.toLp 2 ![1, 0] +
        intrinsicFaceChart A B hh i (faceEntryAt A B hh t i) := hm
    _ = _ := by
      have hevec :
          (s / retainedLowerRunCoeff A B hh t i *
              rho (localRatio A B hh d i) (trimParameter d t)) •
            localE A B hh d i = s • WithLp.toLp 2 ![(1 : ℝ), 0] := by
        rw [localE_eq]
        calc
          _ = ((s / retainedLowerRunCoeff A B hh t i *
                rho (localRatio A B hh d i) (trimParameter d t)) *
              retainedLowerRunCoeff A B hh d i) • WithLp.toLp 2 ![(1 : ℝ), 0] := by
            ext k
            fin_cases k <;> simp <;> ring
          _ = _ := by rw [hsc]
      rw [panel, local_entryAt_eq A B hh d t hdn i, hevec]
      abel

lemma heightTrim_convex (d : ℝ) (i : SourceIndex A B) :
    Convex ℝ (heightTrim (certificate A B hh (cycle A B i)).domain
      (certificate A B hh (cycle A B i)).height d) := by
  exact (certificate A B hh (cycle A B i)).domain_convex.inter
    ((convex_Icc d (1-d)).affine_preimage
      (certificate A B hh (cycle A B i)).height)

lemma retainedFaceHull_subset_heightTrim {d : ℝ} (hd0 : 0 ≤ d)
    (hd1 : d ≤ (1 : ℝ)/2) (i : SourceIndex A B) :
    retainedFaceHull A B hh d i ⊆
      heightTrim (certificate A B hh (cycle A B i)).domain
        (certificate A B hh (cycle A B i)).height d := by
  apply convexHull_min
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · refine ⟨faceEntryAt_mem_domain A B hh ⟨hd0, by linarith⟩ i, ?_⟩
      change d ≤ (certificate A B hh (cycle A B i)).height (faceEntryAt A B hh d i) ∧
        (certificate A B hh (cycle A B i)).height (faceEntryAt A B hh d i) ≤ 1-d
      rw [faceEntryAt_height]
      exact ⟨le_rfl, by linarith⟩
    · refine ⟨faceExitAt_mem_domain A B hh ⟨hd0, by linarith⟩ i, ?_⟩
      change d ≤ (certificate A B hh (cycle A B i)).height (faceExitAt A B hh d i) ∧
        (certificate A B hh (cycle A B i)).height (faceExitAt A B hh d i) ≤ 1-d
      rw [faceExitAt_height]
      exact ⟨le_rfl, by linarith⟩
    · refine ⟨faceExitAt_mem_domain A B hh ⟨by linarith, by linarith⟩ i, ?_⟩
      change d ≤ (certificate A B hh (cycle A B i)).height (faceExitAt A B hh (1-d) i) ∧
        (certificate A B hh (cycle A B i)).height (faceExitAt A B hh (1-d) i) ≤ 1-d
      rw [faceExitAt_height]
      exact ⟨by linarith, le_rfl⟩
    · refine ⟨faceEntryAt_mem_domain A B hh ⟨by linarith, by linarith⟩ i, ?_⟩
      change d ≤ (certificate A B hh (cycle A B i)).height (faceEntryAt A B hh (1-d) i) ∧
        (certificate A B hh (cycle A B i)).height (faceEntryAt A B hh (1-d) i) ≤ 1-d
      rw [faceEntryAt_height]
      exact ⟨by linarith, le_rfl⟩
  · exact heightTrim_convex A B hh d i

lemma heightTrim_subset_retainedFaceHull {d : ℝ} (hd0 : 0 < d)
    (hd1 : d < (1 : ℝ)/2) (i : SourceIndex A B) :
    heightTrim (certificate A B hh (cycle A B i)).domain
        (certificate A B hh (cycle A B i)).height d ⊆
      retainedFaceHull A B hh d i := by
  intro x hx
  let t := (certificate A B hh (cycle A B i)).height x
  obtain ⟨s, hs0, hsr, hxrep⟩ :=
    face_horizontal_parameter_bounds A B hh i x hx.1 rfl
  have ht0 : d ≤ t := hx.2.1
  have ht1 : t ≤ 1-d := hx.2.2
  have htI := trimParameter_mem_Icc hd0 hd1 ht0 ht1
  have ht : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_lt_of_le hd0 ht0, by linarith⟩
  have hr := retainedLowerRunCoeff_pos_of_mem_Ioo A B hh ht i
  have hsI : s / retainedLowerRunCoeff A B hh t i ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hs0 hr.le, (div_le_one hr).mpr hsr⟩
  have hp := panel_mem_hull (localB A B hh d i) (localE A B hh d i)
    (localD A B hh d i) (localRatio A B hh d i)
    (s / retainedLowerRunCoeff A B hh t i) (trimParameter d t) hsI htI
  rw [← intrinsicFaceChart_entry_add_eq_panel A B hh hd0 hd1 ht0 ht1 s i,
    ← hxrep] at hp
  rw [← intrinsicFaceChart_retainedFaceHull A B hh hd0 hd1 i] at hp
  obtain ⟨y, hy, heq⟩ := hp
  have hyx : y = x := (intrinsicFaceChart A B hh i).injective heq
  rwa [hyx] at hy

/-- The actual trimmed source facet is exactly its canonical four-vertex hull;
when a full-rim run vanishes this specializes to a triangular facet. -/
theorem heightTrim_eq_retainedFaceHull {d : ℝ} (hd0 : 0 < d)
    (hd1 : d < (1 : ℝ)/2) (i : SourceIndex A B) :
    heightTrim (certificate A B hh (cycle A B i)).domain
        (certificate A B hh (cycle A B i)).height d =
      retainedFaceHull A B hh d i := by
  apply Set.Subset.antisymm
  · exact heightTrim_subset_retainedFaceHull A B hh hd0 hd1 i
  · exact retainedFaceHull_subset_heightTrim A B hh hd0.le hd1.le i

/-- Exact source-image equality in the intrinsic physical face chart. -/
theorem intrinsicFaceChart_heightTrim_image {d : ℝ} (hd0 : 0 < d)
    (hd1 : d < (1 : ℝ)/2) (i : SourceIndex A B) :
    intrinsicFaceChart A B hh i ''
        heightTrim (certificate A B hh (cycle A B i)).domain
          (certificate A B hh (cycle A B i)).height d =
      hull (localB A B hh d i) (localE A B hh d i)
        (localD A B hh d i) (localRatio A B hh d i) := by
  rw [heightTrim_eq_retainedFaceHull A B hh hd0 hd1,
    intrinsicFaceChart_retainedFaceHull A B hh hd0 hd1]

lemma local_orientation_neg {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2)
    (i : SourceIndex A B) : MixedTurnSafeCut.det (localE A B hh d i) (localD A B hh d i) < 0 := by
  rw [localE_eq, localD_eq]
  simp [MixedTurnSafeCut.det]
  have hb := retainedLowerRunCoeff_pos A B hh hd0 hd1 i
  have hs := faceS_pos A B hh i
  have hd : 0 < 1 - 2*d := by linarith
  have hp := mul_pos hb (mul_pos hd hs)
  nlinarith

def familySource (k : Fin (MechanismN A B + 1)) : ℕ → SourceIndex A B
  | 0 => sourceIndexEquiv A B k
  | i+1 => next (familySource k i)

@[simp] lemma familySource_zero (k : Fin (MechanismN A B + 1)) :
    familySource A B k 0 = sourceIndexEquiv A B k := rfl

@[simp] lemma familySource_succ (k : Fin (MechanismN A B + 1)) (i : ℕ) :
    familySource A B k (i+1) = next (familySource A B k i) := rfl

lemma sourceIndexEquiv_next (j : Fin (MechanismN A B + 1)) :
    next (sourceIndexEquiv A B j) = sourceIndexEquiv A B (finRotate _ j) := by
  apply Fin.ext
  change (((sourceIndexEquiv A B j).val+1) % sideCount A B) =
    (sourceIndexEquiv A B (finRotate _ j)).val
  have hj : (sourceIndexEquiv A B j).val = j.val :=
    Fin.val_cast (size_restore A B) j
  have hj' : (sourceIndexEquiv A B (finRotate _ j)).val = (finRotate _ j).val :=
    Fin.val_cast (size_restore A B) (finRotate _ j)
  rw [hj, hj', finRotate_apply]
  have hval : (j+1).val = (j.val+1) % (MechanismN A B+1) := by
    rw [Fin.val_add]
    have hone : (1 : Fin (MechanismN A B+1)).val = 1 := by
      change 1 % (MechanismN A B+1) = 1
      exact Nat.mod_eq_of_lt (by
        change 1 < sideCount A B-1+1
        have hs := three_le_sideCount A B
        omega)
    rw [hone]
  rw [hval]
  exact congrArg (fun n => (j.val+1) % n) (size_restore A B).symm

lemma next_sourceIndexEquiv_add (k j : Fin (MechanismN A B + 1)) :
    next (sourceIndexEquiv A B (k+j)) = sourceIndexEquiv A B (k + finRotate _ j) := by
  rw [sourceIndexEquiv_next]
  congr 1
  calc
    finRotate _ (k+j) = (k+j)+1 := finRotate_apply _
    _ = k+(j+1) := by abel
    _ = k+finRotate _ j := congrArg (fun x => k+x) (finRotate_apply j).symm

lemma familySource_eq_add (k : Fin (MechanismN A B + 1)) (i : ℕ)
    (hi : i < MechanismN A B + 1) :
    familySource A B k i = sourceIndexEquiv A B (k + ⟨i,hi⟩) := by
  induction i with
  | zero =>
      rw [familySource_zero]
      congr 1
      apply Fin.ext
      simp
  | succ i ih =>
      rw [familySource_succ, ih (by omega), next_sourceIndexEquiv_add]
      have hj : finRotate (MechanismN A B+1) ⟨i, by omega⟩ = ⟨i+1,hi⟩ := by
        apply Fin.ext
        simp only [finRotate_apply, Fin.val_add]
        have hone : (1 : Fin (MechanismN A B+1)).val = 1 := by
          change 1 % (MechanismN A B+1) = 1
          exact Nat.mod_eq_of_lt (by
      have hs := three_le_sideCount A B
      have hr := size_restore A B
      omega)
        rw [hone]
        change (i+1) % (MechanismN A B+1) = i+1
        rw [Nat.mod_eq_of_lt hi]
      rw [hj]

lemma familySource_mechanism_add (k : Fin (MechanismN A B + 1))
    (i : Fin (MechanismN A B)) :
    familySource A B k (i.val+1) = sourceIndexEquiv A B (k + i.succ) := by
  rw [familySource_eq_add A B k (i.val+1) (by have := i.isLt; omega)]
  congr 1

noncomputable def familyHeading (k : Fin (MechanismN A B + 1)) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range i, intrinsicQ A B (hh := hh) (familySource A B k (j+1))

lemma familyHeading_zero (k : Fin (MechanismN A B + 1)) :
    familyHeading A B hh k 0 = 0 := by simp [familyHeading]

lemma familyHeading_succ (k : Fin (MechanismN A B + 1)) (i : ℕ) :
    familyHeading A B hh k (i+1) - familyHeading A B hh k i =
      intrinsicQ A B (hh := hh) (familySource A B k (i+1)) := by
  rw [familyHeading, familyHeading, Finset.sum_range_succ]
  ring

lemma familyHeading_internal (k : Fin (MechanismN A B + 1))
    (i : Fin (MechanismN A B)) :
    familyHeading A B hh k (i+1) - familyHeading A B hh k i =
      mechanismQ A B (hh := hh) (k+i.succ) := by
  rw [familyHeading_succ, mechanismQ, familySource_mechanism_add]

noncomputable def familyLength (d : ℝ) (k : Fin (MechanismN A B + 1)) (i : ℕ) : ℝ :=
  retainedLowerRunCoeff A B hh d (familySource A B k i)

noncomputable def familyRatio (d : ℝ) (k : Fin (MechanismN A B + 1)) (i : ℕ) : ℝ :=
  localRatio A B hh d (familySource A B k i)

noncomputable def familyE (d : ℝ) (k : Fin (MechanismN A B + 1)) (i : ℕ) : Plane :=
  planeRotation (familyHeading A B hh k i)
    (localE A B hh d (familySource A B k i))

noncomputable def familyD (d : ℝ) (k : Fin (MechanismN A B + 1)) (i : ℕ) : Plane :=
  planeRotation (familyHeading A B hh k i)
    (localD A B hh d (familySource A B k i))

noncomputable def familyB (d : ℝ) (k : Fin (MechanismN A B + 1)) (i : ℕ) : Plane :=
  ∑ j ∈ Finset.range i, familyE A B hh d k j

lemma familyB_succ (d : ℝ) (k : Fin (MechanismN A B + 1)) (i : ℕ) :
    familyB A B hh d k (i+1) = familyB A B hh d k i + familyE A B hh d k i := by
  rw [familyB, familyB, Finset.sum_range_succ]

/-- The trim-independent translation increment contributed by the midpoint run
of source face `k+i`. -/
noncomputable def directMidpointStep (k : Fin (MechanismN A B + 1)) (i : ℕ) : Plane :=
  planeRotation (familyHeading A B hh k i)
    (WithLp.toLp 2 ![middleLength A B hh (familySource A B k i), 0])

/-- The accumulated translation in the direct midpoint-anchored development.
This is the finite-sum form of `t(k,0)=0` and
`t(k,i+1)=t(k,i)+Rot(theta(k,i))*(ell_(k+i),0)`. -/
noncomputable def directTranslation (k : Fin (MechanismN A B + 1)) (i : ℕ) : Plane :=
  ∑ j ∈ Finset.range i, directMidpointStep A B hh k j

@[simp] lemma directTranslation_zero (k : Fin (MechanismN A B + 1)) :
    directTranslation A B hh k 0 = 0 := by
  simp [directTranslation]

lemma directTranslation_succ (k : Fin (MechanismN A B + 1)) (i : ℕ) :
    directTranslation A B hh k (i+1) = directTranslation A B hh k i +
      planeRotation (familyHeading A B hh k i)
        (WithLp.toLp 2 ![middleLength A B hh (familySource A B k i), 0]) := by
  rw [directTranslation, directTranslation, Finset.sum_range_succ]
  rfl

lemma familyE_represents (d : ℝ) (k : Fin (MechanismN A B + 1)) (i : ℕ) :
    familyE A B hh d k i = familyLength A B hh d k i •
      direction (familyHeading A B hh k i) := by
  rw [familyE, familyLength, localE_eq]
  have he : WithLp.toLp 2 ![retainedLowerRunCoeff A B hh d (familySource A B k i), 0] =
      retainedLowerRunCoeff A B hh d (familySource A B k i) • direction 0 := by
    ext z
    fin_cases z <;> simp [direction]
  rw [he, map_smul, planeRotation_direction]
  simp

lemma family_orientation_neg {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2)
    (k : Fin (MechanismN A B + 1)) (i : ℕ) :
    MixedTurnSafeCut.det (familyE A B hh d k i) (familyD A B hh d k i) < 0 := by
  rw [familyE, familyD, planeRotation_det]
  exact local_orientation_neg A B hh hd0 hd1 (familySource A B k i)

lemma familyD_succ {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2)
    (k : Fin (MechanismN A B + 1)) (i : ℕ) (_hi : i ≤ MechanismN A B) :
    familyD A B hh d k (i+1) = familyD A B hh d k i +
      (familyRatio A B hh d k i - 1) • familyE A B hh d k i := by
  have hs := familySource_succ A B k i
  have hhead := familyHeading_succ A B hh k i
  rw [hs] at hhead
  rw [familyD, familyD, familyRatio, familyE, hs]
  have hrot := planeRotation_localD_eq_prevExitD A B hh d
    (familySource A B k (i+1))
  rw [hs, prev_next] at hrot
  have hloc := local_hinge_step A B hh hd0 hd1 (familySource A B k i)
  rw [show familyHeading A B hh k (i+1) = familyHeading A B hh k i +
      intrinsicQ A B (hh := hh) (next (familySource A B k i)) by linarith]
  calc
    _ = planeRotation (familyHeading A B hh k i)
        (planeRotation (intrinsicQ A B (hh := hh) (next (familySource A B k i)))
          (localD A B hh d (next (familySource A B k i)))) := by
      rw [planeRotation_comp]
    _ = planeRotation (familyHeading A B hh k i)
        (localExitD A B hh d (familySource A B k i)) := by rw [hrot]
    _ = planeRotation (familyHeading A B hh k i)
        (localD A B hh d (familySource A B k i) +
          (localRatio A B hh d (familySource A B k i)-1) •
            localE A B hh d (familySource A B k i)) := by rw [hloc]
    _ = _ := by rw [map_add, map_smul]

lemma localB_eq_midpoint_smul_localD_zero (t : ℝ) (i : SourceIndex A B) :
    localB A B hh t i = (t - (1/2 : ℝ)) • localD A B hh 0 i := by
  rw [localB, intrinsicFaceChart_entryAt, localD_eq]
  ext z
  fin_cases z <;> simp <;> ring

lemma lineMap_eq_midpoint_add (a b : Plane) (t : ℝ) :
    AffineMap.lineMap a b t = AffineMap.lineMap a b (1/2 : ℝ) +
      (t - (1/2 : ℝ)) • (b-a) := by
  simp only [AffineMap.lineMap_apply_module]
  module

lemma intrinsicFaceChart_exitAt_eq_midpoint_add (t : ℝ) (i : SourceIndex A B) :
    intrinsicFaceChart A B hh i (faceExitAt A B hh t i) =
      WithLp.toLp 2 ![middleLength A B hh i, 0] +
        (t - (1/2 : ℝ)) • localExitD A B hh 0 i := by
  let ψ := (intrinsicFaceChart A B hh i).toAffineEquiv.toAffineMap
  have hline (s : ℝ) : intrinsicFaceChart A B hh i (faceExitAt A B hh s i) =
      AffineMap.lineMap (intrinsicFaceChart A B hh i (faceExitLower A B hh i))
        (intrinsicFaceChart A B hh i (faceExitUpper A B hh i)) s := by
    change ψ (AffineMap.lineMap _ _ s) = _
    exact ψ.apply_lineMap _ _ _
  rw [hline, lineMap_eq_midpoint_add]
  rw [← hline (1/2 : ℝ), ← intrinsicFaceChart_exitMidpoint A B hh i]
  congr 1
  rw [localExitD]
  have h0 : faceExitAt A B hh 0 i = faceExitLower A B hh i := by
    simp [faceExitAt, AffineMap.lineMap_apply_module]
  have h1 : faceExitAt A B hh (1-0) i = faceExitUpper A B hh i := by
    simp [faceExitAt, AffineMap.lineMap_apply_module]
  rw [h0, h1]

/-- The direct transition `G_i(z)=Rot(q_(i+1)) z + (ell_i,0)` identifies the
whole physical exit hinge of face `i` with the entry hinge of face `i+1`.
The statement is independent of trim and is valid for every real hinge
parameter. -/
theorem directTransition_entryAt (t : ℝ) (i : SourceIndex A B) :
    planeRotation (intrinsicQ A B (hh := hh) (next i))
        (intrinsicFaceChart A B hh (next i) (faceEntryAt A B hh t (next i))) +
      WithLp.toLp 2 ![middleLength A B hh i, 0] =
    intrinsicFaceChart A B hh i (faceExitAt A B hh t i) := by
  rw [← localB, localB_eq_midpoint_smul_localD_zero, map_smul,
    planeRotation_localD_eq_prevExitD A B hh 0 (next i), prev_next,
    intrinsicFaceChart_exitAt_eq_midpoint_add]
  abel

noncomputable def planarPlacement (θ : ℝ) (L B0 : Plane) : Plane →ᵃⁱ[ℝ] Plane :=
  (AffineIsometryEquiv.constVAdd ℝ Plane (B0 - planeRotation θ L)).toAffineIsometry.comp
    (planeRotation θ).toAffineIsometry

@[simp] lemma planarPlacement_apply (θ : ℝ) (L B0 x : Plane) :
    planarPlacement θ L B0 x = B0 + planeRotation θ (x-L) := by
  simp [planarPlacement]
  abel

noncomputable def developedMap (d : ℝ) (k : Fin (MechanismN A B + 1)) (i : ℕ) :
    FaceSpace A B h (cycle A B (familySource A B k i)) →ᵃⁱ[ℝ] Plane :=
  (planarPlacement (familyHeading A B hh k i)
      (localB A B hh d (familySource A B k i)) (familyB A B hh d k i)).comp
    (intrinsicFaceChart A B hh (familySource A B k i)).toAffineIsometry

/-- Direct source development: rotate the midpoint-anchored intrinsic chart by
`theta(k,i)` and add the recursively accumulated, trim-independent translation
`t(k,i)`.  This construction mentions neither trim depth nor safety. -/
noncomputable def directDevelopedMap (k : Fin (MechanismN A B + 1)) (i : ℕ) :
    FaceSpace A B h (cycle A B (familySource A B k i)) →ᵃⁱ[ℝ] Plane :=
  (planarPlacement (familyHeading A B hh k i) 0
      (directTranslation A B hh k i)).comp
    (intrinsicFaceChart A B hh (familySource A B k i)).toAffineIsometry

@[simp] lemma directDevelopedMap_apply (k : Fin (MechanismN A B + 1)) (i : ℕ)
    (x : FaceSpace A B h (cycle A B (familySource A B k i))) :
    directDevelopedMap A B hh k i x =
      planeRotation (familyHeading A B hh k i)
        (intrinsicFaceChart A B hh (familySource A B k i) x) +
      directTranslation A B hh k i := by
  change planarPlacement (familyHeading A B hh k i) 0
      (directTranslation A B hh k i)
      (intrinsicFaceChart A B hh (familySource A B k i) x) = _
  rw [planarPlacement_apply]
  simp
  abel

@[simp] lemma developedMap_apply (d : ℝ) (k : Fin (MechanismN A B + 1)) (i : ℕ)
    (x : FaceSpace A B h (cycle A B (familySource A B k i))) :
    developedMap A B hh d k i x = familyB A B hh d k i +
      planeRotation (familyHeading A B hh k i)
        (intrinsicFaceChart A B hh (familySource A B k i) x -
          localB A B hh d (familySource A B k i)) := by
  change planarPlacement (familyHeading A B hh k i)
      (localB A B hh d (familySource A B k i)) (familyB A B hh d k i)
        (intrinsicFaceChart A B hh (familySource A B k i) x) = _
  rw [planarPlacement_apply]

lemma familyOffset_eq_directTranslation (d : ℝ)
    (k : Fin (MechanismN A B + 1)) (i : ℕ) :
    familyB A B hh d k i -
        planeRotation (familyHeading A B hh k i)
          (localB A B hh d (familySource A B k i)) =
      directTranslation A B hh k i - localB A B hh d (familySource A B k 0) := by
  induction i with
  | zero =>
      have hzero (x : Plane) : planeRotation 0 x = x := by
        ext z
        fin_cases z <;> simp [planeRotation, planeRotationLinear]
      simp [familyB, familyHeading_zero, hzero]
  | succ i ih =>
      have hs := familySource_succ A B k i
      have hhead := familyHeading_succ A B hh k i
      have ht := directTransition_entryAt A B hh d (familySource A B k i)
      rw [← localB, ← localB_add_localE] at ht
      rw [hs] at hhead
      have hrot := congrArg (planeRotation (familyHeading A B hh k i)) ht
      rw [map_add, map_add, planeRotation_comp] at hrot
      have he :
          planeRotation (familyHeading A B hh k i)
              (localE A B hh d (familySource A B k i)) =
            planeRotation (familyHeading A B hh k i +
              intrinsicQ A B (hh := hh) (next (familySource A B k i)))
                (localB A B hh d (next (familySource A B k i))) +
              planeRotation (familyHeading A B hh k i)
                (WithLp.toLp 2 ![middleLength A B hh (familySource A B k i), 0]) -
              planeRotation (familyHeading A B hh k i)
                (localB A B hh d (familySource A B k i)) := by
        calc
          _ = (planeRotation (familyHeading A B hh k i)
                (localB A B hh d (familySource A B k i)) +
              planeRotation (familyHeading A B hh k i)
                (localE A B hh d (familySource A B k i))) -
              planeRotation (familyHeading A B hh k i)
                (localB A B hh d (familySource A B k i)) := by abel
          _ = _ := by rw [← hrot]
      rw [familyB_succ, directTranslation_succ, familyE, hs,
        show familyHeading A B hh k (i+1) = familyHeading A B hh k i +
          intrinsicQ A B (hh := hh) (next (familySource A B k i)) by linarith]
      calc
        _ = (familyB A B hh d k i -
              planeRotation (familyHeading A B hh k i)
                (localB A B hh d (familySource A B k i))) +
            planeRotation (familyHeading A B hh k i)
              (WithLp.toLp 2 ![middleLength A B hh (familySource A B k i), 0]) := by
          rw [he]
          abel
        _ = (directTranslation A B hh k i -
              localB A B hh d (familySource A B k 0)) +
            planeRotation (familyHeading A B hh k i)
              (WithLp.toLp 2 ![middleLength A B hh (familySource A B k i), 0]) := by
          rw [ih]
        _ = _ := by abel

/-- Every former depth-anchored map is the direct source map followed by one
common translation depending only on the root and the displayed trim.  In
particular all face-to-face geometry is exactly the direct construction; this
identity is used below to refactor the live layouts to `directDevelopedMap`. -/
theorem directDevelopedMap_eq_developedMap_add_root (d : ℝ)
    (k : Fin (MechanismN A B + 1)) (i : ℕ)
    (x : FaceSpace A B h (cycle A B (familySource A B k i))) :
    directDevelopedMap A B hh k i x = developedMap A B hh d k i x +
      localB A B hh d (familySource A B k 0) := by
  rw [directDevelopedMap_apply, developedMap_apply, map_sub]
  have hoff := familyOffset_eq_directTranslation A B hh d k i
  have ht : directTranslation A B hh k i =
      familyB A B hh d k i -
        planeRotation (familyHeading A B hh k i)
          (localB A B hh d (familySource A B k i)) +
        localB A B hh d (familySource A B k 0) := by
    rw [hoff]
    abel
  rw [ht]
  abel

lemma planarPlacement_hull (θ : ℝ) (L B0 e dvec : Plane) (a : ℝ) :
    planarPlacement θ L B0 '' hull L e dvec a =
      hull B0 (planeRotation θ e) (planeRotation θ dvec) a := by
  rw [hull, hull]
  change (planarPlacement θ L B0).toAffineMap ''
      convexHull ℝ {L, L+e, L+dvec+a • e, L+dvec} = _
  rw [(planarPlacement θ L B0).toAffineMap.image_convexHull]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl | rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inl (by simp [planarPlacement_apply, map_add]))
    · exact Or.inr (Or.inr (Or.inl (by
        simp [planarPlacement_apply, map_add, map_smul]
        abel)))
    · exact Or.inr (Or.inr (Or.inr (by simp [planarPlacement_apply, map_add])))
  · intro hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨L, Or.inl rfl, by simp⟩
    · exact ⟨L+e, Or.inr (Or.inl rfl), by simp [planarPlacement_apply, map_add]⟩
    · refine ⟨L+dvec+a • e, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
      simp [planarPlacement_apply, map_add, map_smul]
      abel
    · exact ⟨L+dvec, Or.inr (Or.inr (Or.inr rfl)),
        by simp [planarPlacement_apply, map_add]⟩

noncomputable def physicalDevelopedFamily {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2) :
    DevelopedFamily (MechanismN A B) where
  q := mechanismQ A B (hh := hh)
  B := familyB A B hh d
  e := familyE A B hh d
  d := familyD A B hh d
  ratio := familyRatio A B hh d
  heading := familyHeading A B hh
  length := familyLength A B hh d
  ratio_pos := by
    intro k i hi
    exact localRatio_pos A B hh hd0 hd1 (familySource A B k i)
  length_pos := by
    intro k i hi
    exact retainedLowerRunCoeff_pos A B hh hd0 hd1 (familySource A B k i)
  represents := by
    intro k i hi
    exact familyE_represents A B hh d k i
  orientation := by
    intro k
    exact Or.inr (fun i hi => family_orientation_neg A B hh hd0 hd1 k i)
  lower_step := by
    intro k i hi
    exact familyB_succ A B hh d k i
  hinge_step := by
    intro k i hi
    exact familyD_succ A B hh hd0 hd1 k i hi
  internal_step := by
    intro k i
    exact familyHeading_internal A B hh k i
  total_variation := mechanismQ_total_variation A B hh

theorem developedMap_heightTrim_image {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2)
    (k i : Fin (MechanismN A B + 1)) :
    developedMap A B hh d k i.val ''
        heightTrim (certificate A B hh (cycle A B (familySource A B k i.val))).domain
          (certificate A B hh (cycle A B (familySource A B k i.val))).height d =
      (physicalDevelopedFamily A B hh hd0 hd1).face k i := by
  change developedMap A B hh d k i.val '' _ =
    hull (familyB A B hh d k i.val) (familyE A B hh d k i.val)
      (familyD A B hh d k i.val) (familyRatio A B hh d k i.val)
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hlocal : intrinsicFaceChart A B hh (familySource A B k i.val) x ∈
        hull (localB A B hh d (familySource A B k i.val))
          (localE A B hh d (familySource A B k i.val))
          (localD A B hh d (familySource A B k i.val))
          (localRatio A B hh d (familySource A B k i.val)) := by
      rw [← intrinsicFaceChart_heightTrim_image A B hh hd0 hd1]
      exact ⟨x, hx, rfl⟩
    have hp : planarPlacement (familyHeading A B hh k i.val)
        (localB A B hh d (familySource A B k i.val)) (familyB A B hh d k i.val)
        (intrinsicFaceChart A B hh (familySource A B k i.val) x) ∈
        hull (familyB A B hh d k i.val)
          (planeRotation (familyHeading A B hh k i.val)
            (localE A B hh d (familySource A B k i.val)))
          (planeRotation (familyHeading A B hh k i.val)
            (localD A B hh d (familySource A B k i.val)))
          (localRatio A B hh d (familySource A B k i.val)) := by
      rw [← planarPlacement_hull]
      exact ⟨_, hlocal, rfl⟩
    simpa [developedMap, familyE, familyD, familyRatio] using hp
  · intro hz
    have hp : z ∈ planarPlacement (familyHeading A B hh k i.val)
        (localB A B hh d (familySource A B k i.val)) (familyB A B hh d k i.val) ''
        hull (localB A B hh d (familySource A B k i.val))
          (localE A B hh d (familySource A B k i.val))
          (localD A B hh d (familySource A B k i.val))
          (localRatio A B hh d (familySource A B k i.val)) := by
      rw [planarPlacement_hull]
      simpa [familyE, familyD, familyRatio] using hz
    obtain ⟨y, hy, hyz⟩ := hp
    rw [← intrinsicFaceChart_heightTrim_image A B hh hd0 hd1] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    refine ⟨x, hx, ?_⟩
    rw [developedMap]
    change planarPlacement _ _ _ (intrinsicFaceChart A B hh _ x) = z
    rw [hxy, hyz]

/-- Exact retained source-face image for the direct midpoint-anchored map.  The
right side is the already certified physical developed face under the single
common root translation; no face-dependent repositioning occurs. -/
theorem directDevelopedMap_heightTrim_image {d : ℝ}
    (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2)
    (k i : Fin (MechanismN A B + 1)) :
    directDevelopedMap A B hh k i.val ''
        heightTrim (certificate A B hh (cycle A B (familySource A B k i.val))).domain
          (certificate A B hh (cycle A B (familySource A B k i.val))).height d =
      (AffineIsometryEquiv.constVAdd ℝ Plane
        (localB A B hh d (familySource A B k 0))) ''
        (physicalDevelopedFamily A B hh hd0 hd1).face k i := by
  rw [← developedMap_heightTrim_image A B hh hd0 hd1 k i]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨developedMap A B hh d k i.val x, ⟨x, hx, rfl⟩, ?_⟩
    rw [directDevelopedMap_eq_developedMap_add_root A B hh d k i.val]
    simp
    abel
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    rw [directDevelopedMap_eq_developedMap_add_root A B hh d k i.val]
    simp
    abel

lemma developedMap_entryLow (d : ℝ) (k : Fin (MechanismN A B+1)) (i : ℕ) :
    developedMap A B hh d k i (faceEntryAt A B hh d (familySource A B k i)) =
      familyB A B hh d k i := by
  rw [developedMap_apply, localB]
  simp

lemma developedMap_exitLow (d : ℝ) (k : Fin (MechanismN A B+1)) (i : ℕ) :
    developedMap A B hh d k i (faceExitAt A B hh d (familySource A B k i)) =
      familyB A B hh d k (i+1) := by
  rw [developedMap_apply, familyB_succ]
  have he := localB_add_localE A B hh d (familySource A B k i)
  have hdif : intrinsicFaceChart A B hh (familySource A B k i)
      (faceExitAt A B hh d (familySource A B k i)) -
        localB A B hh d (familySource A B k i) =
      localE A B hh d (familySource A B k i) := by
    rw [← he]
    abel
  rw [hdif]
  rfl

lemma developedMap_entryHigh (d : ℝ) (k : Fin (MechanismN A B+1)) (i : ℕ) :
    developedMap A B hh d k i (faceEntryAt A B hh (1-d) (familySource A B k i)) =
      familyB A B hh d k i + familyD A B hh d k i := by
  rw [developedMap_apply]
  have he := localB_add_localD A B hh d (familySource A B k i)
  have hdif : intrinsicFaceChart A B hh (familySource A B k i)
      (faceEntryAt A B hh (1-d) (familySource A B k i)) -
        localB A B hh d (familySource A B k i) =
      localD A B hh d (familySource A B k i) := by
    rw [← he]
    abel
  rw [hdif]
  rfl

lemma developedMap_exitHigh {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2)
    (k : Fin (MechanismN A B+1)) (i : ℕ) (hi : i ≤ MechanismN A B) :
    developedMap A B hh d k i (faceExitAt A B hh (1-d) (familySource A B k i)) =
      familyB A B hh d k (i+1) + familyD A B hh d k (i+1) := by
  rw [developedMap_apply, familyB_succ,
    familyD_succ A B hh hd0 hd1 k i hi]
  have hu := local_exitUpper_vertex A B hh hd0 hd1 (familySource A B k i)
  have hdif : intrinsicFaceChart A B hh (familySource A B k i)
      (faceExitAt A B hh (1-d) (familySource A B k i)) -
        localB A B hh d (familySource A B k i) =
      localD A B hh d (familySource A B k i) +
        localRatio A B hh d (familySource A B k i) •
          localE A B hh d (familySource A B k i) := by
    rw [← hu]
    abel
  rw [hdif, map_add, map_smul]
  simp only [familyE, familyD, familyRatio]
  module

theorem developedMap_exitAt_eq_next_entryAt {d : ℝ} (hd0 : 0 < d)
    (hd1 : d < (1 : ℝ)/2) (k : Fin (MechanismN A B+1)) (i : ℕ)
    (hi : i ≤ MechanismN A B) (t : ℝ) :
    developedMap A B hh d k i (faceExitAt A B hh t (familySource A B k i)) =
      developedMap A B hh d k (i+1)
        (faceEntryAt A B hh t (familySource A B k (i+1))) := by
  have hd : d ≠ (1 : ℝ)/2 := ne_of_lt hd1
  rw [faceExitAt_eq_retained_lineMap A B hh hd,
    faceEntryAt_eq_retained_lineMap A B hh hd]
  change (developedMap A B hh d k i).toAffineMap
      (AffineMap.lineMap _ _ (trimParameter d t)) =
    (developedMap A B hh d k (i+1)).toAffineMap
      (AffineMap.lineMap _ _ (trimParameter d t))
  rw [(developedMap A B hh d k i).toAffineMap.apply_lineMap,
    (developedMap A B hh d k (i+1)).toAffineMap.apply_lineMap]
  change AffineMap.lineMap
      (developedMap A B hh d k i (faceExitAt A B hh d (familySource A B k i)))
      (developedMap A B hh d k i (faceExitAt A B hh (1-d) (familySource A B k i)))
      (trimParameter d t) =
    AffineMap.lineMap
      (developedMap A B hh d k (i+1)
        (faceEntryAt A B hh d (familySource A B k (i+1))))
      (developedMap A B hh d k (i+1)
        (faceEntryAt A B hh (1-d) (familySource A B k (i+1))))
      (trimParameter d t)
  rw [developedMap_exitLow, developedMap_entryLow,
    developedMap_exitHigh A B hh hd0 hd1 k i hi,
    developedMap_entryHigh]

theorem developedMap_glues_physical {d : ℝ} (hd0 : 0 < d)
    (hd1 : d < (1 : ℝ)/2) (k : Fin (MechanismN A B+1)) (i : ℕ)
    (hi : i ≤ MechanismN A B)
    (x : FaceSpace A B h (cycle A B (familySource A B k i)))
    (y : FaceSpace A B h (cycle A B (next (familySource A B k i))))
    (hx : x ∈ (certificate A B hh (cycle A B (familySource A B k i))).domain)
    (hy : y ∈ (certificate A B hh (cycle A B (next (familySource A B k i)))).domain)
    (hxy : (certificate A B hh (cycle A B (familySource A B k i))).chart x =
      (certificate A B hh (cycle A B (next (familySource A B k i)))).chart y) :
    developedMap A B hh d k i x = developedMap A B hh d k (i+1) y := by
  let t := (certificate A B hh (cycle A B (familySource A B k i))).height x
  have hty : (certificate A B hh (cycle A B (next (familySource A B k i)))).height y = t := by
    change heightLinear h
      ((certificate A B hh (cycle A B (next (familySource A B k i)))).chart y) = t
    rw [← hxy]
    rfl
  have hyown := (certificate A B hh
    (cycle A B (next (familySource A B k i)))).own_zero y
  change sideRow A B h (cycle A B (next (familySource A B k i))).val
    ((certificate A B hh (cycle A B (next (familySource A B k i)))).chart y) = 0 at hyown
  have hxnext : sideRow A B h (cycle A B (next (familySource A B k i))).val
      ((certificate A B hh (cycle A B (familySource A B k i))).chart x) = 0 := by
    rw [hxy]
    exact hyown
  have hxeq := face_eq_exitAt_of_nextRow_zero A B hh (familySource A B k i)
    x hx rfl hxnext
  have hxown := (certificate A B hh
    (cycle A B (familySource A B k i))).own_zero x
  change sideRow A B h (cycle A B (familySource A B k i)).val
    ((certificate A B hh (cycle A B (familySource A B k i))).chart x) = 0 at hxown
  have hyprev : sideRow A B h (cycle A B (prev (next (familySource A B k i)))).val
      ((certificate A B hh (cycle A B (next (familySource A B k i)))).chart y) = 0 := by
    rw [prev_next, ← hxy]
    exact hxown
  have hyeq := face_eq_entryAt_of_prevRow_zero A B hh (next (familySource A B k i))
    y hy hty hyprev
  rw [hxeq, hyeq]
  exact developedMap_exitAt_eq_next_entryAt A B hh hd0 hd1 k i hi t

noncomputable def fixedCutIndex (hmix : IntrinsicTMixed A B hh) :
    Fin (MechanismN A B+1) := Classical.choose (mixed_budget_selection
      (mechanismQ A B hh)
      (positiveBudget (mechanismQ A B hh)) (negativeBudget (mechanismQ A B hh))
      Real.pi (mechanismQ_total_variation A B hh)
      (intrinsicTMixed_mechanism A B hh hmix).1
      (intrinsicTMixed_mechanism A B hh hmix).2)

lemma fixedCutIndex_budgets (hmix : IntrinsicTMixed A B hh) :
    positiveBudget (mechanismQ A B hh) -
        max (mechanismQ A B hh (fixedCutIndex A B hh hmix)) 0 < Real.pi ∧
      negativeBudget (mechanismQ A B hh) -
        max (-mechanismQ A B hh (fixedCutIndex A B hh hmix)) 0 < Real.pi :=
  Classical.choose_spec (mixed_budget_selection
    (mechanismQ A B hh)
    (positiveBudget (mechanismQ A B hh)) (negativeBudget (mechanismQ A B hh))
    Real.pi (mechanismQ_total_variation A B hh)
    (intrinsicTMixed_mechanism A B hh hmix).1
    (intrinsicTMixed_mechanism A B hh hmix).2)

theorem fixedCut_nonoverlap (hmix : IntrinsicTMixed A B hh)
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2)
    (i j : Fin (MechanismN A B+1)) (hij : i ≠ j) :
    Disjoint (interior ((physicalDevelopedFamily A B hh hd0 hd1).face
      (fixedCutIndex A B hh hmix) i))
      (interior ((physicalDevelopedFamily A B hh hd0 hd1).face
        (fixedCutIndex A B hh hmix) j)) := by
  let D := physicalDevelopedFamily A B hh hd0 hd1
  obtain ⟨hp, hn⟩ := retained_variations D (fixedCutIndex A B hh hmix)
  obtain ⟨hP, hN⟩ := fixedCutIndex_budgets A B hh hmix
  apply small_variation_nonoverlap (MechanismN A B)
    (D.B (fixedCutIndex A B hh hmix)) (D.e (fixedCutIndex A B hh hmix))
    (D.d (fixedCutIndex A B hh hmix)) (D.ratio (fixedCutIndex A B hh hmix))
    (D.heading (fixedCutIndex A B hh hmix)) (D.length (fixedCutIndex A B hh hmix))
    (D.ratio_pos _) (D.length_pos _) (D.represents _) (D.orientation _)
    (D.lower_step _) (D.hinge_step _)
    (by rw [hp]; simpa [D, physicalDevelopedFamily] using hP)
    (by rw [hn]; simpa [D, physicalDevelopedFamily] using hN)
    i j (by omega) (by omega)
  exact fun heq => hij (Fin.ext heq)

theorem fixedCut_safe (hmix : IntrinsicTMixed A B hh)
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2) :
    FiniteWitnessClosure.Safe
      (fun i : Fin (MechanismN A B+1) =>
        heightTrim
          (certificate A B hh (cycle A B
            (familySource A B (fixedCutIndex A B hh hmix) i.val))).domain
          (certificate A B hh (cycle A B
            (familySource A B (fixedCutIndex A B hh hmix) i.val))).height d)
      (fun i : Fin (MechanismN A B+1) =>
        developedMap A B hh d (fixedCutIndex A B hh hmix) i.val) := by
  intro i j hij
  change Disjoint (interior (developedMap A B hh d (fixedCutIndex A B hh hmix) i.val '' _))
    (interior (developedMap A B hh d (fixedCutIndex A B hh hmix) j.val '' _))
  rw [developedMap_heightTrim_image A B hh hd0 hd1,
    developedMap_heightTrim_image A B hh hd0 hd1]
  exact fixedCut_nonoverlap A B hh hmix hd0 hd1 i j hij

theorem fixedCut_developmentOn (hmix : IntrinsicTMixed A B hh)
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2) :
    DevelopmentOn
      (fun i : Fin (MechanismN A B+1) =>
        (certificate A B hh (cycle A B
          (familySource A B (fixedCutIndex A B hh hmix) i.val))).chart.toAffineMap)
      (fun i : Fin (MechanismN A B+1) =>
        heightTrim
          (certificate A B hh (cycle A B
            (familySource A B (fixedCutIndex A B hh hmix) i.val))).domain
          (certificate A B hh (cycle A B
            (familySource A B (fixedCutIndex A B hh hmix) i.val))).height d)
      (fun i : Fin (MechanismN A B+1) =>
        developedMap A B hh d (fixedCutIndex A B hh hmix) i.val) := by
  constructor
  · intro j x hx y hy hxy
    exact developedMap_glues_physical A B hh hd0 hd1
      (fixedCutIndex A B hh hmix) j.val (by omega) x y hx.1 hy.1 hxy
  · intro j
    exact fixedCut_safe A B hh hmix hd0 hd1 j.castSucc j.succ (by
      intro he
      have := congrArg Fin.val he
      simp at this)

lemma sourceIndexEquiv_add (k i : Fin (MechanismN A B+1)) :
    sourceIndexEquiv A B (k+i) = sourceIndexEquiv A B k + sourceIndexEquiv A B i := by
  apply Fin.ext
  have hk : (sourceIndexEquiv A B k).val = k.val := Fin.val_cast (size_restore A B) k
  have hi : (sourceIndexEquiv A B i).val = i.val := Fin.val_cast (size_restore A B) i
  have hki : (sourceIndexEquiv A B (k+i)).val = (k+i).val :=
    Fin.val_cast (size_restore A B) (k+i)
  rw [hki]
  change (k+i).val =
    ((sourceIndexEquiv A B k).val + (sourceIndexEquiv A B i).val) % sideCount A B
  rw [Fin.val_add, hk, hi]
  exact congrArg (fun n => (k.val+i.val) % n) (size_restore A B)

lemma familySource_fin (k i : Fin (MechanismN A B+1)) :
    familySource A B k i.val = sourceIndexEquiv A B k + sourceIndexEquiv A B i := by
  rw [familySource_eq_add A B k i.val i.isLt]
  have he : (⟨i.val, i.isLt⟩ : Fin (MechanismN A B+1)) = i := Fin.ext rfl
  rw [he, sourceIndexEquiv_add]

lemma positions_eq_sourceIndexEquiv (j : Fin (MechanismN A B + 1)) :
    positions A B j = sourceIndexEquiv A B j := by
  apply Fin.ext
  rfl

/-- A mathematical entry cut `k` is the source exit-edge label `k-1`; the
opened order then visits exactly `F_(k+j)`. -/
theorem order_prev_apply (k : SourceIndex A B) (j : Fin (MechanismN A B + 1)) :
    order A B (prev k) j = cycle A B (k + sourceIndexEquiv A B j) := by
  change cycle A B (positions A B j + finRotate (sideCount A B) (prev k)) = _
  rw [finRotate_eq_next, next_prev, positions_eq_sourceIndexEquiv]
  congr 1
  abel

/-- Exact `k ↦ k-1` transport from mathematical entry labels to the existing
source cut convention. -/
theorem familySource_order_prev (k i : Fin (MechanismN A B+1)) :
    cycle A B (familySource A B k i.val) =
      order A B (prev (sourceIndexEquiv A B k)) i := by
  rw [familySource_fin, order_prev_apply]

def orderSource (k : Fin (MechanismN A B+1))
    (i : Fin (MechanismN A B+1)) : SourceIndex A B :=
  familySource A B k i.val

lemma order_eq_cycle_orderSource (k : Fin (MechanismN A B+1))
    (i : Fin (MechanismN A B+1)) :
    order A B (prev (sourceIndexEquiv A B k)) i =
      cycle A B (orderSource A B k i) := by
  exact (familySource_order_prev A B k i).symm

@[simp] lemma orderSource_eq_familySource (k : Fin (MechanismN A B+1))
    (i : Fin (MechanismN A B+1)) :
    orderSource A B k i = familySource A B k i.val := rfl

noncomputable def orderedDevelopedMap (hmix : IntrinsicTMixed A B hh) (d : ℝ)
    (i : Fin (MechanismN A B+1)) :
    FaceSpace A B h (cycle A B
      (orderSource A B (fixedCutIndex A B hh hmix) i)) →ᵃⁱ[ℝ] Plane :=
  (planarPlacement (familyHeading A B hh (fixedCutIndex A B hh hmix) i.val)
      (localB A B hh d (orderSource A B (fixedCutIndex A B hh hmix) i))
      (familyB A B hh d (fixedCutIndex A B hh hmix) i.val)).comp
    (intrinsicFaceChart A B hh
      (orderSource A B (fixedCutIndex A B hh hmix) i)).toAffineIsometry

/-- The selected-cut ordering of the direct midpoint-anchored source maps. -/
noncomputable def orderedDirectMap (hmix : IntrinsicTMixed A B hh)
    (i : Fin (MechanismN A B+1)) :
    FaceSpace A B h (cycle A B
      (orderSource A B (fixedCutIndex A B hh hmix) i)) →ᵃⁱ[ℝ] Plane :=
  directDevelopedMap A B hh (fixedCutIndex A B hh hmix) i.val

/-- Pointwise compatibility of the direct selected-cut maps with every former
trim-anchored ordered map.  The only discrepancy is one common translation. -/
theorem orderedDirectMap_eq_orderedDevelopedMap_add_root
    (hmix : IntrinsicTMixed A B hh) (d : ℝ)
    (i : Fin (MechanismN A B+1))
    (x : FaceSpace A B h (cycle A B
      (orderSource A B (fixedCutIndex A B hh hmix) i))) :
    orderedDirectMap A B hh hmix i x = orderedDevelopedMap A B hh hmix d i x +
      localB A B hh d
        (familySource A B (fixedCutIndex A B hh hmix) 0) := by
  exact directDevelopedMap_eq_developedMap_add_root A B hh d
    (fixedCutIndex A B hh hmix) i.val x


end Raw
end
end PhysicalMixedTurnSource
