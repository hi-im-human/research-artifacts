import GeneralTwoRimEndpoint
import PhysicalMixedTurnSourceSanityFixtures

open scoped BigOperators Classical NNReal
open Set PhysicalMixedTurnSource PhysicalMixedTurnSourceSanityFixtures
open MergedNormalPrismatoid TrimmedFacetWitnesses CyclicCutOrders
open OriginalFacetCertificates PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon PolyhedralInputBridge

namespace GeneralTwoRimFrustumSanity
noncomputable section
set_option maxHeartbeats 8000000

/-- Concentric square rims with side lengths three and one. -/
def largeSquareVertices : Fin 4 → MergedNormalPrismatoid.Plane :=
  ![WithLp.toLp 2 ![-1,-1], WithLp.toLp 2 ![-1,2],
    WithLp.toLp 2 ![2,2], WithLp.toLp 2 ![2,-1]]

def largeSquare : ReducedConvexPolygon 4 where
  vertex := largeSquareVertices
  three_le := by norm_num
  edge_ne := by
    intro i
    fin_cases i <;> norm_num [largeSquareVertices, next]
  supports := by
    intro i j
    fin_cases i <;> fin_cases j
    all_goals norm_num [largeSquareVertices, next, outwardNormal, edgeVector, rotateCW,
      inner, Fin.sum_univ_two]
  support_eq_vertices := by
    intro i j hz
    fin_cases i <;> fin_cases j
    all_goals try norm_num [largeSquareVertices, next, outwardNormal, edgeVector, rotateCW,
      inner, Fin.sum_univ_two] at hz
    all_goals norm_num [largeSquareVertices, next]

lemma largeNoStrict (i j : Fin 4) :
    ¬ NormalFanSplice.StrictAt largeSquare
      (outwardNormal unitSquare.vertex j) i := by
  fin_cases i <;> fin_cases j <;>
    norm_num [NormalFanSplice.StrictAt, largeSquare, largeSquareVertices,
      unitSquare, unitSquareVertices, outwardNormal, edgeVector, next, prev, rotateCW,
      back, ahead, inner, Fin.sum_univ_two]

lemma largeKnots (i : Fin 4) :
    NormalFanSplice.knots largeSquare unitSquare i = {0, 1} := by
  ext t
  simp [NormalFanSplice.knots, largeNoStrict]

lemma largeNormalBlend (i : Fin 4) (t : ℝ) :
    CommonSupportMerge.normalBlend largeSquare i t =
      (3 : ℝ) • CommonSupportMerge.normalBlend unitSquare i t := by
  fin_cases i
  all_goals ext z
  all_goals fin_cases z <;>
    simp [CommonSupportMerge.normalBlend, largeSquare, largeSquareVertices,
      unitSquare, unitSquareVertices, outwardNormal, edgeVector, next, prev,
      rotateCW] <;> ring

lemma largeGapB (g : NormalFanSplice.Gap largeSquare unitSquare) :
    MaximalSupportCells.gapB largeSquare unitSquare g = g.1 := by
  let t := MaximalSupportCells.mid largeSquare unitSquare g
  have ht := MaximalSupportCells.mid_mem largeSquare unitSquare g
  have hs := (MaximalSupportCells.gapB_spec largeSquare unitSquare g).2 t ht
  have hcon := NormalFanSplice.gap_consecutive largeSquare unitSquare g
  have hl := NormalFanSplice.knots_subset_Icc largeSquare unitSquare g.1 hcon.1
  have hr := NormalFanSplice.knots_subset_Icc largeSquare unitSquare g.1 hcon.2.1
  have ht01 : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt hl.1 ht.1,
    lt_of_lt_of_le ht.2 hr.2⟩
  have hstrictB : NormalFanSplice.StrictAt unitSquare
      (CommonSupportMerge.normalBlend largeSquare g.1 t) g.1 := by
    rw [largeNormalBlend]
    have hb := NormalFanSplice.blend_strict unitSquare g.1 ht01
    simp only [NormalFanSplice.StrictAt, real_inner_smul_left] at hb ⊢
    constructor <;> nlinarith [hb.1, hb.2]
  have hface := NormalFanSplice.supportFace_of_strict unitSquare g.1 _ hstrictB
  have hv : unitSquare.vertex (MaximalSupportCells.gapB largeSquare unitSquare g) =
      unitSquare.vertex g.1 := by
    have hm : unitSquare.vertex
        (MaximalSupportCells.gapB largeSquare unitSquare g) ∈
        ({unitSquare.vertex g.1} : Set MergedNormalPrismatoid.Plane) := by
      rw [← hface, hs.2]
      simp
    simpa using hm
  exact NormalFanSplice.raw_vertex_injective unitSquare hv

noncomputable def sourceAtGap
    (g : NormalFanSplice.Gap largeSquare unitSquare) :
    SourceIndex largeSquare unitSquare :=
  next ((NormalFanSplice.orderedGaps largeSquare unitSquare).symm (toLex g))

lemma sourceAtGap_entry (g : NormalFanSplice.Gap largeSquare unitSquare) :
    entryGap largeSquare unitSquare (sourceAtGap g) = g := by
  rw [entryGap, sourceAtGap, NormalFanSplice.prev_next]
  change ofLex (NormalFanSplice.orderedGaps largeSquare unitSquare
    ((NormalFanSplice.orderedGaps largeSquare unitSquare).symm (toLex g))) = g
  rw [(NormalFanSplice.orderedGaps largeSquare unitSquare).apply_symm_apply,
    ofLex_toLex]

lemma sourceAtGap_next_entry (g : NormalFanSplice.Gap largeSquare unitSquare) :
    entryGap largeSquare unitSquare (next (sourceAtGap g)) =
      CyclicCutOrders.nextGap largeSquare unitSquare g := by
  rw [entryGap, NormalFanSplice.prev_next, sourceAtGap]
  change ofLex (NormalFanSplice.orderedGaps largeSquare unitSquare
      (next ((NormalFanSplice.orderedGaps largeSquare unitSquare).symm (toLex g)))) = _
  rw [← finRotate_eq_next]
  have hs := CyclicCutOrders.ordered_successor
    (CyclicCutOrders.sizes largeSquare unitSquare)
    (CyclicCutOrders.sizes_pos largeSquare unitSquare)
    (le_trans (by norm_num) (three_le_sideCount largeSquare unitSquare))
    (NormalFanSplice.orderedGaps largeSquare unitSquare)
    ((NormalFanSplice.orderedGaps largeSquare unitSquare).symm (toLex g))
  rw [hs, (NormalFanSplice.orderedGaps largeSquare unitSquare).apply_symm_apply]
  rfl

lemma large_nextGap_zero (i : Fin 4) :
    CyclicCutOrders.nextGap largeSquare unitSquare
      (NormalFanSplice.zeroGap largeSquare unitSquare i) =
      NormalFanSplice.zeroGap largeSquare unitSquare (next i) := by
  unfold CyclicCutOrders.nextGap CyclicCutOrders.blockNext
  rw [dif_neg (by simp [CyclicCutOrders.sizes, largeKnots])]
  apply Sigma.ext
  · rfl
  · exact heq_of_eq (Fin.ext rfl)

lemma entryGap_injective : Function.Injective
    (entryGap largeSquare unitSquare) := by
  intro i j hij
  unfold entryGap at hij
  have hp := (NormalFanSplice.orderedGaps largeSquare unitSquare).injective hij
  have hn := congrArg next hp
  rw [PolygonSupportCompleteness.next_prev, PolygonSupportCompleteness.next_prev] at hn
  exact hn

lemma sourceAtGap_next (g : NormalFanSplice.Gap largeSquare unitSquare) :
    sourceAtGap (CyclicCutOrders.nextGap largeSquare unitSquare g) =
      next (sourceAtGap g) := by
  apply entryGap_injective
  rw [sourceAtGap_entry, sourceAtGap_next_entry]

lemma largeMiddleStep (i : Fin 4) :
    middleStep largeSquare unitSquare (by norm_num : (0:ℝ)<1)
      (sourceAtGap (NormalFanSplice.zeroGap largeSquare unitSquare i)) =
      (2 : ℝ) • squareStep3 i := by
  unfold middleStep PhysicalMixedTurnSource.midpoint lowerEndpoint upperEndpoint
  rw [sourceAtGap_entry, sourceAtGap_next_entry, large_nextGap_zero]
  rw [largeGapB, largeGapB]
  fin_cases i
  all_goals ext z
  all_goals fin_cases z <;>
    norm_num [EuclideanPrismatoidCoordinates.pack,
      MergedNormalPrismatoid.lowerLift, MergedNormalPrismatoid.upperLift,
      unitSquare, unitSquareVertices, largeSquare, largeSquareVertices, squareStep3, NormalFanSplice.zeroGap, next]

lemma largeMiddleDirection (i : Fin 4) :
    middleDirection largeSquare unitSquare (by norm_num : (0:ℝ)<1)
      (sourceAtGap (NormalFanSplice.zeroGap largeSquare unitSquare i)) =
      squareStep3 i := by
  rw [middleDirection, middleLength, largeMiddleStep]
  have hn : ‖squareStep3 i‖ = 1 := by
    fin_cases i <;>
      simp [squareStep3, EuclideanSpace.norm_eq, inner, Fin.sum_univ_three]
  simp [norm_smul, hn, smul_smul]

lemma sourceAtGap_prev_nextZero (i : Fin 4) :
    prev (sourceAtGap (NormalFanSplice.zeroGap largeSquare unitSquare (next i))) =
      sourceAtGap (NormalFanSplice.zeroGap largeSquare unitSquare i) := by
  rw [← large_nextGap_zero, sourceAtGap_next, NormalFanSplice.prev_next]

def frustumHinge : Fin 4 → EuclideanPrismatoidCoordinates.PhysicalAmbient :=
  ![WithLp.toLp 2 ![-1,-1,1], WithLp.toLp 2 ![-1,1,1],
    WithLp.toLp 2 ![1,1,1], WithLp.toLp 2 ![1,-1,1]]

lemma hinge_at (i : Fin 4) :
    hingeVector largeSquare unitSquare (by norm_num : (0:ℝ)<1)
      (sourceAtGap (NormalFanSplice.zeroGap largeSquare unitSquare i)) =
      frustumHinge i := by
  rw [hingeVector, upperEndpoint, lowerEndpoint, sourceAtGap_entry, largeGapB]
  fin_cases i
  all_goals ext z
  all_goals fin_cases z <;>
    norm_num [EuclideanPrismatoidCoordinates.pack,
      MergedNormalPrismatoid.lowerLift, MergedNormalPrismatoid.upperLift,
      largeSquare, largeSquareVertices, unitSquare, unitSquareVertices,
      frustumHinge, NormalFanSplice.zeroGap]

lemma q_pos_at (i : Fin 4) :
    0 < intrinsicQ largeSquare unitSquare (hh := (by norm_num : (0:ℝ)<1))
      (sourceAtGap (NormalFanSplice.zeroGap largeSquare unitSquare i)) := by
  have hp : prev (sourceAtGap (NormalFanSplice.zeroGap largeSquare unitSquare i)) =
      sourceAtGap (NormalFanSplice.zeroGap largeSquare unitSquare (prev i)) := by
    simpa only [PolygonSupportCompleteness.next_prev] using
      sourceAtGap_prev_nextZero (prev i)
  rw [intrinsicQ, hp, largeMiddleDirection, largeMiddleDirection, hinge_at]
  have hc : Real.pi / 2 < InnerProductGeometry.angle (squareStep3 i) (frustumHinge i) :=
    InnerProductGeometry.inner_neg_iff_pi_div_two_lt_angle.mp (by
      fin_cases i <;> norm_num [squareStep3, frustumHinge, inner, Fin.sum_univ_three])
  have hp' : InnerProductGeometry.angle (squareStep3 (prev i)) (frustumHinge i) < Real.pi / 2 := by
    apply lt_of_not_ge
    intro hge
    have hn := InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.mpr hge
    fin_cases i <;> norm_num [squareStep3, frustumHinge, prev, inner, Fin.sum_univ_three] at hn
  linarith

lemma q_pos (i : SourceIndex largeSquare unitSquare) :
    0 < intrinsicQ largeSquare unitSquare (hh := (by norm_num : (0:ℝ)<1)) i := by
  let g := entryGap largeSquare unitSquare i
  have hg : g = NormalFanSplice.zeroGap largeSquare unitSquare g.1 := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Fin.ext
      have hi := g.2.isLt
      simp only [largeKnots] at hi
      norm_num at hi
      change g.2.val = 0
      omega
  have hi : sourceAtGap (NormalFanSplice.zeroGap largeSquare unitSquare g.1) = i := by
    apply entryGap_injective
    rw [sourceAtGap_entry]
    exact hg.symm
  rw [← hi]
  exact q_pos_at g.1

theorem frustum_delta_pos :
    0 < intrinsicDelta largeSquare unitSquare (hh := (by norm_num : (0:ℝ)<1)) := by
  apply Finset.sum_pos'
  · intro i _
    exact (q_pos i).le
  · exact ⟨0, Finset.mem_univ _, q_pos 0⟩

/-- This genuine source lies outside the old shifted-mixed class. -/
theorem frustum_not_tmixed :
    ¬ IntrinsicTMixed largeSquare unitSquare (by norm_num : (0:ℝ)<1) := by
  intro hm
  obtain ⟨i, hi⟩ := ((intrinsicTMixed_iff_sum_between_values largeSquare unitSquare
    (by norm_num : (0:ℝ)<1)).mp hm).2
  have hsum : 0 < ∑ j ∈ Finset.univ.erase i,
      intrinsicQ largeSquare unitSquare (hh := (by norm_num : (0:ℝ)<1)) j := by
    apply Finset.sum_pos'
    · intro j _
      exact (q_pos j).le
    · refine ⟨next i, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, q_pos (next i)⟩
      exact PolygonSupportCompleteness.next_ne
        (le_trans (by norm_num) (three_le_sideCount largeSquare unitSquare)) i
  have he := Finset.sum_erase_add (s := Finset.univ)
    (f := intrinsicQ largeSquare unitSquare (hh := (by norm_num : (0:ℝ)<1)))
    (Finset.mem_univ i)
  change (∑ j, intrinsicQ largeSquare unitSquare (hh := (by norm_num : (0:ℝ)<1)) j) ≤ _ at hi
  linarith

/-- A checked physical example requiring the new nonzero branch. -/
theorem frustum_general :
    Nonempty (GeneralTwoRimUnfolding.SameCutSameMapsResult largeSquare unitSquare
      (by norm_num : (0:ℝ)<1)) :=
  GeneralTwoRimUnfolding.exists_sameCutSameMaps largeSquare unitSquare (by norm_num)

/-- The same concrete source directly inhabits the new positive branch. -/
theorem frustum_selected_positive :
    Nonempty (GeneralTwoRimUnfolding.SameCutSameMapsResult largeSquare unitSquare
      (by norm_num : (0:ℝ)<1)) :=
  ⟨GeneralTwoRimUnfolding.selectedPositiveSameCutSameMaps largeSquare unitSquare
    (by norm_num) frustum_delta_pos⟩

end
end GeneralTwoRimFrustumSanity

#print axioms GeneralTwoRimFrustumSanity.frustum_delta_pos
#print axioms GeneralTwoRimFrustumSanity.frustum_not_tmixed
#print axioms GeneralTwoRimFrustumSanity.frustum_general
#print axioms GeneralTwoRimFrustumSanity.frustum_selected_positive
