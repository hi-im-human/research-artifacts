import GeneralTwoRimFrustumSanity

open scoped BigOperators Classical NNReal
open Set PhysicalMixedTurnSource PhysicalMixedTurnSourceSanityFixtures
open GeneralTwoRimFrustumSanity
open MergedNormalPrismatoid TrimmedFacetWitnesses CyclicCutOrders
open OriginalFacetCertificates PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon PolyhedralInputBridge

namespace GeneralTwoRimReversedFrustumSanity
noncomputable section
set_option maxHeartbeats 8000000

lemma largeNoStrict (i j : Fin 4) :
    ¬ NormalFanSplice.StrictAt unitSquare
      (outwardNormal largeSquare.vertex j) i := by
  fin_cases i <;> fin_cases j <;>
    norm_num [NormalFanSplice.StrictAt, unitSquare, unitSquareVertices,
      largeSquare, largeSquareVertices, outwardNormal, edgeVector, next, prev, rotateCW,
      back, ahead, inner, Fin.sum_univ_two]

lemma largeKnots (i : Fin 4) :
    NormalFanSplice.knots unitSquare largeSquare i = {0, 1} := by
  ext t
  simp [NormalFanSplice.knots, largeNoStrict]

lemma largeNormalBlend (i : Fin 4) (t : ℝ) :
    CommonSupportMerge.normalBlend unitSquare i t =
      ((1 : ℝ) / 3) • CommonSupportMerge.normalBlend largeSquare i t := by
  fin_cases i
  all_goals ext z
  all_goals fin_cases z <;>
    simp [CommonSupportMerge.normalBlend, unitSquare, unitSquareVertices,
      largeSquare, largeSquareVertices, outwardNormal, edgeVector, next, prev,
      rotateCW] <;> ring

lemma largeGapB (g : NormalFanSplice.Gap unitSquare largeSquare) :
    MaximalSupportCells.gapB unitSquare largeSquare g = g.1 := by
  let t := MaximalSupportCells.mid unitSquare largeSquare g
  have ht := MaximalSupportCells.mid_mem unitSquare largeSquare g
  have hs := (MaximalSupportCells.gapB_spec unitSquare largeSquare g).2 t ht
  have hcon := NormalFanSplice.gap_consecutive unitSquare largeSquare g
  have hl := NormalFanSplice.knots_subset_Icc unitSquare largeSquare g.1 hcon.1
  have hr := NormalFanSplice.knots_subset_Icc unitSquare largeSquare g.1 hcon.2.1
  have ht01 : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt hl.1 ht.1,
    lt_of_lt_of_le ht.2 hr.2⟩
  have hstrictB : NormalFanSplice.StrictAt largeSquare
      (CommonSupportMerge.normalBlend unitSquare g.1 t) g.1 := by
    rw [largeNormalBlend]
    have hb := NormalFanSplice.blend_strict largeSquare g.1 ht01
    simp only [NormalFanSplice.StrictAt, real_inner_smul_left] at hb ⊢
    constructor <;> nlinarith [hb.1, hb.2]
  have hface := NormalFanSplice.supportFace_of_strict largeSquare g.1 _ hstrictB
  have hv : largeSquare.vertex (MaximalSupportCells.gapB unitSquare largeSquare g) =
      largeSquare.vertex g.1 := by
    have hm : largeSquare.vertex
        (MaximalSupportCells.gapB unitSquare largeSquare g) ∈
        ({largeSquare.vertex g.1} : Set MergedNormalPrismatoid.Plane) := by
      rw [← hface, hs.2]
      simp
    simpa using hm
  exact NormalFanSplice.raw_vertex_injective largeSquare hv

noncomputable def sourceAtGap
    (g : NormalFanSplice.Gap unitSquare largeSquare) :
    SourceIndex unitSquare largeSquare :=
  next ((NormalFanSplice.orderedGaps unitSquare largeSquare).symm (toLex g))

lemma sourceAtGap_entry (g : NormalFanSplice.Gap unitSquare largeSquare) :
    entryGap unitSquare largeSquare (sourceAtGap g) = g := by
  rw [entryGap, sourceAtGap, NormalFanSplice.prev_next]
  change ofLex (NormalFanSplice.orderedGaps unitSquare largeSquare
    ((NormalFanSplice.orderedGaps unitSquare largeSquare).symm (toLex g))) = g
  rw [(NormalFanSplice.orderedGaps unitSquare largeSquare).apply_symm_apply,
    ofLex_toLex]

lemma sourceAtGap_next_entry (g : NormalFanSplice.Gap unitSquare largeSquare) :
    entryGap unitSquare largeSquare (next (sourceAtGap g)) =
      CyclicCutOrders.nextGap unitSquare largeSquare g := by
  rw [entryGap, NormalFanSplice.prev_next, sourceAtGap]
  change ofLex (NormalFanSplice.orderedGaps unitSquare largeSquare
      (next ((NormalFanSplice.orderedGaps unitSquare largeSquare).symm (toLex g)))) = _
  rw [← finRotate_eq_next]
  have hs := CyclicCutOrders.ordered_successor
    (CyclicCutOrders.sizes unitSquare largeSquare)
    (CyclicCutOrders.sizes_pos unitSquare largeSquare)
    (le_trans (by norm_num) (three_le_sideCount unitSquare largeSquare))
    (NormalFanSplice.orderedGaps unitSquare largeSquare)
    ((NormalFanSplice.orderedGaps unitSquare largeSquare).symm (toLex g))
  rw [hs, (NormalFanSplice.orderedGaps unitSquare largeSquare).apply_symm_apply]
  rfl

lemma large_nextGap_zero (i : Fin 4) :
    CyclicCutOrders.nextGap unitSquare largeSquare
      (NormalFanSplice.zeroGap unitSquare largeSquare i) =
      NormalFanSplice.zeroGap unitSquare largeSquare (next i) := by
  unfold CyclicCutOrders.nextGap CyclicCutOrders.blockNext
  rw [dif_neg (by simp [CyclicCutOrders.sizes, largeKnots])]
  apply Sigma.ext
  · rfl
  · exact heq_of_eq (Fin.ext rfl)

lemma entryGap_injective : Function.Injective
    (entryGap unitSquare largeSquare) := by
  intro i j hij
  unfold entryGap at hij
  have hp := (NormalFanSplice.orderedGaps unitSquare largeSquare).injective hij
  have hn := congrArg next hp
  rw [PolygonSupportCompleteness.next_prev, PolygonSupportCompleteness.next_prev] at hn
  exact hn

lemma sourceAtGap_next (g : NormalFanSplice.Gap unitSquare largeSquare) :
    sourceAtGap (CyclicCutOrders.nextGap unitSquare largeSquare g) =
      next (sourceAtGap g) := by
  apply entryGap_injective
  rw [sourceAtGap_entry, sourceAtGap_next_entry]

lemma largeMiddleStep (i : Fin 4) :
    middleStep unitSquare largeSquare (by norm_num : (0:ℝ)<1)
      (sourceAtGap (NormalFanSplice.zeroGap unitSquare largeSquare i)) =
      (2 : ℝ) • squareStep3 i := by
  unfold middleStep PhysicalMixedTurnSource.midpoint lowerEndpoint upperEndpoint
  rw [sourceAtGap_entry, sourceAtGap_next_entry, large_nextGap_zero]
  rw [largeGapB, largeGapB]
  fin_cases i
  all_goals ext z
  all_goals fin_cases z <;>
    norm_num [EuclideanPrismatoidCoordinates.pack,
      MergedNormalPrismatoid.lowerLift, MergedNormalPrismatoid.upperLift,
      largeSquare, largeSquareVertices, unitSquare, unitSquareVertices, squareStep3, NormalFanSplice.zeroGap, next]

lemma largeMiddleDirection (i : Fin 4) :
    middleDirection unitSquare largeSquare (by norm_num : (0:ℝ)<1)
      (sourceAtGap (NormalFanSplice.zeroGap unitSquare largeSquare i)) =
      squareStep3 i := by
  rw [middleDirection, middleLength, largeMiddleStep]
  have hn : ‖squareStep3 i‖ = 1 := by
    fin_cases i <;>
      simp [squareStep3, EuclideanSpace.norm_eq, inner, Fin.sum_univ_three]
  simp [norm_smul, hn, smul_smul]

lemma sourceAtGap_prev_nextZero (i : Fin 4) :
    prev (sourceAtGap (NormalFanSplice.zeroGap unitSquare largeSquare (next i))) =
      sourceAtGap (NormalFanSplice.zeroGap unitSquare largeSquare i) := by
  rw [← large_nextGap_zero, sourceAtGap_next, NormalFanSplice.prev_next]

def frustumHinge : Fin 4 → EuclideanPrismatoidCoordinates.PhysicalAmbient :=
  ![WithLp.toLp 2 ![1,1,1], WithLp.toLp 2 ![1,-1,1],
    WithLp.toLp 2 ![-1,-1,1], WithLp.toLp 2 ![-1,1,1]]

lemma hinge_at (i : Fin 4) :
    hingeVector unitSquare largeSquare (by norm_num : (0:ℝ)<1)
      (sourceAtGap (NormalFanSplice.zeroGap unitSquare largeSquare i)) =
      frustumHinge i := by
  rw [hingeVector, upperEndpoint, lowerEndpoint, sourceAtGap_entry, largeGapB]
  fin_cases i
  all_goals ext z
  all_goals fin_cases z <;>
    norm_num [EuclideanPrismatoidCoordinates.pack,
      MergedNormalPrismatoid.lowerLift, MergedNormalPrismatoid.upperLift,
      unitSquare, unitSquareVertices, largeSquare, largeSquareVertices,
      frustumHinge, NormalFanSplice.zeroGap]

lemma q_neg_at (i : Fin 4) :
    intrinsicQ unitSquare largeSquare (hh := (by norm_num : (0:ℝ)<1))
      (sourceAtGap (NormalFanSplice.zeroGap unitSquare largeSquare i)) < 0 := by
  have hp : prev (sourceAtGap (NormalFanSplice.zeroGap unitSquare largeSquare i)) =
      sourceAtGap (NormalFanSplice.zeroGap unitSquare largeSquare (prev i)) := by
    simpa only [PolygonSupportCompleteness.next_prev] using
      sourceAtGap_prev_nextZero (prev i)
  rw [intrinsicQ, hp, largeMiddleDirection, largeMiddleDirection, hinge_at]
  have hc : InnerProductGeometry.angle (squareStep3 i) (frustumHinge i) < Real.pi / 2 := by
    apply lt_of_not_ge
    intro hge
    have hn := InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.mpr hge
    fin_cases i <;> norm_num [squareStep3, frustumHinge, inner, Fin.sum_univ_three] at hn
  have hp' : Real.pi / 2 < InnerProductGeometry.angle (squareStep3 (prev i)) (frustumHinge i) :=
    InnerProductGeometry.inner_neg_iff_pi_div_two_lt_angle.mp (by
      fin_cases i <;> norm_num [squareStep3, frustumHinge, prev, inner, Fin.sum_univ_three])
  linarith

lemma q_neg (i : SourceIndex unitSquare largeSquare) :
    intrinsicQ unitSquare largeSquare (hh := (by norm_num : (0:ℝ)<1)) i < 0 := by
  let g := entryGap unitSquare largeSquare i
  have hg : g = NormalFanSplice.zeroGap unitSquare largeSquare g.1 := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Fin.ext
      have hi := g.2.isLt
      simp only [largeKnots] at hi
      norm_num at hi
      change g.2.val = 0
      omega
  have hi : sourceAtGap (NormalFanSplice.zeroGap unitSquare largeSquare g.1) = i := by
    apply entryGap_injective
    rw [sourceAtGap_entry]
    exact hg.symm
  rw [← hi]
  exact q_neg_at g.1

theorem frustum_delta_neg :
    intrinsicDelta unitSquare largeSquare (hh := (by norm_num : (0:ℝ)<1)) < 0 := by
  have hp : 0 < ∑ i, -intrinsicQ unitSquare largeSquare (hh := (by norm_num : (0:ℝ)<1)) i := by
    apply Finset.sum_pos'
    · intro i _
      exact (neg_pos.mpr (q_neg i)).le
    · exact ⟨0, Finset.mem_univ _, neg_pos.mpr (q_neg 0)⟩
  rw [Finset.sum_neg_distrib] at hp
  change (∑ i, intrinsicQ unitSquare largeSquare (hh := (by norm_num : (0:ℝ)<1)) i) < 0
  linarith

theorem frustum_not_tmixed :
    ¬ IntrinsicTMixed unitSquare largeSquare (by norm_num : (0:ℝ)<1) := by
  intro hm
  obtain ⟨i, hi⟩ := ((intrinsicTMixed_iff_sum_between_values unitSquare largeSquare
    (by norm_num : (0:ℝ)<1)).mp hm).1
  have hsum : 0 < ∑ j ∈ Finset.univ.erase i,
      -intrinsicQ unitSquare largeSquare (hh := (by norm_num : (0:ℝ)<1)) j := by
    apply Finset.sum_pos'
    · intro j _
      exact (neg_pos.mpr (q_neg j)).le
    · refine ⟨next i, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, neg_pos.mpr (q_neg (next i))⟩
      exact PolygonSupportCompleteness.next_ne
        (le_trans (by norm_num) (three_le_sideCount unitSquare largeSquare)) i
  rw [Finset.sum_neg_distrib] at hsum
  have he := Finset.sum_erase_add (s := Finset.univ)
    (f := intrinsicQ unitSquare largeSquare (hh := (by norm_num : (0:ℝ)<1)))
    (Finset.mem_univ i)
  change _ ≤ (∑ j, intrinsicQ unitSquare largeSquare (hh := (by norm_num : (0:ℝ)<1)) j) at hi
  linarith

theorem frustum_general :
    Nonempty (GeneralTwoRimUnfolding.SameCutSameMapsResult unitSquare largeSquare
      (by norm_num : (0:ℝ)<1)) :=
  GeneralTwoRimUnfolding.exists_sameCutSameMaps unitSquare largeSquare (by norm_num)

theorem frustum_selected_negative :
    Nonempty (GeneralTwoRimUnfolding.SameCutSameMapsResult unitSquare largeSquare
      (by norm_num : (0:ℝ)<1)) :=
  ⟨GeneralTwoRimUnfolding.negativeSameCutSameMaps unitSquare largeSquare
    (by norm_num) frustum_delta_neg⟩

end
end GeneralTwoRimReversedFrustumSanity

#print axioms GeneralTwoRimReversedFrustumSanity.frustum_delta_neg
#print axioms GeneralTwoRimReversedFrustumSanity.frustum_not_tmixed
#print axioms GeneralTwoRimReversedFrustumSanity.frustum_general
#print axioms GeneralTwoRimReversedFrustumSanity.frustum_selected_negative
