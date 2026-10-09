import PhysicalMixedTurnBridge
import CyclicCutOrdersSanity

/-! Exact actual-source fixtures for the final physical mixed-turn acceptance checks. -/

open scoped BigOperators Classical NNReal
open PhysicalMixedTurnSource
open MergedNormalPrismatoid CyclicCutOrdersSanity
open TrimmedFacetWitnesses CyclicCutOrders
open OriginalFacetCertificates PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon PolyhedralInputBridge

namespace PhysicalMixedTurnSourceSanityFixtures
noncomputable section

def unitSquareVertices : Fin 4 → MergedNormalPrismatoid.Plane :=
  ![WithLp.toLp 2 ![0,0], WithLp.toLp 2 ![0,1],
    WithLp.toLp 2 ![1,1], WithLp.toLp 2 ![1,0]]

def shiftedSquareVertices : Fin 4 → MergedNormalPrismatoid.Plane :=
  ![WithLp.toLp 2 ![1,0], WithLp.toLp 2 ![1,1],
    WithLp.toLp 2 ![2,1], WithLp.toLp 2 ![2,0]]

def unitSquare : ReducedConvexPolygon 4 where
  vertex := unitSquareVertices
  three_le := by norm_num
  edge_ne := by
    intro i
    fin_cases i <;> norm_num [unitSquareVertices, next]
  supports := by
    intro i j
    fin_cases i <;> fin_cases j
    all_goals norm_num [unitSquareVertices, next, outwardNormal, edgeVector, rotateCW,
      inner, Fin.sum_univ_two]
  support_eq_vertices := by
    intro i j hz
    fin_cases i <;> fin_cases j
    all_goals try norm_num [unitSquareVertices, next, outwardNormal, edgeVector, rotateCW,
      inner, Fin.sum_univ_two] at hz
    all_goals norm_num [unitSquareVertices, next]

def shiftedSquare : ReducedConvexPolygon 4 where
  vertex := shiftedSquareVertices
  three_le := by norm_num
  edge_ne := by
    intro i
    fin_cases i <;> norm_num [shiftedSquareVertices, next]
  supports := by
    intro i j
    fin_cases i <;> fin_cases j
    all_goals norm_num [shiftedSquareVertices, next, outwardNormal, edgeVector, rotateCW,
      inner, Fin.sum_univ_two]
  support_eq_vertices := by
    intro i j hz
    fin_cases i <;> fin_cases j
    all_goals try norm_num [shiftedSquareVertices, next, outwardNormal, edgeVector, rotateCW,
      inner, Fin.sum_univ_two] at hz
    all_goals norm_num [shiftedSquareVertices, next]

lemma unitNoStrict (i j : Fin 4) :
    ¬ NormalFanSplice.StrictAt unitSquare
      (outwardNormal unitSquare.vertex j) i := by
  fin_cases i <;> fin_cases j <;>
    norm_num [NormalFanSplice.StrictAt, unitSquare, unitSquareVertices,
      outwardNormal, edgeVector, next, prev, rotateCW, back, ahead, inner,
      Fin.sum_univ_two]

lemma shiftedNoStrict (i j : Fin 4) :
    ¬ NormalFanSplice.StrictAt shiftedSquare
      (outwardNormal unitSquare.vertex j) i := by
  fin_cases i <;> fin_cases j <;>
    norm_num [NormalFanSplice.StrictAt, shiftedSquare, shiftedSquareVertices,
      unitSquare, unitSquareVertices, outwardNormal, edgeVector, next, prev, rotateCW,
      back, ahead, inner, Fin.sum_univ_two]

lemma unitKnots (i : Fin 4) :
    NormalFanSplice.knots unitSquare unitSquare i = {0, 1} := by
  ext t
  simp [NormalFanSplice.knots, unitNoStrict]

lemma shiftedKnots (i : Fin 4) :
    NormalFanSplice.knots shiftedSquare unitSquare i = {0, 1} := by
  ext t
  simp [NormalFanSplice.knots, shiftedNoStrict]

lemma rightPrism_sideCount : sideCount unitSquare unitSquare = 4 := by
  simp [sideCount, NormalFanSplice.OrderedGap, unitKnots]

lemma obliquePrism_sideCount : sideCount shiftedSquare unitSquare = 4 := by
  simp [sideCount, NormalFanSplice.OrderedGap, shiftedKnots]

lemma shiftedNormalBlend (i : Fin 4) (t : ℝ) :
    CommonSupportMerge.normalBlend shiftedSquare i t =
      CommonSupportMerge.normalBlend unitSquare i t := by
  fin_cases i
  all_goals ext z
  all_goals fin_cases z <;>
    simp [CommonSupportMerge.normalBlend, shiftedSquare, shiftedSquareVertices,
      unitSquare, unitSquareVertices, outwardNormal, edgeVector, next, prev,
      rotateCW] <;> ring

lemma shiftedVertex (i : Fin 4) :
    shiftedSquare.vertex i = unitSquare.vertex i + WithLp.toLp 2 ![1, 0] := by
  fin_cases i
  all_goals ext z
  all_goals fin_cases z <;>
    norm_num [shiftedSquare, shiftedSquareVertices, unitSquare, unitSquareVertices]

lemma shiftedGapB (g : NormalFanSplice.Gap shiftedSquare unitSquare) :
    MaximalSupportCells.gapB shiftedSquare unitSquare g = g.1 := by
  let t := MaximalSupportCells.mid shiftedSquare unitSquare g
  have ht := MaximalSupportCells.mid_mem shiftedSquare unitSquare g
  have hs := (MaximalSupportCells.gapB_spec shiftedSquare unitSquare g).2 t ht
  have hcon := NormalFanSplice.gap_consecutive shiftedSquare unitSquare g
  have hl := NormalFanSplice.knots_subset_Icc shiftedSquare unitSquare g.1 hcon.1
  have hr := NormalFanSplice.knots_subset_Icc shiftedSquare unitSquare g.1 hcon.2.1
  have ht01 : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt hl.1 ht.1,
    lt_of_lt_of_le ht.2 hr.2⟩
  have hstrictB : NormalFanSplice.StrictAt unitSquare
      (CommonSupportMerge.normalBlend shiftedSquare g.1 t) g.1 := by
    rw [shiftedNormalBlend]
    exact NormalFanSplice.blend_strict unitSquare g.1 ht01
  have hface := NormalFanSplice.supportFace_of_strict unitSquare g.1 _ hstrictB
  have hv : unitSquare.vertex (MaximalSupportCells.gapB shiftedSquare unitSquare g) =
      unitSquare.vertex g.1 := by
    have hm : unitSquare.vertex
        (MaximalSupportCells.gapB shiftedSquare unitSquare g) ∈
        ({unitSquare.vertex g.1} : Set MergedNormalPrismatoid.Plane) := by
      rw [← hface, hs.2]
      simp
    simpa using hm
  exact NormalFanSplice.raw_vertex_injective unitSquare hv

lemma shiftedHingeVector (i : SourceIndex shiftedSquare unitSquare) :
    hingeVector shiftedSquare unitSquare (by norm_num : (0:ℝ)<1) i =
      WithLp.toLp 2 ![1, 0, 1] := by
  rw [hingeVector, upperEndpoint, lowerEndpoint, shiftedGapB, shiftedVertex]
  ext k
  fin_cases k <;>
    simp [EuclideanPrismatoidCoordinates.pack, MergedNormalPrismatoid.upperLift,
      MergedNormalPrismatoid.lowerLift]

noncomputable def sourceAtGap
    (g : NormalFanSplice.Gap shiftedSquare unitSquare) :
    SourceIndex shiftedSquare unitSquare :=
  next ((NormalFanSplice.orderedGaps shiftedSquare unitSquare).symm (toLex g))

lemma sourceAtGap_entry (g : NormalFanSplice.Gap shiftedSquare unitSquare) :
    entryGap shiftedSquare unitSquare (sourceAtGap g) = g := by
  rw [entryGap, sourceAtGap, NormalFanSplice.prev_next]
  change ofLex (NormalFanSplice.orderedGaps shiftedSquare unitSquare
    ((NormalFanSplice.orderedGaps shiftedSquare unitSquare).symm (toLex g))) = g
  rw [(NormalFanSplice.orderedGaps shiftedSquare unitSquare).apply_symm_apply,
    ofLex_toLex]

lemma sourceAtGap_next_entry (g : NormalFanSplice.Gap shiftedSquare unitSquare) :
    entryGap shiftedSquare unitSquare (next (sourceAtGap g)) =
      CyclicCutOrders.nextGap shiftedSquare unitSquare g := by
  rw [entryGap, NormalFanSplice.prev_next, sourceAtGap]
  change ofLex (NormalFanSplice.orderedGaps shiftedSquare unitSquare
      (next ((NormalFanSplice.orderedGaps shiftedSquare unitSquare).symm (toLex g)))) = _
  rw [← finRotate_eq_next]
  have hs := CyclicCutOrders.ordered_successor
    (CyclicCutOrders.sizes shiftedSquare unitSquare)
    (CyclicCutOrders.sizes_pos shiftedSquare unitSquare)
    (le_trans (by norm_num) (three_le_sideCount shiftedSquare unitSquare))
    (NormalFanSplice.orderedGaps shiftedSquare unitSquare)
    ((NormalFanSplice.orderedGaps shiftedSquare unitSquare).symm (toLex g))
  rw [hs, (NormalFanSplice.orderedGaps shiftedSquare unitSquare).apply_symm_apply]
  rfl

lemma shifted_nextGap_zero (i : Fin 4) :
    CyclicCutOrders.nextGap shiftedSquare unitSquare
      (NormalFanSplice.zeroGap shiftedSquare unitSquare i) =
      NormalFanSplice.zeroGap shiftedSquare unitSquare (next i) := by
  unfold CyclicCutOrders.nextGap CyclicCutOrders.blockNext
  rw [dif_neg (by simp [CyclicCutOrders.sizes, shiftedKnots])]
  apply Sigma.ext
  · rfl
  · exact heq_of_eq (Fin.ext rfl)

lemma entryGap_injective : Function.Injective
    (entryGap shiftedSquare unitSquare) := by
  intro i j hij
  unfold entryGap at hij
  have hp := (NormalFanSplice.orderedGaps shiftedSquare unitSquare).injective hij
  have hn := congrArg next hp
  rw [PolygonSupportCompleteness.next_prev, PolygonSupportCompleteness.next_prev] at hn
  exact hn

lemma sourceAtGap_next (g : NormalFanSplice.Gap shiftedSquare unitSquare) :
    sourceAtGap (CyclicCutOrders.nextGap shiftedSquare unitSquare g) =
      next (sourceAtGap g) := by
  apply entryGap_injective
  rw [sourceAtGap_entry, sourceAtGap_next_entry]

def squareStep3 : Fin 4 → EuclideanPrismatoidCoordinates.PhysicalAmbient :=
  ![WithLp.toLp 2 ![0, 1, 0], WithLp.toLp 2 ![1, 0, 0],
    WithLp.toLp 2 ![0, -1, 0], WithLp.toLp 2 ![-1, 0, 0]]

lemma shiftedMiddleStep (i : Fin 4) :
    middleStep shiftedSquare unitSquare (by norm_num : (0:ℝ)<1)
      (sourceAtGap (NormalFanSplice.zeroGap shiftedSquare unitSquare i)) =
      squareStep3 i := by
  unfold middleStep PhysicalMixedTurnSource.midpoint lowerEndpoint upperEndpoint
  rw [sourceAtGap_entry, sourceAtGap_next_entry, shifted_nextGap_zero]
  rw [shiftedGapB, shiftedGapB, shiftedVertex, shiftedVertex]
  fin_cases i
  all_goals ext z
  all_goals fin_cases z <;>
    norm_num [EuclideanPrismatoidCoordinates.pack,
      MergedNormalPrismatoid.lowerLift, MergedNormalPrismatoid.upperLift,
      unitSquare, unitSquareVertices, squareStep3, NormalFanSplice.zeroGap, next]

lemma shiftedMiddleDirection (i : Fin 4) :
    middleDirection shiftedSquare unitSquare (by norm_num : (0:ℝ)<1)
      (sourceAtGap (NormalFanSplice.zeroGap shiftedSquare unitSquare i)) =
      squareStep3 i := by
  rw [middleDirection, middleLength, shiftedMiddleStep]
  have hn : ‖squareStep3 i‖ = 1 := by
    fin_cases i <;>
      simp [squareStep3, EuclideanSpace.norm_eq, inner, Fin.sum_univ_three]
  rw [hn]
  simp

lemma sourceAtGap_prev_nextZero (i : Fin 4) :
    prev (sourceAtGap (NormalFanSplice.zeroGap shiftedSquare unitSquare (next i))) =
      sourceAtGap (NormalFanSplice.zeroGap shiftedSquare unitSquare i) := by
  rw [← shifted_nextGap_zero, sourceAtGap_next, NormalFanSplice.prev_next]

def prevEquiv (n : ℕ) [NeZero n] : Fin n ≃ Fin n where
  toFun := prev
  invFun := next
  left_inv := PolygonSupportCompleteness.next_prev
  right_inv := NormalFanSplice.prev_next

lemma shiftedDelta_zero :
    intrinsicDelta shiftedSquare unitSquare (hh := (by norm_num : (0:ℝ)<1)) = 0 := by
  let f : SourceIndex shiftedSquare unitSquare → ℝ := fun i =>
    InnerProductGeometry.angle
      (middleDirection shiftedSquare unitSquare (by norm_num : (0:ℝ)<1) i)
      (WithLp.toLp 2 ![1, 0, 1])
  have hsum : (∑ i, f (prev i)) = ∑ i, f i :=
    Equiv.sum_comp (prevEquiv (sideCount shiftedSquare unitSquare)) f
  unfold intrinsicDelta intrinsicQ
  simp_rw [shiftedHingeVector]
  change (∑ i, (f i - f (prev i))) = 0
  rw [Finset.sum_sub_distrib, hsum]
  ring

lemma shiftedQ_neg : intrinsicQ shiftedSquare unitSquare
    (hh := (by norm_num : (0:ℝ)<1))
    (sourceAtGap (NormalFanSplice.zeroGap shiftedSquare unitSquare 0)) < 0 := by
  have hp : prev (sourceAtGap
      (NormalFanSplice.zeroGap shiftedSquare unitSquare 0)) =
      sourceAtGap (NormalFanSplice.zeroGap shiftedSquare unitSquare 3) := by
    simpa [next] using sourceAtGap_prev_nextZero (3 : Fin 4)
  rw [intrinsicQ, shiftedHingeVector, shiftedMiddleDirection, hp,
    shiftedMiddleDirection]
  have hcur : InnerProductGeometry.angle (squareStep3 0)
      (WithLp.toLp 2 ![1, 0, 1]) = Real.pi / 2 :=
    (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mp (by
      norm_num [squareStep3, inner, Fin.sum_univ_three])
  have hprev : Real.pi / 2 < InnerProductGeometry.angle (squareStep3 3)
      (WithLp.toLp 2 ![1, 0, 1]) :=
    (InnerProductGeometry.inner_neg_iff_pi_div_two_lt_angle).mp (by
      norm_num [squareStep3, inner, Fin.sum_univ_three])
  rw [hcur]
  linarith

lemma shiftedQ_pos : 0 < intrinsicQ shiftedSquare unitSquare
    (hh := (by norm_num : (0:ℝ)<1))
    (sourceAtGap (NormalFanSplice.zeroGap shiftedSquare unitSquare 2)) := by
  have hp : prev (sourceAtGap
      (NormalFanSplice.zeroGap shiftedSquare unitSquare 2)) =
      sourceAtGap (NormalFanSplice.zeroGap shiftedSquare unitSquare 1) := by
    simpa [next] using sourceAtGap_prev_nextZero (1 : Fin 4)
  rw [intrinsicQ, shiftedHingeVector, shiftedMiddleDirection, hp,
    shiftedMiddleDirection]
  have hcur : InnerProductGeometry.angle (squareStep3 2)
      (WithLp.toLp 2 ![1, 0, 1]) = Real.pi / 2 :=
    (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mp (by
      norm_num [squareStep3, inner, Fin.sum_univ_three])
  have hinner : 0 < inner ℝ (squareStep3 1) (WithLp.toLp 2 ![1, 0, 1]) := by
    norm_num [squareStep3, inner, Fin.sum_univ_three]
  have hprev : InnerProductGeometry.angle (squareStep3 1)
      (WithLp.toLp 2 ![1, 0, 1]) < Real.pi / 2 := by
    apply lt_of_not_ge
    intro hge
    have hn := (InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle).mpr hge
    linarith
  rw [hcur]
  linarith

lemma shiftedTMixed : IntrinsicTMixed shiftedSquare unitSquare
    (by norm_num : (0:ℝ)<1) := by
  refine ⟨⟨sourceAtGap (NormalFanSplice.zeroGap shiftedSquare unitSquare 0), ?_⟩,
    ⟨sourceAtGap (NormalFanSplice.zeroGap shiftedSquare unitSquare 2), ?_⟩⟩
  · simp [intrinsicT, shiftedDelta_zero, shiftedQ_neg.le]
  · simp [intrinsicT, shiftedDelta_zero, shiftedQ_pos.le]

theorem shiftedEndpoint : RawCutSurfaceConclusion shiftedSquare unitSquare
    (by norm_num : (0:ℝ)<1) :=
  physical_rawCutSurfaceConclusion shiftedSquare unitSquare (by norm_num) shiftedTMixed

def obliqueIndex : SourceIndex shiftedSquare unitSquare :=
  sourceAtGap (NormalFanSplice.zeroGap shiftedSquare unitSquare 0)

def obliqueSeam : SourceIndex shiftedSquare unitSquare := prev obliqueIndex

noncomputable def obliqueOmittedEdge :=
  CyclicCutOrders.cut shiftedSquare unitSquare (h := 1) (by norm_num) obliqueSeam

def obliqueChain0 : Fin (sideCount shiftedSquare unitSquare - 1) :=
  ⟨0, by have hs := three_le_sideCount shiftedSquare unitSquare; omega⟩

noncomputable def obliqueRetainedEdge :=
  CyclicCutOrders.hinge shiftedSquare unitSquare (h := 1) (by norm_num) obliqueSeam
    obliqueChain0

lemma oblique_omit_retain_wrap :
    intrinsicQ shiftedSquare unitSquare (hh := (by norm_num : (0:ℝ)<1))
        obliqueIndex ≠ 0 ∧
    order shiftedSquare unitSquare obliqueSeam
        (Fin.last (sideCount shiftedSquare unitSquare - 1)) =
      cycle shiftedSquare unitSquare obliqueSeam ∧
    order shiftedSquare unitSquare obliqueSeam 0 =
      cycle shiftedSquare unitSquare obliqueIndex ∧
    ¬ SamePair
      (order shiftedSquare unitSquare obliqueSeam obliqueChain0.castSucc)
      (order shiftedSquare unitSquare obliqueSeam obliqueChain0.succ)
      (order shiftedSquare unitSquare obliqueSeam
        (Fin.last (sideCount shiftedSquare unitSquare - 1)))
      (order shiftedSquare unitSquare obliqueSeam 0) := by
  refine ⟨ne_of_lt (by simpa [obliqueIndex] using shiftedQ_neg),
    order_last shiftedSquare unitSquare obliqueSeam, ?_, ?_⟩
  · rw [order_zero, finRotate_eq_next, obliqueSeam,
      PolygonSupportCompleteness.next_prev]
  · exact chain_pair_not_cut shiftedSquare unitSquare obliqueSeam obliqueChain0

lemma sameGapB {n : ℕ} [NeZero n] (P : ReducedConvexPolygon n)
    (g : NormalFanSplice.Gap P P) : MaximalSupportCells.gapB P P g = g.1 := by
  have hs := (MaximalSupportCells.gapB_spec P P g).2 _
    (MaximalSupportCells.mid_mem P P g)
  have hv : P.vertex (MaximalSupportCells.gapB P P g) = P.vertex g.1 := by
    have hm : P.vertex (MaximalSupportCells.gapB P P g) ∈
        ({P.vertex g.1} : Set MergedNormalPrismatoid.Plane) := by
      rw [← hs.1, hs.2]
      simp
    simpa using hm
  exact NormalFanSplice.raw_vertex_injective P hv

lemma sameHingeVector {n : ℕ} [NeZero n] (P : ReducedConvexPolygon n)
    {h : ℝ} (hh : 0 < h) (i : SourceIndex P P) :
    hingeVector P P hh i = WithLp.toLp 2 ![0, 0, h] := by
  rw [hingeVector, upperEndpoint, lowerEndpoint, sameGapB]
  ext k
  fin_cases k <;> simp [EuclideanPrismatoidCoordinates.pack,
    MergedNormalPrismatoid.upperLift, MergedNormalPrismatoid.lowerLift]

lemma sameDirection_vertical_inner {n : ℕ} [NeZero n]
    (P : ReducedConvexPolygon n) {h : ℝ} (hh : 0 < h)
    (i j : SourceIndex P P) :
    inner ℝ (middleDirection P P hh j) (hingeVector P P hh i) = 0 := by
  rw [sameHingeVector]
  have hz := middleDirection_height P P hh j
  rw [OriginalFacetCertificates.height_apply] at hz
  have hz' : middleDirection P P hh j 2 = 0 := by
    apply (div_eq_zero_iff).mp hz |>.resolve_right hh.ne'
  simp [inner, Fin.sum_univ_three, hz']

lemma rightPrismQ_zero {n : ℕ} [NeZero n] (P : ReducedConvexPolygon n)
    {h : ℝ} (hh : 0 < h) (i : SourceIndex P P) :
    intrinsicQ P P (hh := hh) i = 0 := by
  have hi : InnerProductGeometry.angle (middleDirection P P hh i)
      (hingeVector P P hh i) = Real.pi / 2 :=
    (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mp
      (sameDirection_vertical_inner P hh i i)
  have hp : InnerProductGeometry.angle (middleDirection P P hh (prev i))
      (hingeVector P P hh i) = Real.pi / 2 :=
    (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mp
      (sameDirection_vertical_inner P hh i (prev i))
  rw [intrinsicQ, hi, hp]
  ring

lemma rightPrismDelta_zero {n : ℕ} [NeZero n] (P : ReducedConvexPolygon n)
    {h : ℝ} (hh : 0 < h) : intrinsicDelta P P (hh := hh) = 0 := by
  simp [intrinsicDelta, rightPrismQ_zero P hh]

lemma rightPrismTMixed {n : ℕ} [NeZero n] (P : ReducedConvexPolygon n)
    {h : ℝ} (hh : 0 < h) : IntrinsicTMixed P P hh := by
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;>
    simp [intrinsicT, rightPrismQ_zero P hh, rightPrismDelta_zero P hh]

theorem rightPrismEndpoint : RawCutSurfaceConclusion unitSquare unitSquare
    (by norm_num : (0:ℝ)<1) :=
  physical_rawCutSurfaceConclusion unitSquare unitSquare (by norm_num)
    (rightPrismTMixed unitSquare (by norm_num))

lemma rightPrismHeading_zero {n : ℕ} [NeZero n] (P : ReducedConvexPolygon n)
    {h : ℝ} (hh : 0 < h) (k : Fin (MechanismN P P + 1)) (i : ℕ) :
    familyHeading P P hh k i = 0 := by
  unfold familyHeading
  apply Finset.sum_eq_zero
  intro j hj
  exact rightPrismQ_zero P hh _

lemma rightPrism_rotation_identity (k : Fin (MechanismN unitSquare unitSquare + 1)) :
    planeRotation
      (familyHeading unitSquare unitSquare (by norm_num : (0:ℝ)<1) k
        (sideCount unitSquare unitSquare)) = LinearIsometry.id := by
  rw [rightPrismHeading_zero]
  ext x z
  fin_cases z <;> simp [planeRotation, planeRotationLinear]

lemma rightPrism_translation_nonzero
    (k : Fin (MechanismN unitSquare unitSquare + 1)) :
    familyB unitSquare unitSquare (by norm_num : (0:ℝ)<1) (1/4) k
      (sideCount unitSquare unitSquare) ≠ 0 := by
  intro hz
  have hcoord := congrArg (fun p : PhysicalMixedTurnSource.Plane => p 0) hz
  have he (j : ℕ) : 0 <
      familyE unitSquare unitSquare (by norm_num : (0:ℝ)<1) (1/4) k j 0 := by
    have her := familyE_represents unitSquare unitSquare
      (by norm_num : (0:ℝ)<1) (1/4) k j
    have hc := congrArg (fun p : PhysicalMixedTurnSource.Plane => p 0) her
    have hc' : familyE unitSquare unitSquare (by norm_num : (0:ℝ)<1)
        (1/4) k j 0 = familyLength unitSquare unitSquare
          (by norm_num : (0:ℝ)<1) (1/4) k j := by
      rw [hc, rightPrismHeading_zero]
      simp [MixedTurnSafeCut.direction]
    rw [hc']
    simpa [familyLength] using
      (retainedLowerRunCoeff_pos unitSquare unitSquare (by norm_num)
        (by norm_num) (by norm_num) (familySource unitSquare unitSquare k j))
  have hpos : 0 <
      (familyB unitSquare unitSquare (by norm_num : (0:ℝ)<1) (1/4) k
        (sideCount unitSquare unitSquare)) 0 := by
    rw [familyB]
    have hcoordSum :
        (∑ j ∈ Finset.range (sideCount unitSquare unitSquare),
          familyE unitSquare unitSquare (by norm_num : (0:ℝ)<1) (1/4) k j) 0 =
        ∑ j ∈ Finset.range (sideCount unitSquare unitSquare),
          familyE unitSquare unitSquare (by norm_num : (0:ℝ)<1) (1/4) k j 0 := by
      simp
    rw [hcoordSum]
    exact Finset.sum_pos (f := fun j =>
      familyE unitSquare unitSquare (by norm_num : (0:ℝ)<1) (1/4) k j 0)
      (s := Finset.range (sideCount unitSquare unitSquare))
      (fun j _ => he j) ⟨0, Finset.mem_range.mpr (by
        have hs := three_le_sideCount unitSquare unitSquare
        omega)⟩
  change (familyB unitSquare unitSquare (by norm_num : (0:ℝ)<1) (1/4) k
    (sideCount unitSquare unitSquare)) 0 = 0 at hcoord
  linarith

end
end PhysicalMixedTurnSourceSanityFixtures
