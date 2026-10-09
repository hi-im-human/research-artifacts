import MixedTurnSafeCut
import ConvexPolygonTurning
import GeneralBandClosedApplication
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
Physical source bridge for the intrinsic shifted T-mixed subclass.
-/

open Set
open scoped BigOperators Classical NNReal
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CommonSupportMerge OriginalFacetCertificates NormalFanSplice MaximalSupportCells CyclicCutOrders
open EuclideanPrismatoidCoordinates PolyhedralInputBridge
open TrimmedFacetWitnesses BandGeometryAssembly FiniteWitnessClosure
open CutSurfaceQuotient MixedTurnSafeCut PolygonSetReconstruction ConvexPolygonTurning

namespace PhysicalMixedTurnSource
noncomputable section
set_option maxHeartbeats 2000000

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Isometric inclusion of the horizontal physical plane. -/
def horizontalLinear : Plane →ₗ[ℝ] PhysicalAmbient where
  toFun x := WithLp.toLp 2 ![x 0, x 1, 0]
  map_add' := by
    intro x y
    ext k
    fin_cases k <;> simp
  map_smul' := by
    intro c x
    ext k
    fin_cases k <;> simp

def horizontalIsometry : Plane →ₗᵢ[ℝ] PhysicalAmbient :=
  horizontalLinear.isometryOfInner (by
    intro x y
    simp [horizontalLinear, inner, Fin.sum_univ_three, Fin.sum_univ_two])

/-- Shifted mixedness for a finite scalar array.  This isolates the exact
condition used by `mixed_budget_selection`. -/
def ShiftedMixed {ι : Type*} [Fintype ι] (q : ι → ℝ) : Prop :=
  (∃ i, q i - ∑ j, q j ≤ 0) ∧ (∃ i, 0 ≤ q i - ∑ j, q j)

lemma scalar_eq_positive_sub_negative (x : ℝ) :
    x = max x 0 - max (-x) 0 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, max_eq_right (by linarith : -x ≤ 0)]
    ring
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx', max_eq_left (by linarith : 0 ≤ -x)]
    ring

lemma max_add_max_neg_eq_abs (x : ℝ) : max x 0 + max (-x) 0 = |x| := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, max_eq_right (by linarith : -x ≤ 0), abs_of_nonneg hx]
    ring
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx', max_eq_left (by linarith : 0 ≤ -x), abs_of_nonpos hx']
    ring

/-- The sum of the two mechanism budgets is exact total variation. -/
theorem positiveBudget_add_negativeBudget_eq_sum_abs
    {n : ℕ} (q : Fin (n+1) → ℝ) :
    positiveBudget q + negativeBudget q = ∑ i, |q i| := by
  rw [positiveBudget, negativeBudget, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact max_add_max_neg_eq_abs (q i)

/-- Guard the mechanism's budget convention: `sum q = P-N`. -/
theorem sum_eq_positiveBudget_sub_negativeBudget
    {n : ℕ} (q : Fin (n+1) → ℝ) :
    (∑ i, q i) = positiveBudget q - negativeBudget q := by
  rw [positiveBudget, negativeBudget, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact scalar_eq_positive_sub_negative (q i)

section Raw
variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

abbrev SourceIndex := Fin (sideCount A B)

lemma finRotate_eq_next (i : SourceIndex A B) :
    finRotate (sideCount A B) i = next i := by
  apply Fin.ext
  rw [finRotate_apply]
  simp only [Fin.val_add]
  have hOne : ((1 : Fin (sideCount A B))).val = 1 := by
    change 1 % sideCount A B = 1
    exact Nat.mod_eq_of_lt (by have := three_le_sideCount A B; omega)
  rw [hOne]
  rfl

lemma section_support_eq_iff
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {a b w : Plane} (ha : a ∈ A.body) (hb : b ∈ B.body) :
    inner ℝ w ((1-t) • b + t • a) = rowBound A B t w ↔
      inner ℝ w b = supportValue B w ∧ inner ℝ w a = supportValue A w := by
  have hB := supportIndex_max B w b hb
  have hA := supportIndex_max A w a ha
  change inner ℝ w b ≤ supportValue B w at hB
  change inner ℝ w a ≤ supportValue A w at hA
  unfold rowBound
  simp only [inner_add_right, inner_smul_right]
  constructor
  · intro he
    constructor <;> nlinarith
  · rintro ⟨hbe, hae⟩
    rw [hbe, hae]

/-- The entry hinge of face `cycle i`; `cyclicEdge j` is an exit hinge, hence
entry indexing uses the predecessor `j = i-1`. -/
def entryGap (i : SourceIndex A B) : Gap A B := enumeratedGap A B (prev i)

def entryEdge (i : SourceIndex A B) := cyclicEdge A B hh (prev i)

lemma entryGap_left (i : SourceIndex A B) :
    gapSide A B (entryGap A B i) = cycle A B (prev i) := by
  exact (cycle_gap A B (prev i)).symm

lemma entryGap_right (i : SourceIndex A B) :
    rightSide A B (entryGap A B i) = cycle A B i := by
  rw [entryGap, rightSide_cycle_successor]
  congr 1
  rw [finRotate_eq_next, next_prev]

/-- Canonical lower endpoint of the actual common material hinge. -/
def lowerEndpoint (_hh : 0 < h) (i : SourceIndex A B) : PhysicalAmbient :=
  pack (lowerLift (B.vertex (gapB A B (entryGap A B i))))

/-- Canonical upper endpoint of the actual common material hinge. -/
def upperEndpoint (_hh : 0 < h) (i : SourceIndex A B) : PhysicalAmbient :=
  pack (upperLift h (A.vertex (entryGap A B i).1))

def hingeVector (i : SourceIndex A B) : PhysicalAmbient :=
  upperEndpoint A B hh i - lowerEndpoint A B hh i

def midpoint (i : SourceIndex A B) : PhysicalAmbient :=
  (2 : ℝ)⁻¹ • (lowerEndpoint A B hh i + upperEndpoint A B hh i)

lemma lowerEndpoint_height (i : SourceIndex A B) :
    heightLinear h (lowerEndpoint A B hh i) = 0 := by
  rw [height_apply]
  simp [lowerEndpoint, pack, unpack, lowerLift]

lemma upperEndpoint_height (i : SourceIndex A B) :
    heightLinear h (upperEndpoint A B hh i) = 1 := by
  rw [height_apply]
  simp [upperEndpoint, pack, unpack, upperLift, hh.ne']

lemma hingeVector_height (i : SourceIndex A B) :
    heightLinear h (hingeVector A B hh i) = 1 := by
  rw [hingeVector, map_sub, upperEndpoint_height, lowerEndpoint_height]
  ring

lemma hingeVector_ne_zero (i : SourceIndex A B) : hingeVector A B hh i ≠ 0 := by
  intro hz
  have hzheight := congrArg (heightLinear h) hz
  rw [map_zero, hingeVector_height] at hzheight
  norm_num at hzheight

lemma midpoint_eq_lineMap (i : SourceIndex A B) :
    midpoint A B hh i =
      AffineMap.lineMap (lowerEndpoint A B hh i) (upperEndpoint A B hh i) (1/2 : ℝ) := by
  rw [midpoint, AffineMap.lineMap_apply_module]
  module

lemma midpoint_height (i : SourceIndex A B) :
    heightLinear h (midpoint A B hh i) = (1/2 : ℝ) := by
  rw [midpoint, map_smul, map_add, lowerEndpoint_height, upperEndpoint_height]
  norm_num

def middleVertex (i : SourceIndex A B) : Plane :=
  (1/2 : ℝ) •
    (B.vertex (gapB A B (entryGap A B i)) + A.vertex (entryGap A B i).1)

lemma middleVertex_pair_maximizes_exit (i : SourceIndex A B) :
    Maximizes A (cycle A B i).val (entryGap A B i).1 ∧
      Maximizes B (cycle A B i).val (gapB A B (entryGap A B i)) := by
  apply (side_supports_pair_iff A B (entryGap A B i) (cycle A B i)).mpr
  exact Or.inr (entryGap_right A B i).symm

lemma nextMiddleVertex_pair_maximizes_exit (i : SourceIndex A B) :
    Maximizes A (cycle A B i).val (entryGap A B (next i)).1 ∧
      Maximizes B (cycle A B i).val (gapB A B (entryGap A B (next i))) := by
  apply (side_supports_pair_iff A B (entryGap A B (next i)) (cycle A B i)).mpr
  left
  have h := entryGap_left A B (next i)
  simpa only [prev_next] using h.symm

lemma middleVertex_mem_section (i : SourceIndex A B) :
    middleVertex A B i ∈ sectionSet A B (1/2 : ℝ) := by
  refine ⟨(B.vertex (gapB A B (entryGap A B i)),
      A.vertex (entryGap A B i).1),
    ⟨B.vertex_mem_body _, A.vertex_mem_body _⟩, ?_⟩
  simp [middleVertex, mixLinear]
  module

lemma flatLinear_pack (p : Ambient) : flatLinear (pack p) = p.1 := by
  ext k
  fin_cases k <;> rfl

theorem midpoint_eq_mixedPoint (i : SourceIndex A B) :
    midpoint A B hh i = mixedPoint A B h (1/2 : ℝ) (entryGap A B i) := by
  change (2 : ℝ)⁻¹ •
      (coordinateEquiv (lowerLift (B.vertex (gapB A B (entryGap A B i)))) +
        coordinateEquiv (upperLift h (A.vertex (entryGap A B i).1))) =
    coordinateEquiv ((1-(1/2 : ℝ)) •
      lowerLift (B.vertex (gapB A B (entryGap A B i))) +
      (1/2 : ℝ) • upperLift h (A.vertex (entryGap A B i).1))
  rw [← map_add, ← map_smul]
  congr 1
  module

lemma midpoint_flat (i : SourceIndex A B) :
    flatLinear (midpoint A B hh i) = middleVertex A B i := by
  rw [midpoint_eq_mixedPoint]
  unfold mixedPoint
  rw [flatLinear_pack]
  simp [lowerLift, upperLift]
  rw [middleVertex]
  norm_num

def chosenLowerEndpoint (i : SourceIndex A B) : PhysicalAmbient :=
  (certificate A B hh (cycle A B (prev i))).chart (entryEdge A B hh i).aL

def chosenUpperEndpoint (i : SourceIndex A B) : PhysicalAmbient :=
  (certificate A B hh (cycle A B (prev i))).chart (entryEdge A B hh i).bL

lemma lowerEndpoint_eq_mixedPoint_zero (i : SourceIndex A B) :
    lowerEndpoint A B hh i = mixedPoint A B h 0 (entryGap A B i) := by
  change coordinateEquiv (lowerLift (B.vertex (gapB A B (entryGap A B i)))) =
    coordinateEquiv ((1-0) • lowerLift (B.vertex (gapB A B (entryGap A B i))) +
      0 • upperLift h (A.vertex (entryGap A B i).1))
  simp

lemma upperEndpoint_eq_mixedPoint_one (i : SourceIndex A B) :
    upperEndpoint A B hh i = mixedPoint A B h 1 (entryGap A B i) := by
  change coordinateEquiv (upperLift h (A.vertex (entryGap A B i).1)) =
    coordinateEquiv ((1-1) • lowerLift (B.vertex (gapB A B (entryGap A B i))) +
      1 • upperLift h (A.vertex (entryGap A B i).1))
  simp

lemma canonical_hinge_point_mem_both (i : SourceIndex A B) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    mixedPoint A B h t (entryGap A B i) ∈
      materialFace A B hh (cycle A B (prev i)) ∩
        materialFace A B hh (cycle A B (finRotate (sideCount A B) (prev i))) := by
  constructor
  · rw [← entryGap_left A B i]
    exact mixedPoint_in_face A B hh ht _ _
      ((side_supports_pair_iff A B _ _).mpr (Or.inl rfl))
  · rw [← rightSide_cycle_successor A B (prev i)]
    exact mixedPoint_in_face A B hh ht _ _
      ((side_supports_pair_iff A B _ _).mpr (Or.inr rfl))

lemma lowerEndpoint_mem_face (i : SourceIndex A B) :
    lowerEndpoint A B hh i ∈ materialFace A B hh (cycle A B i) := by
  rw [lowerEndpoint_eq_mixedPoint_zero, ← entryGap_right A B i]
  exact mixedPoint_in_face A B hh (by norm_num) _ _
    ((side_supports_pair_iff A B _ _).mpr (Or.inr rfl))

lemma upperEndpoint_mem_face (i : SourceIndex A B) :
    upperEndpoint A B hh i ∈ materialFace A B hh (cycle A B i) := by
  rw [upperEndpoint_eq_mixedPoint_one, ← entryGap_right A B i]
  exact mixedPoint_in_face A B hh (by norm_num) _ _
    ((side_supports_pair_iff A B _ _).mpr (Or.inr rfl))

lemma nextLowerEndpoint_mem_face (i : SourceIndex A B) :
    lowerEndpoint A B hh (next i) ∈ materialFace A B hh (cycle A B i) := by
  rw [lowerEndpoint_eq_mixedPoint_zero]
  have hs := entryGap_left A B (next i)
  rw [prev_next] at hs
  rw [← hs]
  exact mixedPoint_in_face A B hh (by norm_num) _ _
    ((side_supports_pair_iff A B _ _).mpr (Or.inl rfl))

lemma nextUpperEndpoint_mem_face (i : SourceIndex A B) :
    upperEndpoint A B hh (next i) ∈ materialFace A B hh (cycle A B i) := by
  rw [upperEndpoint_eq_mixedPoint_one]
  have hs := entryGap_left A B (next i)
  rw [prev_next] at hs
  rw [← hs]
  exact mixedPoint_in_face A B hh (by norm_num) _ _
    ((side_supports_pair_iff A B _ _).mpr (Or.inl rfl))

noncomputable def facePoint (i : SourceIndex A B) (p : PhysicalAmbient)
    (hp : p ∈ materialFace A B hh (cycle A B i)) :
    FaceSpace A B h (cycle A B i) := Classical.choose hp

lemma facePoint_mem (i : SourceIndex A B) (p : PhysicalAmbient)
    (hp : p ∈ materialFace A B hh (cycle A B i)) :
    facePoint A B hh i p hp ∈ (certificate A B hh (cycle A B i)).domain :=
  (Classical.choose_spec hp).1

lemma chart_facePoint (i : SourceIndex A B) (p : PhysicalAmbient)
    (hp : p ∈ materialFace A B hh (cycle A B i)) :
    (certificate A B hh (cycle A B i)).chart (facePoint A B hh i p hp) = p :=
  (Classical.choose_spec hp).2

noncomputable def faceEntryLower (i : SourceIndex A B) : FaceSpace A B h (cycle A B i) :=
  facePoint A B hh i (lowerEndpoint A B hh i) (lowerEndpoint_mem_face A B hh i)

noncomputable def faceEntryUpper (i : SourceIndex A B) : FaceSpace A B h (cycle A B i) :=
  facePoint A B hh i (upperEndpoint A B hh i) (upperEndpoint_mem_face A B hh i)

noncomputable def faceExitLower (i : SourceIndex A B) : FaceSpace A B h (cycle A B i) :=
  facePoint A B hh i (lowerEndpoint A B hh (next i)) (nextLowerEndpoint_mem_face A B hh i)

noncomputable def faceExitUpper (i : SourceIndex A B) : FaceSpace A B h (cycle A B i) :=
  facePoint A B hh i (upperEndpoint A B hh (next i)) (nextUpperEndpoint_mem_face A B hh i)

@[simp] lemma chart_faceEntryLower (i : SourceIndex A B) :
    (certificate A B hh (cycle A B i)).chart (faceEntryLower A B hh i) =
      lowerEndpoint A B hh i := chart_facePoint A B hh _ _ _

@[simp] lemma chart_faceEntryUpper (i : SourceIndex A B) :
    (certificate A B hh (cycle A B i)).chart (faceEntryUpper A B hh i) =
      upperEndpoint A B hh i := chart_facePoint A B hh _ _ _

@[simp] lemma chart_faceExitLower (i : SourceIndex A B) :
    (certificate A B hh (cycle A B i)).chart (faceExitLower A B hh i) =
      lowerEndpoint A B hh (next i) := chart_facePoint A B hh _ _ _

@[simp] lemma chart_faceExitUpper (i : SourceIndex A B) :
    (certificate A B hh (cycle A B i)).chart (faceExitUpper A B hh i) =
      upperEndpoint A B hh (next i) := chart_facePoint A B hh _ _ _

noncomputable def faceEntryMidpoint (i : SourceIndex A B) : FaceSpace A B h (cycle A B i) :=
  AffineMap.lineMap (faceEntryLower A B hh i) (faceEntryUpper A B hh i) (1/2 : ℝ)

noncomputable def faceExitMidpoint (i : SourceIndex A B) : FaceSpace A B h (cycle A B i) :=
  AffineMap.lineMap (faceExitLower A B hh i) (faceExitUpper A B hh i) (1/2 : ℝ)

@[simp] lemma chart_faceEntryMidpoint (i : SourceIndex A B) :
    (certificate A B hh (cycle A B i)).chart (faceEntryMidpoint A B hh i) =
      midpoint A B hh i := by
  rw [faceEntryMidpoint]
  change (certificate A B hh (cycle A B i)).chart.toAffineMap
      (AffineMap.lineMap (faceEntryLower A B hh i) (faceEntryUpper A B hh i) (1/2 : ℝ)) = _
  rw [(certificate A B hh (cycle A B i)).chart.toAffineMap.apply_lineMap]
  change AffineMap.lineMap
    ((certificate A B hh (cycle A B i)).chart (faceEntryLower A B hh i))
    ((certificate A B hh (cycle A B i)).chart (faceEntryUpper A B hh i)) (1/2 : ℝ) = _
  rw [chart_faceEntryLower, chart_faceEntryUpper, ← midpoint_eq_lineMap]

@[simp] lemma chart_faceExitMidpoint (i : SourceIndex A B) :
    (certificate A B hh (cycle A B i)).chart (faceExitMidpoint A B hh i) =
      midpoint A B hh (next i) := by
  rw [faceExitMidpoint]
  change (certificate A B hh (cycle A B i)).chart.toAffineMap
      (AffineMap.lineMap (faceExitLower A B hh i) (faceExitUpper A B hh i) (1/2 : ℝ)) = _
  rw [(certificate A B hh (cycle A B i)).chart.toAffineMap.apply_lineMap]
  change AffineMap.lineMap
    ((certificate A B hh (cycle A B i)).chart (faceExitLower A B hh i))
    ((certificate A B hh (cycle A B i)).chart (faceExitUpper A B hh i)) (1/2 : ℝ) = _
  rw [chart_faceExitLower, chart_faceExitUpper, ← midpoint_eq_lineMap]

lemma middleVertex_exit_tight (i : SourceIndex A B) :
    inner ℝ (cycle A B i).val (middleVertex A B i) =
      rowBound A B (1/2 : ℝ) (cycle A B i).val := by
  rw [middleVertex]
  have he : (1/2 : ℝ) •
      (B.vertex (gapB A B (entryGap A B i)) + A.vertex (entryGap A B i).1) =
      (1-(1/2 : ℝ)) • B.vertex (gapB A B (entryGap A B i)) +
        (1/2 : ℝ) • A.vertex (entryGap A B i).1 := by module
  rw [he]
  apply (section_support_eq_iff A B (by norm_num) (by norm_num)
    (A.vertex_mem_body _) (B.vertex_mem_body _)).mpr
  have hm := middleVertex_pair_maximizes_exit A B i
  exact ⟨(supportValue_at B _ _ hm.2).symm,
    (supportValue_at A _ _ hm.1).symm⟩

lemma nextMiddleVertex_exit_tight (i : SourceIndex A B) :
    inner ℝ (cycle A B i).val (middleVertex A B (next i)) =
      rowBound A B (1/2 : ℝ) (cycle A B i).val := by
  rw [middleVertex]
  have he : (1/2 : ℝ) •
      (B.vertex (gapB A B (entryGap A B (next i))) + A.vertex (entryGap A B (next i)).1) =
      (1-(1/2 : ℝ)) • B.vertex (gapB A B (entryGap A B (next i))) +
        (1/2 : ℝ) • A.vertex (entryGap A B (next i)).1 := by module
  rw [he]
  apply (section_support_eq_iff A B (by norm_num) (by norm_num)
    (A.vertex_mem_body _) (B.vertex_mem_body _)).mpr
  have hm := nextMiddleVertex_pair_maximizes_exit A B i
  exact ⟨(supportValue_at B _ _ hm.2).symm,
    (supportValue_at A _ _ hm.1).symm⟩

theorem middleVertex_tight_iff (i j : SourceIndex A B) :
    inner ℝ (cycle A B i).val (middleVertex A B j) =
        rowBound A B (1/2 : ℝ) (cycle A B i).val ↔
      j = i ∨ j = next i := by
  constructor
  · intro htight
    have he : (1/2 : ℝ) •
        (B.vertex (gapB A B (entryGap A B j)) + A.vertex (entryGap A B j).1) =
        (1-(1/2 : ℝ)) • B.vertex (gapB A B (entryGap A B j)) +
          (1/2 : ℝ) • A.vertex (entryGap A B j).1 := by module
    rw [middleVertex, he] at htight
    have hs := (section_support_eq_iff A B (by norm_num) (by norm_num)
      (A.vertex_mem_body _) (B.vertex_mem_body _)).mp htight
    have hmaxA : Maximizes A (cycle A B i).val (entryGap A B j).1 := by
      intro x hx
      calc
        inner ℝ (cycle A B i).val x ≤ supportValue A (cycle A B i).val :=
          supportIndex_max A _ x hx
        _ = inner ℝ (cycle A B i).val (A.vertex (entryGap A B j).1) := hs.2.symm
    have hmaxB : Maximizes B (cycle A B i).val (gapB A B (entryGap A B j)) := by
      intro x hx
      calc
        inner ℝ (cycle A B i).val x ≤ supportValue B (cycle A B i).val :=
          supportIndex_max B _ x hx
        _ = inner ℝ (cycle A B i).val (B.vertex (gapB A B (entryGap A B j))) := hs.1.symm
    have hside := (side_supports_pair_iff A B (entryGap A B j) (cycle A B i)).mp
      ⟨hmaxA, hmaxB⟩
    rcases hside with hleft | hright
    · have hc : cycle A B i = cycle A B (prev j) := hleft.trans (entryGap_left A B j)
      have hip : i = prev j := (cycle A B).injective hc
      right
      have hn := congrArg next hip
      simpa only [next_prev] using hn.symm
    · have hc : cycle A B i = cycle A B j := hright.trans (entryGap_right A B j)
      exact Or.inl ((cycle A B).injective hc).symm
  · intro hj
    rcases hj with hj | hj
    · subst j
      exact middleVertex_exit_tight A B i
    · subst j
      exact nextMiddleVertex_exit_tight A B i

lemma middleVertex_edge_ne (i : SourceIndex A B) :
    middleVertex A B (next i) ≠ middleVertex A B i := by
  intro heq
  have htight : inner ℝ (cycle A B (prev i)).val (middleVertex A B (next i)) =
      rowBound A B (1/2 : ℝ) (cycle A B (prev i)).val := by
    rw [heq]
    simpa only [next_prev] using nextMiddleVertex_exit_tight A B (prev i)
  rcases (middleVertex_tight_iff A B (prev i) (next i)).mp htight with hbad | hbad
  · have := prev_ne_next (three_le_sideCount A B) i
    exact this hbad.symm
  · have hn := next_ne (by have := three_le_sideCount A B; omega) i
    apply hn
    simpa only [next_prev] using hbad

lemma middleEdge_orthogonal (i : SourceIndex A B) :
    inner ℝ (cycle A B i).val
      (middleVertex A B (next i) - middleVertex A B i) = 0 := by
  rw [inner_sub_right, nextMiddleVertex_exit_tight, middleVertex_exit_tight]
  ring

lemma cycle_det_next_neg (i : SourceIndex A B) :
    PolygonSupportCompleteness.det (cycle A B i).val (cycle A B (next i)).val < 0 := by
  let g := enumeratedGap A B i
  let l := leftKnot A B g
  let r := rightKnot A B g
  let p := outwardNormal A.vertex (prev g.1)
  let q := outwardNormal A.vertex g.1
  let L := normalBlend A g.1 l
  let R := normalBlend A g.1 r
  have hlr : l < r := (gap_consecutive A B g).2.2.1
  have hcorner := PolygonSupportCompleteness.ReducedConvexPolygon.corner_det_pos A g.1
  have hpq : PolygonSupportCompleteness.det p q =
      -PolygonSupportCompleteness.det (back A g.1) (ahead A g.1) := by
    simpa [p, q] using incident_det A g.1
  have hLR : PolygonSupportCompleteness.det L R =
      (r-l) * PolygonSupportCompleteness.det p q := by
    simp [L, R, normalBlend, p, q, PolygonSupportCompleteness.det]
    ring
  have hLRneg : PolygonSupportCompleteness.det L R < 0 := by
    rw [hLR, hpq]
    nlinarith
  have hL : 0 < ‖L‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr (normalBlend_ne_zero A g.1))
  have hR : 0 < ‖R‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr (normalBlend_ne_zero A g.1))
  have hleft : (cycle A B i).val = unitRay L := by
    change (gapSide A B g).val = unitRay L
    rfl
  have hright : (cycle A B (next i)).val = unitRay R := by
    have hs := rightSide_cycle_successor A B i
    rw [finRotate_eq_next] at hs
    change rightSide A B g = cycle A B (next i) at hs
    exact congrArg Subtype.val hs.symm
  rw [hleft, hright]
  change PolygonSupportCompleteness.det (‖L‖⁻¹ • L) (‖R‖⁻¹ • R) < 0
  simp only [PolygonSupportCompleteness.det, PiLp.smul_apply, smul_eq_mul]
  have hd := hLRneg
  simp only [PolygonSupportCompleteness.det] at hd
  rw [show ‖L‖⁻¹ * L 0 * (‖R‖⁻¹ * R 1) - ‖L‖⁻¹ * L 1 * (‖R‖⁻¹ * R 0) =
      (‖L‖⁻¹ * ‖R‖⁻¹) * (L 0 * R 1 - L 1 * R 0) by ring]
  exact mul_neg_of_pos_of_neg (mul_pos hL hR) hd

lemma middleEdge_normal_parallel (i : SourceIndex A B) :
    ∃ c : ℝ, c ≠ 0 ∧
      outwardNormal (middleVertex A B) i = c • (cycle A B i).val := by
  let u := (cycle A B i).val
  let e := middleVertex A B (next i) - middleVertex A B i
  let c : ℝ := -PolygonSupportCompleteness.det u e
  have hu : u 0 * u 0 + u 1 * u 1 = 1 := by
    have hn := side_unit A B (cycle A B i)
    have huinner : inner ℝ u u = 1 := by
      rw [real_inner_self_eq_norm_sq, hn]
      norm_num
    simpa [inner, Fin.sum_univ_two] using huinner
  have hue : u 0 * e 0 + u 1 * e 1 = 0 := by
    have ho := middleEdge_orthogonal A B i
    change inner ℝ u e = 0 at ho
    simp [inner, Fin.sum_univ_two] at ho
    nlinarith
  have hue0 := congrArg (fun z : ℝ => u 0 * z) hue
  have hue1 := congrArg (fun z : ℝ => u 1 * z) hue
  have hu0 := congrArg (fun z : ℝ => e 0 * z) hu
  have hu1 := congrArg (fun z : ℝ => e 1 * z) hu
  ring_nf at hue0 hue1 hu0 hu1
  have heq : outwardNormal (middleVertex A B) i = c • u := by
    change rotateCW e = c • u
    ext k
    fin_cases k <;>
      simp [rotateCW, c, PolygonSupportCompleteness.det] <;>
      nlinarith
  refine ⟨c, ?_, heq⟩
  intro hc
  have hz : outwardNormal (middleVertex A B) i = 0 := by simpa [hc] using heq
  have h0 := congrArg (fun x : Plane => x 0) hz
  have h1 := congrArg (fun x : Plane => x 1) hz
  apply middleVertex_edge_ne A B i
  apply sub_eq_zero.mp
  ext k
  fin_cases k
  · simpa [outwardNormal, edgeVector, rotateCW] using h1
  · simpa [outwardNormal, edgeVector, rotateCW] using neg_eq_zero.mp h0

lemma middleEdge_normal_positive (i : SourceIndex A B) :
    ∃ c : ℝ, 0 < c ∧
      outwardNormal (middleVertex A B) i = c • (cycle A B i).val := by
  obtain ⟨c, hc0, heq⟩ := middleEdge_normal_parallel A B i
  let u := (cycle A B i).val
  let v := (cycle A B (next i)).val
  let e := middleVertex A B (next i) - middleVertex A B i
  have hback : middleVertex A B i - middleVertex A B (next i) = c • rotateCW u := by
    have hr := congrArg rotateCW heq
    change rotateCW (rotateCW e) = rotateCW (c • u) at hr
    have hr0 := congrArg (fun z : Plane => z 0) hr
    have hr1 := congrArg (fun z : Plane => z 1) hr
    ext k
    fin_cases k
    · simpa [rotateCW, e, u] using hr0
    · simpa [rotateCW, e, u] using hr1
  have hle := section_support_le A B (by norm_num : (1/2 : ℝ) ∈ Icc 0 1)
    v (middleVertex_mem_section A B i)
  have hvnext := middleVertex_exit_tight A B (next i)
  have hne : inner ℝ v (middleVertex A B i) ≠ rowBound A B (1/2 : ℝ) v := by
    intro he
    rcases (middleVertex_tight_iff A B (next i) i).mp he with hbad | hbad
    · exact (next_ne (by have := three_le_sideCount A B; omega) i) hbad.symm
    · exact (self_ne_next_next (three_le_sideCount A B) i) hbad
  have hlt : inner ℝ v (middleVertex A B i) < rowBound A B (1/2 : ℝ) v :=
    lt_of_le_of_ne hle hne
  have hstrict : inner ℝ v (middleVertex A B i - middleVertex A B (next i)) < 0 := by
    rw [inner_sub_right, hvnext]
    linarith
  rw [hback, inner_smul_right] at hstrict
  have huv : inner ℝ v (rotateCW u) = PolygonSupportCompleteness.det u v := by
    rw [real_inner_comm, inner_rotate]
  rw [huv] at hstrict
  have hd := cycle_det_next_neg A B i
  change PolygonSupportCompleteness.det u v < 0 at hd
  have hc : 0 < c := by
    rcases lt_or_gt_of_ne hc0 with hc | hc
    · have := mul_pos_of_neg_of_neg hc hd
      linarith
    · exact hc
  exact ⟨c, hc, heq⟩

/-- The actual support-cell midpoint cycle, with reducedness and orientation
proved from the ordered normal splice. -/
def middlePolygon : ReducedConvexPolygon (sideCount A B) where
  vertex := middleVertex A B
  three_le := three_le_sideCount A B
  edge_ne := middleVertex_edge_ne A B
  supports := by
    intro i j
    obtain ⟨c, hc, heq⟩ := middleEdge_normal_positive A B i
    rw [heq, real_inner_smul_left]
    have hj := section_support_le A B (by norm_num : (1/2 : ℝ) ∈ Icc 0 1)
      (cycle A B i).val (middleVertex_mem_section A B j)
    have hi := middleVertex_exit_tight A B i
    rw [inner_sub_right, hi]
    exact mul_nonpos_of_nonneg_of_nonpos hc.le (sub_nonpos.mpr hj)
  support_eq_vertices := by
    intro i j hz
    obtain ⟨c, hc, heq⟩ := middleEdge_normal_positive A B i
    rw [heq, real_inner_smul_left] at hz
    have hzero : inner ℝ (cycle A B i).val
        (middleVertex A B j - middleVertex A B i) = 0 := by
      exact (mul_eq_zero.mp hz).resolve_left hc.ne'
    rw [inner_sub_right, middleVertex_exit_tight] at hzero
    exact (middleVertex_tight_iff A B i j).mp (by linarith)

/-- Genuine exterior turn of the actual reduced middle-section polygon. -/
def middleExteriorTurn (i : SourceIndex A B) : ℝ :=
  exteriorTurn (middlePolygon A B) i

lemma middleExteriorTurn_pos (i : SourceIndex A B) :
    0 < middleExteriorTurn A B i := exteriorTurn_pos (middlePolygon A B) i

lemma middleExteriorTurn_lt_pi (i : SourceIndex A B) :
    middleExteriorTurn A B i < Real.pi := exteriorTurn_lt_pi (middlePolygon A B) i

theorem sum_middleExteriorTurn_eq_two_pi :
    (∑ i, middleExteriorTurn A B i) = 2 * Real.pi :=
  sum_exteriorTurn_eq_two_pi (middlePolygon A B)

def middleStep (i : SourceIndex A B) : PhysicalAmbient :=
  midpoint A B hh (next i) - midpoint A B hh i

lemma middleStep_eq_horizontal (i : SourceIndex A B) :
    middleStep A B hh i =
      horizontalIsometry (edgeVector (middlePolygon A B).vertex i) := by
  ext k
  fin_cases k <;>
    simp [middleStep, midpoint, lowerEndpoint, upperEndpoint, horizontalIsometry,
      horizontalLinear, middlePolygon, middleVertex, edgeVector, pack, lowerLift, upperLift]

lemma middleStep_ne_zero (i : SourceIndex A B) : middleStep A B hh i ≠ 0 := by
  rw [middleStep_eq_horizontal]
  intro hz
  apply outgoing_ne_zero (middlePolygon A B) i
  apply horizontalIsometry.injective
  simpa using hz

def middleLength (i : SourceIndex A B) : ℝ := ‖middleStep A B hh i‖

def middleDirection (i : SourceIndex A B) : PhysicalAmbient :=
  (middleLength A B hh i)⁻¹ • middleStep A B hh i

lemma middleLength_pos (i : SourceIndex A B) : 0 < middleLength A B hh i :=
  norm_pos_iff.mpr (middleStep_ne_zero A B hh i)

lemma middleDirection_ne_zero (i : SourceIndex A B) : middleDirection A B hh i ≠ 0 := by
  apply smul_ne_zero (inv_ne_zero (middleLength_pos A B hh i).ne')
    (middleStep_ne_zero A B hh i)

lemma middleStep_height (i : SourceIndex A B) :
    heightLinear h (middleStep A B hh i) = 0 := by
  rw [middleStep, map_sub, midpoint_height, midpoint_height]
  ring

lemma middleDirection_height (i : SourceIndex A B) :
    heightLinear h (middleDirection A B hh i) = 0 := by
  rw [middleDirection, map_smul, middleStep_height]
  simp

lemma angle_middleDirection_eq_exteriorTurn (i : SourceIndex A B) :
    InnerProductGeometry.angle (middleDirection A B hh (prev i))
        (middleDirection A B hh i) = middleExteriorTurn A B i := by
  change InnerProductGeometry.angle
      ((middleLength A B hh (prev i))⁻¹ • middleStep A B hh (prev i))
      ((middleLength A B hh i)⁻¹ • middleStep A B hh i) = _
  rw [InnerProductGeometry.angle_smul_left_of_pos _ _
      (inv_pos.mpr (middleLength_pos A B hh (prev i))),
    InnerProductGeometry.angle_smul_right_of_pos _ _
      (inv_pos.mpr (middleLength_pos A B hh i)),
    middleStep_eq_horizontal, middleStep_eq_horizontal,
    horizontalIsometry.angle_map]
  rfl

noncomputable def faceMiddleStep (i : SourceIndex A B) :
    FaceSpace A B h (cycle A B i) :=
  faceExitMidpoint A B hh i - faceEntryMidpoint A B hh i

noncomputable def faceHingeVector (i : SourceIndex A B) :
    FaceSpace A B h (cycle A B i) :=
  faceEntryUpper A B hh i - faceEntryLower A B hh i

lemma chartLinear_faceMiddleStep (i : SourceIndex A B) :
    (certificate A B hh (cycle A B i)).chart.linearIsometry
      (faceMiddleStep A B hh i) = middleStep A B hh i := by
  calc
    _ = (certificate A B hh (cycle A B i)).chart (faceExitMidpoint A B hh i) -
        (certificate A B hh (cycle A B i)).chart (faceEntryMidpoint A B hh i) :=
      (certificate A B hh (cycle A B i)).chart.map_vsub _ _
    _ = middleStep A B hh i := by
      rw [chart_faceExitMidpoint, chart_faceEntryMidpoint]
      rfl

lemma chartLinear_faceHingeVector (i : SourceIndex A B) :
    (certificate A B hh (cycle A B i)).chart.linearIsometry
      (faceHingeVector A B hh i) = hingeVector A B hh i := by
  calc
    _ = (certificate A B hh (cycle A B i)).chart (faceEntryUpper A B hh i) -
        (certificate A B hh (cycle A B i)).chart (faceEntryLower A B hh i) :=
      (certificate A B hh (cycle A B i)).chart.map_vsub _ _
    _ = hingeVector A B hh i := by
      rw [chart_faceEntryUpper, chart_faceEntryLower]
      rfl

lemma faceMiddleStep_ne_zero (i : SourceIndex A B) : faceMiddleStep A B hh i ≠ 0 := by
  intro hz
  apply middleStep_ne_zero A B hh i
  rw [← chartLinear_faceMiddleStep A B hh i, hz, map_zero]

noncomputable def faceUnit (i : SourceIndex A B) : FaceSpace A B h (cycle A B i) :=
  NormedSpace.normalize (faceMiddleStep A B hh i)

lemma faceUnit_norm (i : SourceIndex A B) : ‖faceUnit A B hh i‖ = 1 :=
  NormedSpace.norm_normalize (faceMiddleStep_ne_zero A B hh i)

lemma chartLinear_faceUnit (i : SourceIndex A B) :
    (certificate A B hh (cycle A B i)).chart.linearIsometry (faceUnit A B hh i) =
      middleDirection A B hh i := by
  have hn : ‖faceMiddleStep A B hh i‖ = ‖middleStep A B hh i‖ := by
    rw [← (certificate A B hh (cycle A B i)).chart.linearIsometry.norm_map,
      chartLinear_faceMiddleStep]
  rw [faceUnit, NormedSpace.normalize, middleDirection, middleLength, map_smul,
    hn, chartLinear_faceMiddleStep]

noncomputable def faceResidual (i : SourceIndex A B) : FaceSpace A B h (cycle A B i) :=
  faceHingeVector A B hh i -
    inner ℝ (faceUnit A B hh i) (faceHingeVector A B hh i) • faceUnit A B hh i

lemma faceUnit_residual_orthogonal (i : SourceIndex A B) :
    inner ℝ (faceUnit A B hh i) (faceResidual A B hh i) = 0 := by
  rw [faceResidual, inner_sub_right]
  have hs := inner_smul_right (𝕜 := ℝ) (faceUnit A B hh i) (faceUnit A B hh i)
    (inner ℝ (faceUnit A B hh i) (faceHingeVector A B hh i))
  rw [hs, real_inner_self_eq_norm_sq, faceUnit_norm]
  ring

lemma faceResidual_ne_zero (i : SourceIndex A B) : faceResidual A B hh i ≠ 0 := by
  intro hz
  have hrmap :
      (certificate A B hh (cycle A B i)).chart.linearIsometry (faceResidual A B hh i) =
        hingeVector A B hh i -
          inner ℝ (faceUnit A B hh i) (faceHingeVector A B hh i) •
            middleDirection A B hh i := by
    rw [faceResidual, map_sub, map_smul, chartLinear_faceHingeVector,
      chartLinear_faceUnit]
  rw [hz, map_zero] at hrmap
  have hzheight := congrArg (heightLinear h) hrmap
  rw [map_zero, map_sub, map_smul, hingeVector_height, middleDirection_height] at hzheight
  norm_num at hzheight

noncomputable def faceTransverse (i : SourceIndex A B) : FaceSpace A B h (cycle A B i) :=
  NormedSpace.normalize (faceResidual A B hh i)

lemma faceTransverse_norm (i : SourceIndex A B) : ‖faceTransverse A B hh i‖ = 1 :=
  NormedSpace.norm_normalize (faceResidual_ne_zero A B hh i)

lemma faceUnit_transverse_orthogonal (i : SourceIndex A B) :
    inner ℝ (faceUnit A B hh i) (faceTransverse A B hh i) = 0 := by
  rw [faceTransverse, NormedSpace.normalize, real_inner_smul_right,
    faceUnit_residual_orthogonal, mul_zero]

noncomputable def faceFrame (i : SourceIndex A B) :
    Fin 2 → FaceSpace A B h (cycle A B i) :=
  ![faceUnit A B hh i, -faceTransverse A B hh i]

lemma faceFrame_orthonormal (i : SourceIndex A B) :
    Orthonormal ℝ (faceFrame A B hh i) := by
  have huu : inner ℝ (faceUnit A B hh i) (faceUnit A B hh i) = 1 := by
    rw [real_inner_self_eq_norm_sq, faceUnit_norm]
    norm_num
  have hvv : inner ℝ (faceTransverse A B hh i) (faceTransverse A B hh i) = 1 := by
    rw [real_inner_self_eq_norm_sq, faceTransverse_norm]
    norm_num
  have huv := faceUnit_transverse_orthogonal A B hh i
  have hvu : inner ℝ (faceTransverse A B hh i) (faceUnit A B hh i) = 0 := by
    rw [real_inner_comm]
    exact huv
  rw [orthonormal_iff_ite]
  intro j k
  fin_cases j <;> fin_cases k
  · simpa [faceFrame] using huu
  · simp [faceFrame, huv]
  · simp [faceFrame, hvu]
  · simpa [faceFrame] using hvv

noncomputable def faceBasis (i : SourceIndex A B) :
    OrthonormalBasis (Fin 2) ℝ (FaceSpace A B h (cycle A B i)) := by
  let v := faceFrame A B hh i
  have hon : Orthonormal ℝ v := faceFrame_orthonormal A B hh i
  refine OrthonormalBasis.mk hon ?_
  have htop := (Orthonormal.linearIndependent hon).span_eq_top_of_card_eq_finrank
    (by simpa using (faceSpace_finrank A B h (cycle A B i)).symm)
  rw [htop]

/-- Intrinsic full-plane chart of the actual face.  Coordinate zero is the
outgoing middle direction and coordinate one is the negative transverse
direction, fixing the unfolding sign convention. -/
noncomputable def intrinsicFaceChart (i : SourceIndex A B) :
    FaceSpace A B h (cycle A B i) ≃ᵃⁱ[ℝ] Plane :=
  (AffineIsometryEquiv.vaddConst ℝ (faceEntryMidpoint A B hh i)).symm.trans
    (faceBasis A B hh i).repr.toAffineIsometryEquiv

@[simp] lemma intrinsicFaceChart_entryMidpoint (i : SourceIndex A B) :
    intrinsicFaceChart A B hh i (faceEntryMidpoint A B hh i) = 0 := by
  simp [intrinsicFaceChart]

@[simp] lemma faceBasis_zero (i : SourceIndex A B) :
    faceBasis A B hh i 0 = faceUnit A B hh i := by
  simp [faceBasis, faceFrame]

@[simp] lemma faceBasis_one (i : SourceIndex A B) :
    faceBasis A B hh i 1 = -faceTransverse A B hh i := by
  simp [faceBasis, faceFrame]

lemma intrinsicFaceChart_apply (i : SourceIndex A B)
    (x : FaceSpace A B h (cycle A B i)) :
    intrinsicFaceChart A B hh i x =
      (faceBasis A B hh i).repr (x - faceEntryMidpoint A B hh i) := by
  rfl

def faceC (i : SourceIndex A B) : ℝ :=
  inner ℝ (faceUnit A B hh i) (faceHingeVector A B hh i)

def faceS (i : SourceIndex A B) : ℝ := ‖faceResidual A B hh i‖

lemma faceS_pos (i : SourceIndex A B) : 0 < faceS A B hh i :=
  norm_pos_iff.mpr (faceResidual_ne_zero A B hh i)

lemma faceHingeVector_decompose (i : SourceIndex A B) :
    faceHingeVector A B hh i = faceC A B hh i • faceUnit A B hh i +
      faceS A B hh i • faceTransverse A B hh i := by
  have hr : faceS A B hh i • faceTransverse A B hh i = faceResidual A B hh i :=
    NormedSpace.norm_smul_normalize (faceResidual A B hh i)
  rw [faceResidual] at hr
  calc
    faceHingeVector A B hh i =
        (faceHingeVector A B hh i - faceC A B hh i • faceUnit A B hh i) +
          faceC A B hh i • faceUnit A B hh i := by module
    _ = faceS A B hh i • faceTransverse A B hh i +
          faceC A B hh i • faceUnit A B hh i := by
      have hz := congrArg
        (fun z => z + faceC A B hh i • faceUnit A B hh i) hr.symm
      simpa [faceC] using hz
    _ = faceC A B hh i • faceUnit A B hh i +
          faceS A B hh i • faceTransverse A B hh i := add_comm _ _

lemma faceMiddleStep_norm (i : SourceIndex A B) :
    ‖faceMiddleStep A B hh i‖ = middleLength A B hh i := by
  rw [middleLength, ← chartLinear_faceMiddleStep A B hh i,
    (certificate A B hh (cycle A B i)).chart.linearIsometry.norm_map]

lemma faceMiddleStep_decompose (i : SourceIndex A B) :
    faceMiddleStep A B hh i = middleLength A B hh i • faceUnit A B hh i := by
  have hu := NormedSpace.norm_smul_normalize (faceMiddleStep A B hh i)
  rw [faceMiddleStep_norm] at hu
  exact hu.symm

lemma faceEntryUpper_sub_midpoint (i : SourceIndex A B) :
    faceEntryUpper A B hh i - faceEntryMidpoint A B hh i =
      (1/2 : ℝ) • faceHingeVector A B hh i := by
  rw [faceEntryMidpoint, AffineMap.lineMap_apply_module, faceHingeVector]
  module

lemma faceEntryLower_sub_midpoint (i : SourceIndex A B) :
    faceEntryLower A B hh i - faceEntryMidpoint A B hh i =
      -(1/2 : ℝ) • faceHingeVector A B hh i := by
  rw [faceEntryMidpoint, AffineMap.lineMap_apply_module, faceHingeVector]
  module

lemma angle_middleDirection_hinge_ne_pi (i j : SourceIndex A B) :
    InnerProductGeometry.angle (middleDirection A B hh j) (hingeVector A B hh i) ≠
      Real.pi := by
  intro hpi
  obtain ⟨_, r, _, he⟩ := InnerProductGeometry.angle_eq_pi_iff.mp hpi
  have hv := congrArg (heightLinear h) he
  rw [map_smul, middleDirection_height, hingeVector_height] at hv
  norm_num at hv

lemma horizontal_direction_not_in_hinge_cone (i j k : SourceIndex A B)
    (hangle : 0 < InnerProductGeometry.angle
      (middleDirection A B hh k) (middleDirection A B hh j)) :
    ¬ (middleDirection A B hh j ∈ Submodule.span ℝ≥0
      ({middleDirection A B hh k, hingeVector A B hh i} : Set PhysicalAmbient)) := by
  intro hmem
  rw [Submodule.mem_span_pair] at hmem
  obtain ⟨α, β, he⟩ := hmem
  simp only [NNReal.smul_def] at he
  have hv := congrArg (heightLinear h) he
  rw [map_add, map_smul, map_smul, middleDirection_height,
    middleDirection_height, hingeVector_height] at hv
  norm_num at hv
  have hβ : β = 0 := hv
  rw [hβ] at he
  norm_num at he
  have hα0 : α ≠ 0 := by
    intro hα
    rw [hα] at he
    norm_num at he
    exact middleDirection_ne_zero A B hh j he.symm
  have hαpos : 0 < (α : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hα0)
  have hang0 : InnerProductGeometry.angle
      (middleDirection A B hh k) (middleDirection A B hh j) = 0 := by
    rw [← he]
    calc
      InnerProductGeometry.angle (middleDirection A B hh k)
          ((α : ℝ) • middleDirection A B hh k) =
        InnerProductGeometry.angle (middleDirection A B hh k)
          (middleDirection A B hh k) :=
        InnerProductGeometry.angle_smul_right_of_pos _ _ hαpos
      _ = 0 := InnerProductGeometry.angle_self (middleDirection_ne_zero A B hh k)
  linarith

/-- Intrinsic signed turn. This definition is meaningful for triangular source
facets because it uses the nondegenerate middle-section edge directions. -/
def intrinsicQ (i : SourceIndex A B) : ℝ :=
  InnerProductGeometry.angle (middleDirection A B hh i) (hingeVector A B hh i) -
    InnerProductGeometry.angle (middleDirection A B hh (prev i))
      (hingeVector A B hh i)

lemma abs_intrinsicQ_lt_middleExteriorTurn (i : SourceIndex A B) :
    |intrinsicQ A B (hh := hh) i| < middleExteriorTurn A B i := by
  let a := middleDirection A B hh i
  let b := middleDirection A B hh (prev i)
  let d := hingeVector A B hh i
  let τ := middleExteriorTurn A B i
  have hτ : InnerProductGeometry.angle b a = τ := by
    exact angle_middleDirection_eq_exteriorTurn A B hh i
  have hτcomm : InnerProductGeometry.angle a b = τ := by
    rw [InnerProductGeometry.angle_comm]
    exact hτ
  have hτpos : 0 < τ := middleExteriorTurn_pos A B i
  have hupper_le : intrinsicQ A B (hh := hh) i ≤ τ := by
    have ht := InnerProductGeometry.angle_le_angle_add_angle a b d
    change InnerProductGeometry.angle a d - InnerProductGeometry.angle b d ≤ τ
    rw [← hτcomm]
    linarith
  have hupper : intrinsicQ A B (hh := hh) i < τ := by
    apply lt_of_le_of_ne hupper_le
    intro heq
    have heq' : InnerProductGeometry.angle a d =
        InnerProductGeometry.angle a b + InnerProductGeometry.angle b d := by
      change InnerProductGeometry.angle a d - InnerProductGeometry.angle b d = τ at heq
      rw [← hτcomm] at heq
      linarith
    rcases (InnerProductGeometry.angle_eq_angle_add_angle_iff
      (middleDirection_ne_zero A B hh (prev i))).mp heq' with hpi | hspan
    · exact angle_middleDirection_hinge_ne_pi A B hh i i hpi
    · exact horizontal_direction_not_in_hinge_cone A B hh i (prev i) i
        (by rw [hτcomm]; exact hτpos) hspan
  have hlower_le : -intrinsicQ A B (hh := hh) i ≤ τ := by
    have ht := InnerProductGeometry.angle_le_angle_add_angle b a d
    change -(InnerProductGeometry.angle a d - InnerProductGeometry.angle b d) ≤ τ
    rw [← hτ]
    linarith
  have hlower : -intrinsicQ A B (hh := hh) i < τ := by
    apply lt_of_le_of_ne hlower_le
    intro heq
    have heq' : InnerProductGeometry.angle b d =
        InnerProductGeometry.angle b a + InnerProductGeometry.angle a d := by
      change -(InnerProductGeometry.angle a d - InnerProductGeometry.angle b d) = τ at heq
      rw [← hτ] at heq
      linarith
    rcases (InnerProductGeometry.angle_eq_angle_add_angle_iff
      (middleDirection_ne_zero A B hh i)).mp heq' with hpi | hspan
    · exact angle_middleDirection_hinge_ne_pi A B hh i (prev i) hpi
    · exact horizontal_direction_not_in_hinge_cone A B hh i i (prev i)
        (by rw [hτ]; exact hτpos) hspan
  exact abs_lt.mpr ⟨by linarith, hupper⟩

abbrev MechanismN : ℕ := sideCount A B - 1

/-- Cardinal transport required by `DevelopedFamily (sideCount-1)`. -/
def sourceIndexEquiv : Fin (MechanismN A B + 1) ≃ SourceIndex A B :=
  (Fin.castOrderIso (Nat.sub_add_cancel (by
    have hs := three_le_sideCount A B
    omega))).toEquiv

def mechanismQ (k : Fin (MechanismN A B + 1)) : ℝ :=
  intrinsicQ A B (hh := hh) (sourceIndexEquiv A B k)

theorem intrinsic_sum_abs_lt_two_pi :
    (∑ i, |intrinsicQ A B (hh := hh) i|) < 2 * Real.pi := by
  calc
    (∑ i, |intrinsicQ A B (hh := hh) i|) <
        ∑ i, middleExteriorTurn A B i := by
      apply Finset.sum_lt_sum
      · intro i _
        exact le_of_lt (abs_intrinsicQ_lt_middleExteriorTurn A B hh i)
      · exact ⟨0, Finset.mem_univ 0,
          abs_intrinsicQ_lt_middleExteriorTurn A B hh 0⟩
    _ = 2 * Real.pi := sum_middleExteriorTurn_eq_two_pi A B

theorem mechanismQ_total_variation :
    positiveBudget (mechanismQ A B hh) + negativeBudget (mechanismQ A B hh) <
      2 * Real.pi := by
  rw [positiveBudget_add_negativeBudget_eq_sum_abs]
  calc
    (∑ k, |mechanismQ A B hh k|) =
        ∑ i, |intrinsicQ A B (hh := hh) i| := by
      exact Equiv.sum_comp (sourceIndexEquiv A B)
        (fun i => |intrinsicQ A B (hh := hh) i|)
    _ < 2 * Real.pi := intrinsic_sum_abs_lt_two_pi A B hh

def intrinsicDelta : ℝ := ∑ i, intrinsicQ A B (hh := hh) i

def intrinsicT (i : SourceIndex A B) : ℝ :=
  intrinsicQ A B (hh := hh) i - intrinsicDelta A B (hh := hh)

/-- The accepted condition is shifted T-mixedness, not mixed signs of `q`. -/
def IntrinsicTMixed : Prop :=
  (∃ i, intrinsicT A B (hh := hh) i ≤ 0) ∧
    (∃ i, 0 ≤ intrinsicT A B (hh := hh) i)

lemma mechanismQ_sum_eq_intrinsicDelta :
    (∑ k, mechanismQ A B hh k) = intrinsicDelta A B (hh := hh) := by
  exact Equiv.sum_comp (sourceIndexEquiv A B) (intrinsicQ A B (hh := hh))

lemma mechanismQ_budget_difference :
    positiveBudget (mechanismQ A B hh) - negativeBudget (mechanismQ A B hh) =
      intrinsicDelta A B (hh := hh) := by
  rw [← sum_eq_positiveBudget_sub_negativeBudget, mechanismQ_sum_eq_intrinsicDelta]

theorem intrinsicTMixed_mechanism (hmix : IntrinsicTMixed A B hh) :
    (∃ k, mechanismQ A B hh k -
        (positiveBudget (mechanismQ A B hh) - negativeBudget (mechanismQ A B hh)) ≤ 0) ∧
    (∃ k, 0 ≤ mechanismQ A B hh k -
        (positiveBudget (mechanismQ A B hh) - negativeBudget (mechanismQ A B hh))) := by
  rcases hmix with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  refine ⟨⟨(sourceIndexEquiv A B).symm i, ?_⟩,
    ⟨(sourceIndexEquiv A B).symm j, ?_⟩⟩
  · rw [mechanismQ, Equiv.apply_symm_apply, mechanismQ_budget_difference]
    exact hi
  · rw [mechanismQ, Equiv.apply_symm_apply, mechanismQ_budget_difference]
    exact hj

theorem intrinsicTMixed_iff_sum_between_values :
    IntrinsicTMixed A B hh ↔
      (∃ i, intrinsicQ A B (hh := hh) i ≤ intrinsicDelta A B (hh := hh)) ∧
      (∃ i, intrinsicDelta A B (hh := hh) ≤ intrinsicQ A B (hh := hh) i) := by
  simp only [IntrinsicTMixed, intrinsicT]
  constructor <;> rintro ⟨hlo, hhi⟩
  · exact ⟨hlo.imp fun _ hi => by linarith, hhi.imp fun _ hi => by linarith⟩
  · exact ⟨hlo.imp fun _ hi => by linarith, hhi.imp fun _ hi => by linarith⟩

/-- Transparent statement of the requested raw conclusion.  Establishing it
requires the physical source bridge; it is deliberately not postulated. -/
def RawCutSurfaceConclusion : Prop :=
  ∃ e : Fin (sideCount A B),
    Nonempty (CutSurfaceDevelopment A B hh Plane e)

end Raw

section Sets

/-- Canonical choice-transparent reduced presentation of an ordinary finite-hull
polygonal set. -/
def canonicalPresentation (K : Set Plane)
    (hfin : ∃ S : Finset Plane, convexHull ℝ (↑S : Set Plane) = K)
    (hint : (interior K).Nonempty) : RawPresentation K :=
  Classical.choice (exists_reduced_polygon_of_polygon_set K hfin hint)

/-- Set-level mixedness is evaluated on exactly the presentations constructed
by `canonicalPresentation`; it is not quantified over unrelated labelings. -/
def SetIntrinsicTMixed (KA KB : Set Plane)
    (hfinA : ∃ S : Finset Plane, convexHull ℝ (↑S : Set Plane) = KA)
    (hfinB : ∃ S : Finset Plane, convexHull ℝ (↑S : Set Plane) = KB)
    (hintA : (interior KA).Nonempty) (hintB : (interior KB).Nonempty)
    {h : ℝ} (hh : 0 < h) : Prop :=
  let PA := canonicalPresentation KA hfinA hintA
  let PB := canonicalPresentation KB hfinB hintB
  IntrinsicTMixed PA.polygon PB.polygon hh

/-- Transparent statement of the requested ordinary finite-hull endpoint. -/
def SetCutSurfaceConclusion (KA KB : Set Plane)
    (hfinA : ∃ S : Finset Plane, convexHull ℝ (↑S : Set Plane) = KA)
    (hfinB : ∃ S : Finset Plane, convexHull ℝ (↑S : Set Plane) = KB)
    (hintA : (interior KA).Nonempty) (hintB : (interior KB).Nonempty)
    {h : ℝ} (hh : 0 < h) : Prop :=
  let PA := canonicalPresentation KA hfinA hintA
  let PB := canonicalPresentation KB hfinB hintB
  PA.polygon.body = KA ∧ PB.polygon.body = KB ∧
    physicalBodyOfSets KA KB h = physicalPrismatoid PA.polygon PB.polygon h ∧
    ∃ e : Fin (sideCount PA.polygon PB.polygon),
      Nonempty (CutSurfaceDevelopment PA.polygon PB.polygon hh Plane e)

end Sets
end
end PhysicalMixedTurnSource
