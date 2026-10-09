import OriginalFacetCertificates
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Sigma.Order
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Scalar insertion into the first polygon's existing normal cycle

System, 2026-09-19. UNCOMPILED SUPPORT DRAFT, not the whole cyclic constructor.

The raw clockwise polygon convention is unchanged. This file supplies the
local proof route and internally computed scalar knot sets: a B edge-normal
strictly inside one A corner gets one insertion parameter; consecutive actual
knots have common A/B support vertices, unique throughout their open gap.

The finite flattening, complete incidence iff, and all-cut output package
remain to be implemented under handoff 55. No stub theorem, sorry, axiom,
correctFan field, premerged order, or unfolding premise is introduced here.
-/
open Set
open scoped BigOperators Classical
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CommonSupportMerge OriginalFacetCertificates

namespace NormalFanSplice
noncomputable section

section Single
variable {n : ℕ} [NeZero n] (P : ReducedConvexPolygon n)

lemma next_injective : Function.Injective (@next n inferInstance) :=
  (Finite.injective_iff_surjective).mpr (fun i => ⟨prev i,next_prev i⟩)

@[simp] lemma prev_next (i : Fin n) : prev (next i) = i := by
  apply next_injective
  rw [next_prev]

/-- Positive rays only: opposite normals are NOT identified. -/
def EdgeRay (w : Plane) : Prop :=
  ∃ k : Fin n, ∃ c : ℝ, 0 < c ∧ w = c • outwardNormal P.vertex k

def StrictAt (w : Plane) (i : Fin n) : Prop :=
  inner ℝ w (back P i) < 0 ∧ inner ℝ w (ahead P i) < 0

/-- The unchanged raw local contract already implies distinct raw vertices. -/
theorem raw_vertex_injective : Function.Injective P.vertex := by
  intro i j hij
  have hz : P.edgeRow i (P.vertex j) = 0 := by
    rw [← hij]
    exact (P.vertex_edge_eq_iff i i).mpr (Or.inl rfl)
  rcases (P.vertex_edge_eq_iff i j).mp hz with h | h
  · exact h.symm
  · subst j
    exact False.elim (P.edge_ne i hij.symm)

lemma edgeNormal_maximizes (i : Fin n) :
    Maximizes P (outwardNormal P.vertex i) i := by
  intro x hx
  have hr := P.body_edge_nonpos i hx
  rw [P.edgeRow_apply,inner_sub_right] at hr
  linarith

/-- Distinct raw edges have distinct POSITIVE normal rays; opposite rays are
not collapsed. -/
theorem edgeNormal_positiveRay_injective {i j : Fin n} {c : ℝ} (hc : 0 < c)
    (he : outwardNormal P.vertex i = c • outwardNormal P.vertex j) : i = j := by
  have hmi : Maximizes P (outwardNormal P.vertex j) i :=
    maximizes_of_pos_smul P _ i hc (by rw [← he]; exact edgeNormal_maximizes P i)
  have hmni : Maximizes P (outwardNormal P.vertex j) (next i) := by
    apply maximizes_of_pos_smul P _ (next i) hc
    rw [← he]
    intro x hx
    have hr := P.body_edge_nonpos i hx
    have hz : P.edgeRow i (P.vertex (next i)) = 0 :=
      (P.vertex_edge_eq_iff i (next i)).mpr (Or.inr rfl)
    rw [P.edgeRow_apply,inner_sub_right] at hr hz
    linarith
  have hmj := edgeNormal_maximizes P j
  have hrowi : P.edgeRow j (P.vertex i) = 0 := by
    have h1 := hmj _ (P.vertex_mem_body i)
    have h2 := hmi _ (P.vertex_mem_body j)
    rw [P.edgeRow_apply,inner_sub_right]
    linarith
  have hrowni : P.edgeRow j (P.vertex (next i)) = 0 := by
    have h1 := hmj _ (P.vertex_mem_body (next i))
    have h2 := hmni _ (P.vertex_mem_body j)
    rw [P.edgeRow_apply,inner_sub_right]
    linarith
  rcases (P.vertex_edge_eq_iff j i).mp hrowi with hij | hij
  · exact hij
  · rcases (P.vertex_edge_eq_iff j (next i)).mp hrowni with hnext | hnext
    · subst i
      exact False.elim (self_ne_next_next P.three_le j hnext.symm)
    · subst i
      exact False.elim (next_ne (le_trans (by norm_num) P.three_le) (next j) hnext)

/-- Off every actual edge ray, the full support face is a singleton. -/
theorem singleton_of_not_edgeRay (w : Plane) (hw : w ≠ 0)
    (hn : ¬ EdgeRay P w) : ∃ i, supportFace P w = {P.vertex i} := by
  rcases supportFace_classification P w hw with h | h
  · exact h
  · obtain ⟨i, hi⟩ := h
    have hleft : P.vertex i ∈ supportFace P w := by
      rw [hi]
      exact ⟨0, by norm_num, by simp⟩
    have hright : P.vertex (next i) ∈ supportFace P w := by
      rw [hi]
      exact ⟨1, by norm_num, by simp⟩
    obtain ⟨c,hc,he⟩ := positive_ray_of_edge_maxima P w hw i hleft.2 hright.2
    exact False.elim (hn ⟨i,c,hc,he⟩)

lemma blend_back (i : Fin n) (t : ℝ) :
    inner ℝ (normalBlend P i t) (back P i) =
      -t * det (back P i) (ahead P i) := by
  simp only [normalBlend, inner_add_left, real_inner_smul_left]
  simp only [outwardNormal, edgeVector, next_prev]
  simp [rotateCW, back, ahead, det, inner, Fin.sum_univ_two]
  <;> ring

lemma blend_ahead (i : Fin n) (t : ℝ) :
    inner ℝ (normalBlend P i t) (ahead P i) =
      -(1-t) * det (back P i) (ahead P i) := by
  simp only [normalBlend, inner_add_left, real_inner_smul_left]
  simp only [outwardNormal, edgeVector, next_prev]
  simp [rotateCW, back, ahead, det, inner, Fin.sum_univ_two]
  <;> ring

lemma blend_strict (i : Fin n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    StrictAt P (normalBlend P i t) i := by
  have hD := corner_det_pos P i
  constructor
  · rw [blend_back]
    exact mul_neg_of_neg_of_pos (by linarith [ht.1]) hD
  · rw [blend_ahead]
    exact mul_neg_of_neg_of_pos (by linarith [ht.2]) hD

/-- No zero-denominator use is claimed outside StrictAt. The total definition
is filtered by StrictAt before any value becomes a knot. -/
def position (i : Fin n) (w : Plane) : ℝ :=
  (-inner ℝ w (back P i)) /
    ((-inner ℝ w (ahead P i)) + (-inner ℝ w (back P i)))

lemma position_of_positive_blend (i : Fin n) {s t : ℝ} (hs : 0 < s)
    (w : Plane) (he : w = s • normalBlend P i t) : position P i w = t := by
  have hD := corner_det_pos P i
  rw [he]
  unfold position
  simp only [real_inner_smul_left, blend_back, blend_ahead]
  have hden : -(s * (-(1-t)*det (back P i) (ahead P i))) +
      -(s * (-t*det (back P i) (ahead P i))) =
      s*det (back P i) (ahead P i) := by ring
  have hsD : s*det (back P i) (ahead P i) ≠ 0 := mul_ne_zero hs.ne' hD.ne'
  rw [hden]
  apply (div_eq_iff hsD).mpr
  ring

/-- The insertion parameter and its positive scale are DERIVED, not supplied. -/
theorem strict_position (i : Fin n) (w : Plane) (hw : StrictAt P w i) :
    position P i w ∈ Ioo (0 : ℝ) 1 ∧
    ∃ s : ℝ, 0 < s ∧ w = s • normalBlend P i (position P i w) := by
  let aa := -inner ℝ w (ahead P i)
  let bb := -inner ℝ w (back P i)
  let D := det (back P i) (ahead P i)
  have ha : 0 < aa := by dsimp [aa]; linarith [hw.2]
  have hb : 0 < bb := by dsimp [bb]; linarith [hw.1]
  have hd : 0 < D := corner_det_pos P i
  have hab : 0 < aa+bb := add_pos ha hb
  have ht : position P i w = bb/(aa+bb) := rfl
  constructor
  · rw [ht]
    exact ⟨div_pos hb hab, (div_lt_one hab).mpr (by linarith)⟩
  · refine ⟨(aa+bb)/D,div_pos hab hd,?_⟩
    have hs1 : ((aa+bb)/D)*(1-bb/(aa+bb)) = aa/D := by
      field_simp [hd.ne',hab.ne']
      <;> ring
    have hs2 : ((aa+bb)/D)*(bb/(aa+bb)) = bb/D := by
      field_simp [hd.ne',hab.ne']
      <;> ring
    rw [normalBlend,ht,smul_add,smul_smul,smul_smul,hs1,hs2]
    have hn : outwardNormal P.vertex (prev i) = rotateCW (-back P i) := by
      simp only [outwardNormal,edgeVector,next_prev,back,neg_sub]
    rw [hn]
    exact normal_reconstruct (back P i) (ahead P i) w hd.ne'

/-- Strict cone membership exposes exactly the owning raw vertex. -/
theorem supportFace_of_strict (i : Fin n) (w : Plane) (hw : StrictAt P w i) :
    supportFace P w = {P.vertex i} := by
  obtain ⟨ht,s,hs,he⟩ := strict_position P i w hw
  have hm : Maximizes P w i :=
    (maximizes_iff_two P w i).mpr ⟨hw.1.le,hw.2.le⟩
  rw [supportFace_at_max P w i hm]
  have hsingle := positive_normal_exposes_singleton P i
    (lam := 1-position P i w) (μ := position P i w)
    (by linarith [ht.2]) ht.1
  dsimp only at hsingle
  rw [he]
  calc
    {x ∈ P.body |
        inner ℝ (s • normalBlend P i (position P i w)) x =
          inner ℝ (s • normalBlend P i (position P i w)) (P.vertex i)} =
        {x ∈ P.body |
          inner ℝ (normalBlend P i (position P i w)) x =
            inner ℝ (normalBlend P i (position P i w)) (P.vertex i)} := by
      ext x
      simp only [Set.mem_setOf_eq,real_inner_smul_left]
      constructor
      · rintro ⟨hx,heq⟩
        exact ⟨hx,mul_left_cancel₀ hs.ne' heq⟩
      · rintro ⟨hx,heq⟩
        exact ⟨hx,congrArg (fun z : ℝ => s*z) heq⟩
    _ = {P.vertex i} := by simpa [normalBlend] using hsingle

/-- Strict normal-cone interiors have one raw owner. -/
theorem strict_owner_unique (w : Plane) {i j : Fin n}
    (hi : StrictAt P w i) (hj : StrictAt P w j) : i = j := by
  have hfaces : ({P.vertex i} : Set Plane) = {P.vertex j} :=
    (supportFace_of_strict P i w hi).symm.trans
      (supportFace_of_strict P j w hj)
  have hv : P.vertex i = P.vertex j := by
    have : P.vertex i ∈ ({P.vertex j} : Set Plane) := by
      rw [← hfaces]
      simp
    simpa using this
  exact raw_vertex_injective P hv

lemma strictAt_pos_smul (i : Fin n) (w : Plane) {c : ℝ} (hc : 0 < c)
    (hw : StrictAt P w i) : StrictAt P (c • w) i := by
  simp only [StrictAt,real_inner_smul_left] at hw ⊢
  constructor <;> nlinarith [hw.1,hw.2]

/-- A strict owner cannot simultaneously be an A-edge positive ray. -/
theorem not_edgeRay_of_strict (w : Plane) (i : Fin n) (hi : StrictAt P w i) :
    ¬ EdgeRay P w := by
  rintro ⟨k,c,hc,he⟩
  have hs := supportFace_of_strict P i w hi
  rw [he] at hs
  have hedge := supportFace_positive_edge_normal P k hc
  have hsets : ({P.vertex i} : Set Plane) =
      AffineMap.lineMap (P.vertex k) (P.vertex (next k)) '' Icc (0 : ℝ) 1 :=
    hs.symm.trans hedge
  have hk : P.vertex k = P.vertex i := by
    have hm : P.vertex k ∈ AffineMap.lineMap (P.vertex k) (P.vertex (next k)) ''
        Icc (0 : ℝ) 1 := ⟨0,by norm_num,by simp⟩
    rw [← hsets] at hm
    simpa using hm
  have hnk : P.vertex (next k) = P.vertex i := by
    have hm : P.vertex (next k) ∈
        AffineMap.lineMap (P.vertex k) (P.vertex (next k)) '' Icc (0 : ℝ) 1 :=
      ⟨1,by norm_num,by simp⟩
    rw [← hsets] at hm
    simpa using hm
  exact P.edge_ne k (hnk.trans hk.symm)

/-- Every non-edge direction has one internally derived strict owner. -/
theorem existsUnique_strict_owner_of_not_edgeRay (w : Plane) (hw : w ≠ 0)
    (hn : ¬ EdgeRay P w) : ∃! i : Fin n, StrictAt P w i := by
  obtain ⟨i,lam,mu,hlam,hmu,heq⟩ := normalCones_cover P w
  have hlampos : 0 < lam := by
    rcases hlam.lt_or_eq with h | h
    · exact h
    · subst lam
      have hmupos : 0 < mu := by
        rcases hmu.lt_or_eq with hmu0 | hmu0
        · exact hmu0
        · subst mu
          exfalso
          exact hw (by simpa using heq)
      exfalso
      apply hn
      refine ⟨i,mu,hmupos,?_⟩
      simpa using heq
  have hmupos : 0 < mu := by
    rcases hmu.lt_or_eq with h | h
    · exact h
    · subst mu
      exfalso
      apply hn
      refine ⟨prev i,lam,hlampos,?_⟩
      simpa using heq
  have hi : StrictAt P w i := by
    have hD := corner_det_pos P i
    have hb0 := blend_back P i (0 : ℝ)
    have hb1 := blend_back P i (1 : ℝ)
    have ha0 := blend_ahead P i (0 : ℝ)
    have ha1 := blend_ahead P i (1 : ℝ)
    norm_num [normalBlend] at hb0 hb1 ha0 ha1
    constructor
    · rw [heq,inner_add_left,real_inner_smul_left,real_inner_smul_left]
      nlinarith
    · rw [heq,inner_add_left,real_inner_smul_left,real_inner_smul_left]
      nlinarith
  refine ⟨i,hi,?_⟩
  intro j hj
  exact strict_owner_unique P w hj hi

/-- Maximizer membership persists between two parameter values, by affinity.
This needs no general circular-order library. -/
lemma blend_maximizes_between {m : ℕ} [NeZero m] (Q : ReducedConvexPolygon m)
    (i : Fin n) (j : Fin m) {a b t : ℝ} (hab : a < b)
    (ht : t ∈ Icc a b)
    (ha : Maximizes Q (normalBlend P i a) j)
    (hb : Maximizes Q (normalBlend P i b) j) :
    Maximizes Q (normalBlend P i t) j := by
  intro x hx
  have h1 := ha x hx
  have h2 := hb x hx
  simp only [normalBlend,inner_add_left,real_inner_smul_left] at h1 h2 ⊢
  have h3 := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr h1)
  have h4 := mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr h2)
  by_contra hnot
  have h5 := mul_pos (sub_pos.mpr hab) (sub_pos.mpr (lt_of_not_ge hnot))
  nlinarith
end Single

section Pair
variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)

/-- Closed [0,1] knots support interval reasoning. For the eventual global
cycle, emit only LEFT endpoints, so block boundaries occur exactly once. -/
def knots (i : Fin nA) : Finset ℝ :=
  insert 0 (insert 1 ((Finset.univ.filter fun j : Fin nB =>
    StrictAt A (outwardNormal B.vertex j) i).image fun j =>
      position A i (outwardNormal B.vertex j)))

lemma knots_subset_Icc (i : Fin nA) {t : ℝ} (ht : t ∈ knots A B i) :
    t ∈ Icc (0 : ℝ) 1 := by
  simp only [knots,Finset.mem_insert,Finset.mem_image,Finset.mem_filter,
    Finset.mem_univ,true_and] at ht
  rcases ht with h0 | h1 | ⟨j,hj,rfl⟩
  · rw [h0]; norm_num
  · rw [h1]; norm_num
  · have h := (strict_position A i _ hj).1
    exact ⟨h.1.le,h.2.le⟩

/-- Every actual B-normal crossing in a strict A block is a COMPUTED knot.
This is the link preventing a caller-supplied no-break assumption. -/
lemma edgeRay_mem_knots (i : Fin nA) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hr : EdgeRay B (normalBlend A i t)) : t ∈ knots A B i := by
  obtain ⟨j,c,hc,he⟩ := hr
  have hb := blend_strict A i ht
  have hj : StrictAt A (outwardNormal B.vertex j) i := by
    rw [he] at hb
    simp only [StrictAt,real_inner_smul_left] at hb ⊢
    constructor <;> nlinarith [hb.1,hb.2]
  have hback : outwardNormal B.vertex j = c⁻¹ • normalBlend A i t := by
    rw [he,smul_smul,inv_mul_cancel₀ hc.ne',one_smul]
  have htj := position_of_positive_blend A i (inv_pos.mpr hc) _ hback
  simp only [knots,Finset.mem_insert,Finset.mem_image,Finset.mem_filter,
    Finset.mem_univ,true_and]
  exact Or.inr (Or.inr ⟨j,hj,htj⟩)

/-- Two actual neighboring knots, not a supplied angular fan. -/
def Consecutive (i : Fin nA) (a b : ℝ) : Prop :=
  a ∈ knots A B i ∧ b ∈ knots A B i ∧ a < b ∧
    ∀ t ∈ knots A B i, ¬ (a < t ∧ t < b)

lemma consecutive_no_edgeRay (i : Fin nA) {a b : ℝ}
    (hab : Consecutive A B i a b) {t : ℝ} (ht : t ∈ Ioo a b) :
    ¬ EdgeRay B (normalBlend A i t) := by
  intro hr
  have ha := knots_subset_Icc A B i hab.1
  have hb := knots_subset_Icc A B i hab.2.1
  have ht01 : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_lt ha.1 ht.1,lt_of_lt_of_le ht.2 hb.2⟩
  exact hab.2.2.2 t (edgeRay_mem_knots A B i ht01 hr) ht

/-- Active endpoints from the already-checked compact-slice theorem identify
all possible changes of B's support vertex. No change can occur between
consecutive actual knots, including at shared A/B boundary directions. -/
theorem consecutive_knots_common_support (i : Fin nA) {a b : ℝ}
    (hab : Consecutive A B i a b) :
    ∃ j : Fin nB,
      (∀ t ∈ Icc a b, Maximizes A (normalBlend A i t) i ∧
        Maximizes B (normalBlend A i t) j) ∧
      (∀ t ∈ Ioo a b, supportFace A (normalBlend A i t) = {A.vertex i} ∧
        supportFace B (normalBlend A i t) = {B.vertex j}) := by
  have ha := knots_subset_Icc A B i hab.1
  have hb := knots_subset_Icc A B i hab.2.1
  have hablt := hab.2.2.1
  let m : ℝ := (a+b)/2
  have hm : m ∈ Ioo a b := by dsimp [m]; constructor <;> linarith
  have hm01 : m ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [ha.1,hm.1],by linarith [hb.2,hm.2]⟩
  let j := supportIndex B (normalBlend A i m)
  let f : ℝ → ℝ := fun t => inner ℝ (normalBlend A i t) (back B j)
  let g : ℝ → ℝ := fun t => inner ℝ (normalBlend A i t) (ahead B j)
  have hf : Continuous f := by unfold f normalBlend; fun_prop
  have hg : Continuous g := by unfold g normalBlend; fun_prop
  have hmSlice : m ∈ scalarSlice f g :=
    ⟨hm01,(maximizes_iff_two B _ j).mp (supportIndex_max B _)⟩
  obtain ⟨lo,hi,hlo,hhi,hlom,hmhi,hloActive,hhiActive⟩ :=
    slice_active_endpoints f g hf hg hmSlice
  have active_not_inside : ∀ q ∈ scalarSlice f g,
      (q=0 ∨ q=1 ∨ f q=0 ∨ g q=0) → ¬ q ∈ Ioo a b := by
    intro q hq hactive hqin
    have hqMax : Maximizes B (normalBlend A i q) j :=
      (maximizes_iff_two B _ j).mpr hq.2
    rcases hactive with h0 | h1 | hback | hahead
    · linarith [ha.1,hqin.1]
    · linarith [hb.2,hqin.2]
    · obtain ⟨k,c,hc,he⟩ := boundary_normal_ray B _ j
        (normalBlend_ne_zero A i) hqMax (Or.inl hback)
      exact consecutive_no_edgeRay A B i hab hqin ⟨k,c,hc,he⟩
    · obtain ⟨k,c,hc,he⟩ := boundary_normal_ray B _ j
        (normalBlend_ne_zero A i) hqMax (Or.inr hahead)
      exact consecutive_no_edgeRay A B i hab hqin ⟨k,c,hc,he⟩
  have hloa : lo ≤ a := by
    by_contra hn
    exact active_not_inside lo hlo hloActive ⟨by linarith,by linarith [hm.2]⟩
  have hbhi : b ≤ hi := by
    by_contra hn
    exact active_not_inside hi hhi hhiActive ⟨by linarith [hm.1],by linarith⟩
  have hlohi : lo < hi := by linarith
  have common : ∀ t ∈ Icc a b,
      Maximizes A (normalBlend A i t) i ∧ Maximizes B (normalBlend A i t) j := by
    intro t ht
    refine ⟨blend_maximizes A i ⟨by linarith [ha.1,ht.1],by linarith [hb.2,ht.2]⟩,?_⟩
    exact blend_maximizes_between A B i j hlohi
      ⟨by linarith [ht.1],by linarith [ht.2]⟩
      ((maximizes_iff_two B _ j).mpr hlo.2)
      ((maximizes_iff_two B _ j).mpr hhi.2)
  refine ⟨j,common,?_⟩
  intro t ht
  have ht01 : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨by linarith [ha.1,ht.1],by linarith [hb.2,ht.2]⟩
  have htClosed : t ∈ Icc a b := ⟨ht.1.le,ht.2.le⟩
  constructor
  · rw [supportFace_at_max A _ i (common t htClosed).1]
    exact positive_normal_exposes_singleton A i (by linarith [ht01.2]) ht01.1
  · obtain ⟨k,hk⟩ := singleton_of_not_edgeRay B _ (normalBlend_ne_zero A i)
      (consecutive_no_edgeRay A B i hab ht)
    have hj : B.vertex j ∈ supportFace B (normalBlend A i t) :=
      ⟨B.vertex_mem_body j,(common t htClosed).2⟩
    rw [hk] at hj
    have he : B.vertex j = B.vertex k := hj
    rw [hk,he]

/-- The scalar sort is existing pinned Mathlib machinery. This does NOT claim
that the whole two-polygon ring has been flattened or proved here. -/
def orderedKnots (i : Fin nA) : Fin (knots A B i).card ≃o (knots A B i) :=
  (knots A B i).orderIsoOfFin rfl

/-- Every block has at least its two distinct inherited endpoints. -/
theorem one_lt_knots_card (i : Fin nA) : 1 < (knots A B i).card := by
  rw [Finset.one_lt_card]
  refine ⟨0,?_,1,?_,by norm_num⟩ <;>
    simp [knots]

/-- One emitted gap for each adjacent pair in every locally sorted block. -/
abbrev Gap := Σ i : Fin nA, Fin ((knots A B i).card - 1)

def leftKnot (g : Gap A B) : ℝ :=
  let hc : (knots A B g.1).card - 1 + 1 = (knots A B g.1).card :=
    Nat.sub_add_cancel (one_lt_knots_card A B g.1).le
  orderedKnots A B g.1 (Fin.cast hc g.2.castSucc)

def rightKnot (g : Gap A B) : ℝ :=
  let hc : (knots A B g.1).card - 1 + 1 = (knots A B g.1).card :=
    Nat.sub_add_cancel (one_lt_knots_card A B g.1).le
  orderedKnots A B g.1 (Fin.cast hc g.2.succ)

/-- The dependent block flattening uses actual consecutive sorted knots. -/
theorem gap_consecutive (g : Gap A B) :
    Consecutive A B g.1 (leftKnot A B g) (rightKnot A B g) := by
  let hc : (knots A B g.1).card - 1 + 1 = (knots A B g.1).card :=
    Nat.sub_add_cancel (one_lt_knots_card A B g.1).le
  let l : Fin (knots A B g.1).card := Fin.cast hc g.2.castSucc
  let r : Fin (knots A B g.1).card := Fin.cast hc g.2.succ
  have hlr : l < r := by
    dsimp [l,r]
    simpa using g.2.castSucc_lt_succ
  refine ⟨(orderedKnots A B g.1 l).property,
    (orderedKnots A B g.1 r).property,?_,?_⟩
  · exact (orderedKnots A B g.1).lt_iff_lt.mpr hlr
  · intro t ht hbetween
    let q : (knots A B g.1) := ⟨t,ht⟩
    let k : Fin (knots A B g.1).card := (orderedKnots A B g.1).symm q
    have hkq : orderedKnots A B g.1 k = q := by
      dsimp [k]
      exact (orderedKnots A B g.1).apply_symm_apply q
    have hleftq : orderedKnots A B g.1 l < q := by
      change (↑(orderedKnots A B g.1 l) : ℝ) < t
      simpa [leftKnot,l,hc] using hbetween.1
    have hqright : q < orderedKnots A B g.1 r := by
      change t < (↑(orderedKnots A B g.1 r) : ℝ)
      simpa [rightKnot,r,hc] using hbetween.2
    have hlk : l < k := by
      apply (orderedKnots A B g.1).lt_iff_lt.mp
      rw [hkq]
      exact hleftq
    have hkr : k < r := by
      apply (orderedKnots A B g.1).lt_iff_lt.mp
      rw [hkq]
      exact hqright
    have hvals : l.val < k.val := hlk
    have hvals' : k.val < r.val := hkr
    change g.2.val < k.val at hvals
    change k.val < g.2.val + 1 at hvals'
    omega

/-- Each emitted dependent gap has a common raw A/B support pair, constructed
from the raw polygons rather than supplied as incidence data. -/
theorem gap_common_support (g : Gap A B) :
    ∃ j : Fin nB,
      (∀ t ∈ Icc (leftKnot A B g) (rightKnot A B g),
        Maximizes A (normalBlend A g.1 t) g.1 ∧
        Maximizes B (normalBlend A g.1 t) j) ∧
      (∀ t ∈ Ioo (leftKnot A B g) (rightKnot A B g),
        supportFace A (normalBlend A g.1 t) = {A.vertex g.1} ∧
        supportFace B (normalBlend A g.1 t) = {B.vertex j}) :=
  consecutive_knots_common_support A B g.1 (gap_consecutive A B g)

/-- Positive-ray classes along one raw cone have injective scalar coordinates. -/
theorem blend_positiveRay_injective (i : Fin nA) {s t c : ℝ} (hc : 0 < c)
    (he : normalBlend A i s = c • normalBlend A i t) : s = t := by
  have hs : position A i (normalBlend A i s) = s :=
    position_of_positive_blend A i (s := 1) (t := s) (by norm_num)
      _ (by simp)
  have ht : position A i (normalBlend A i s) = t :=
    position_of_positive_blend A i (s := c) (t := t) hc _ he
  exact hs.symm.trans ht

/-- Every computed knot is an inherited endpoint or an actual B-normal
insertion. This is a correspondence theorem about the internal finset. -/
theorem knot_source (i : Fin nA) {t : ℝ} (ht : t ∈ knots A B i) :
    t = 0 ∨ t = 1 ∨ ∃ j : Fin nB,
      StrictAt A (outwardNormal B.vertex j) i ∧
      t = position A i (outwardNormal B.vertex j) := by
  simp only [knots,Finset.mem_insert,Finset.mem_image,Finset.mem_filter,
    Finset.mem_univ,true_and] at ht
  rcases ht with h0 | h1 | ⟨j,hj,he⟩
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr ⟨j,hj,he.symm⟩)

/-- LEFT endpoints from every dependent gap already land in the internally
computed merged positive-ray set. No caller supplies a combined fan. -/
theorem leftKnot_ray_mem_mergedRays (g : Gap A B) :
    unitRay (normalBlend A g.1 (leftKnot A B g)) ∈ mergedRays A B := by
  have hcon := gap_consecutive A B g
  have hright := knots_subset_Icc A B g.1 hcon.2.1
  have hlt1 : leftKnot A B g < 1 := lt_of_lt_of_le hcon.2.2.1 hright.2
  rcases knot_source A B g.1 hcon.1 with h0 | h1 | ⟨j,hj,ht⟩
  · rw [h0]
    rw [mem_mergedRays]
    refine ⟨Sum.inl (prev g.1),?_⟩
    simp [normalBlend,inputNormal]
  · exact False.elim (by linarith)
  · obtain ⟨_,scale,hscale,hscaleEq⟩ := strict_position A g.1 _ hj
    rw [ht]
    rw [mem_mergedRays]
    refine ⟨Sum.inr j,?_⟩
    change unitRay (normalBlend A g.1 (position A g.1 (outwardNormal B.vertex j))) =
      unitRay (outwardNormal B.vertex j)
    exact ((unitRay_eq_iff (B.outwardNormal_ne_zero j)
      (normalBlend_ne_zero A g.1)).mpr ⟨scale,hscale,hscaleEq⟩).symm

/-- The finite block family is globally flattened as data. This is deliberately
not called a geometric cycle until bijectivity and adjacency are proved. -/
noncomputable def gapEnumeration :
    Fin (Fintype.card (Gap A B)) ≃ Gap A B :=
  (Fintype.equivFin (Gap A B)).symm

def zeroGap (i : Fin nA) : Gap A B :=
  ⟨i,⟨0,by have := one_lt_knots_card A B i; omega⟩⟩

theorem leftKnot_zeroGap (i : Fin nA) : leftKnot A B (zeroGap A B i) = 0 := by
  let z : (knots A B i) := ⟨0,by simp [knots]⟩
  let k0 : Fin (knots A B i).card := ⟨0,by
    have := one_lt_knots_card A B i
    omega⟩
  let kz : Fin (knots A B i).card := (orderedKnots A B i).symm z
  have hk : k0 ≤ kz := by
    change 0 ≤ kz.val
    exact Nat.zero_le _
  have hv := (orderedKnots A B i).monotone hk
  have hz : orderedKnots A B i kz = z :=
    (orderedKnots A B i).apply_symm_apply z
  rw [hz] at hv
  have hnonneg := (knots_subset_Icc A B i (orderedKnots A B i k0).property).1
  have heq : (↑(orderedKnots A B i k0) : ℝ) = 0 := le_antisymm hv hnonneg
  unfold leftKnot
  dsimp only [zeroGap]
  rw [← heq]
  congr 2

def gapSide (g : Gap A B) : Side A B :=
  ⟨unitRay (normalBlend A g.1 (leftKnot A B g)),
    leftKnot_ray_mem_mergedRays A B g⟩

lemma gap_eq_of_owner_left_eq {g q : Gap A B} (hi : g.1 = q.1)
    (ht : leftKnot A B g = leftKnot A B q) : g = q := by
  cases g with
  | mk gi gk =>
    cases q with
    | mk qi qk =>
      dsimp only at hi
      subst qi
      have hind :
          Fin.cast (Nat.sub_add_cancel (one_lt_knots_card A B gi).le) gk.castSucc =
          Fin.cast (Nat.sub_add_cancel (one_lt_knots_card A B gi).le) qk.castSucc := by
        apply (orderedKnots A B gi).injective
        simpa [leftKnot] using ht
      have hv := congrArg Fin.val hind
      simp only [Fin.val_cast,Fin.val_castSucc] at hv
      have hk : gk = qk := Fin.ext hv
      subst qk
      rfl

/-- Half-open ownership and strict-cone uniqueness rule out duplicate emitted
rays before any physical incidence theorem is used. -/
theorem gapSide_injective : Function.Injective (gapSide A B) := by
  intro g q heq
  have hu : unitRay (normalBlend A g.1 (leftKnot A B g)) =
      unitRay (normalBlend A q.1 (leftKnot A B q)) :=
    congrArg Subtype.val heq
  obtain ⟨c,hc,hray⟩ := (unitRay_eq_iff
    (normalBlend_ne_zero A g.1) (normalBlend_ne_zero A q.1)).mp hu
  have hgcon := gap_consecutive A B g
  have hqcon := gap_consecutive A B q
  have hgright := knots_subset_Icc A B g.1 hgcon.2.1
  have hqright := knots_subset_Icc A B q.1 hqcon.2.1
  have hglt : leftKnot A B g < 1 := lt_of_lt_of_le hgcon.2.2.1 hgright.2
  have hqlt : leftKnot A B q < 1 := lt_of_lt_of_le hqcon.2.2.1 hqright.2
  rcases knot_source A B g.1 hgcon.1 with hg0 | hg1 | ⟨jg,hjg,hgt⟩
  · rcases knot_source A B q.1 hqcon.1 with hq0 | hq1 | ⟨jq,hjq,hqt⟩
    · have hedges : outwardNormal A.vertex (prev g.1) =
          c • outwardNormal A.vertex (prev q.1) := by
        simpa [hg0,hq0,normalBlend] using hray
      have hp := edgeNormal_positiveRay_injective A hc hedges
      have hi : g.1 = q.1 := by
        have := congrArg next hp
        simpa using this
      exact gap_eq_of_owner_left_eq A B hi (hg0.trans hq0.symm)
    · exact False.elim (by linarith)
    · have hqt01 := (strict_position A q.1 _ hjq).1
      have hstrict : StrictAt A (normalBlend A q.1 (leftKnot A B q)) q.1 := by
        rw [hqt]
        exact blend_strict A q.1 hqt01
      have hrel : normalBlend A q.1 (leftKnot A B q) =
          c⁻¹ • outwardNormal A.vertex (prev g.1) := by
        have hs := congrArg (fun z : Plane => c⁻¹ • z) hray
        rw [hg0] at hs
        norm_num [normalBlend,smul_smul,hc.ne'] at hs
        exact hs.symm
      have hedge : EdgeRay A (normalBlend A q.1 (leftKnot A B q)) := by
        refine ⟨prev g.1,c⁻¹,inv_pos.mpr hc,?_⟩
        exact hrel
      exact False.elim (not_edgeRay_of_strict A _ q.1 hstrict hedge)
  · exact False.elim (by linarith)
  · rcases knot_source A B q.1 hqcon.1 with hq0 | hq1 | ⟨jq,hjq,hqt⟩
    · have hgt01 := (strict_position A g.1 _ hjg).1
      have hstrict : StrictAt A (normalBlend A g.1 (leftKnot A B g)) g.1 := by
        rw [hgt]
        exact blend_strict A g.1 hgt01
      have hedge : EdgeRay A (normalBlend A g.1 (leftKnot A B g)) := by
        refine ⟨prev q.1,c, hc,?_⟩
        rw [hq0] at hray
        norm_num [normalBlend] at hray
        exact hray
      exact False.elim (not_edgeRay_of_strict A _ g.1 hstrict hedge)
    · exact False.elim (by linarith)
    · have hgt01 := (strict_position A g.1 _ hjg).1
      have hqt01 := (strict_position A q.1 _ hjq).1
      have hgstrict : StrictAt A (normalBlend A g.1 (leftKnot A B g)) g.1 := by
        rw [hgt]
        exact blend_strict A g.1 hgt01
      have hqstrict : StrictAt A (normalBlend A q.1 (leftKnot A B q)) q.1 := by
        rw [hqt]
        exact blend_strict A q.1 hqt01
      have hqOnLeft : StrictAt A (normalBlend A g.1 (leftKnot A B g)) q.1 := by
        rw [hray]
        exact strictAt_pos_smul A q.1 _ hc hqstrict
      have howner : g.1 = q.1 := strict_owner_unique A _ hgstrict hqOnLeft
      have hray' : normalBlend A g.1 (leftKnot A B g) =
          c • normalBlend A g.1 (leftKnot A B q) := by
        simpa [howner] using hray
      have hleft := blend_positiveRay_injective A g.1 hc hray'
      exact gap_eq_of_owner_left_eq A B howner hleft

/-- Every internally deduplicated input positive ray is emitted by one of the
computed half-open dependent gaps. -/
theorem gapSide_surjective : Function.Surjective (gapSide A B) := by
  intro u
  obtain ⟨k,huk⟩ := (mem_mergedRays A B u.val).mp u.property
  cases k with
  | inl ia =>
      refine ⟨zeroGap A B (next ia),?_⟩
      apply Subtype.ext
      rw [huk]
      change unitRay (normalBlend A (next ia)
        (leftKnot A B (zeroGap A B (next ia)))) = unitRay (outwardNormal A.vertex ia)
      rw [leftKnot_zeroGap]
      norm_num [normalBlend]
  | inr jb =>
      let w := outwardNormal B.vertex jb
      by_cases hEdge : EdgeRay A w
      · obtain ⟨ia,c,hc,he⟩ := hEdge
        refine ⟨zeroGap A B (next ia),?_⟩
        apply Subtype.ext
        rw [huk]
        change unitRay (normalBlend A (next ia) (leftKnot A B (zeroGap A B (next ia)))) =
          unitRay (outwardNormal B.vertex jb)
        rw [leftKnot_zeroGap]
        norm_num [normalBlend]
        exact ((unitRay_eq_iff (B.outwardNormal_ne_zero jb)
          (A.outwardNormal_ne_zero ia)).mpr ⟨c,hc,he⟩).symm
      · obtain ⟨i,hi,_⟩ := existsUnique_strict_owner_of_not_edgeRay A w
          (B.outwardNormal_ne_zero jb) hEdge
        let t := position A i w
        have ht01 : t ∈ Ioo (0 : ℝ) 1 := (strict_position A i w hi).1
        have htmem : t ∈ knots A B i := by
          simp only [knots,Finset.mem_insert,Finset.mem_image,Finset.mem_filter,
            Finset.mem_univ,true_and]
          exact Or.inr (Or.inr ⟨jb,hi,rfl⟩)
        let xt : (knots A B i) := ⟨t,htmem⟩
        let x1 : (knots A B i) := ⟨1,by simp [knots]⟩
        let kt : Fin (knots A B i).card := (orderedKnots A B i).symm xt
        let k1 : Fin (knots A B i).card := (orderedKnots A B i).symm x1
        have htk : orderedKnots A B i kt = xt :=
          (orderedKnots A B i).apply_symm_apply xt
        have h1k : orderedKnots A B i k1 = x1 :=
          (orderedKnots A B i).apply_symm_apply x1
        have hkt : kt < k1 := by
          apply (orderedKnots A B i).lt_iff_lt.mp
          rw [htk,h1k]
          exact ht01.2
        have hbound : kt.val < (knots A B i).card - 1 := by
          have hk1 := k1.isLt
          have hvals : kt.val < k1.val := hkt
          omega
        let g : Gap A B := ⟨i,⟨kt.val,hbound⟩⟩
        have hleft : leftKnot A B g = t := by
          let hc : (knots A B i).card - 1 + 1 = (knots A B i).card :=
            Nat.sub_add_cancel (one_lt_knots_card A B i).le
          have hind : Fin.cast hc g.2.castSucc = kt := Fin.ext rfl
          unfold leftKnot
          dsimp only [g]
          rw [hind,htk]
        refine ⟨g,?_⟩
        apply Subtype.ext
        rw [huk]
        change unitRay (normalBlend A i (leftKnot A B g)) = unitRay w
        rw [hleft]
        obtain ⟨_,scale,hscale,hscaleEq⟩ := strict_position A i w hi
        exact ((unitRay_eq_iff (B.outwardNormal_ne_zero jb)
          (normalBlend_ne_zero A i)).mpr ⟨scale,hscale,hscaleEq⟩).symm

/-- The internally computed dependent gaps and the merged side labels are now
equivalent. This retires fan enumeration only; physical adjacency still needs
the maximal-cell and section-incidence proof below this boundary. -/
noncomputable def gapSideEquiv : Gap A B ≃ Side A B :=
  Equiv.ofBijective (gapSide A B) ⟨gapSide_injective A B,gapSide_surjective A B⟩

noncomputable def sideEnumeration :
    Fin (Fintype.card (Gap A B)) ≃ Side A B :=
  (gapEnumeration A B).trans (gapSideEquiv A B)

/-- Lexicographic block order: raw A block first, then local scalar-gap index.
Unlike `sideEnumeration`, this preserves the intended splice order. The next
missing theorem is that successor/wraparound in this order is exactly physical
adjacency. -/
abbrev OrderedGap := Σₗ i : Fin nA, Fin ((knots A B i).card - 1)

noncomputable def orderedGaps :
    Fin (Fintype.card (OrderedGap A B)) ≃o OrderedGap A B :=
  Fintype.orderIsoFinOfCardEq (OrderedGap A B) rfl

noncomputable def orderedSideEnumeration :
    Fin (Fintype.card (OrderedGap A B)) ≃ Side A B :=
  (orderedGaps A B).toEquiv.trans ((Equiv.refl (Gap A B)).trans (gapSideEquiv A B))

end Pair
end
end NormalFanSplice

#print axioms NormalFanSplice.raw_vertex_injective
#print axioms NormalFanSplice.singleton_of_not_edgeRay
#print axioms NormalFanSplice.strict_position
#print axioms NormalFanSplice.edgeNormal_positiveRay_injective
#print axioms NormalFanSplice.existsUnique_strict_owner_of_not_edgeRay
#print axioms NormalFanSplice.edgeRay_mem_knots
#print axioms NormalFanSplice.consecutive_knots_common_support
#print axioms NormalFanSplice.gap_consecutive
#print axioms NormalFanSplice.gap_common_support
#print axioms NormalFanSplice.gapSide_injective
#print axioms NormalFanSplice.gapSide_surjective
#print axioms NormalFanSplice.gapSideEquiv
#check @NormalFanSplice.consecutive_knots_common_support
#check @NormalFanSplice.orderedSideEnumeration
