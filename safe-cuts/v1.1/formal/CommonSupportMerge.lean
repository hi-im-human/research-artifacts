import PolygonSupportCompleteness
import EuclideanPrismatoidCoordinates
import Mathlib.Analysis.Convex.Join
import Mathlib.Topology.Order.Compact

/-!
# Combine the two polygons' support geometry without sorting their rays

System, 2026-09-19. COMPLETE PROOF-SCRIPT DRAFT; NOT COMPILED HERE.

A common normal cone is sliced by the coefficient sum in one polygon's
incident normal basis. The endpoints of the resulting compact real slice
are rays of one of the two INPUT polygons. Thus every direction is a
nonnegative combination of common maximizing input rays. This proves exact
merged-row sections and the exact physical Euclidean prismatoid body without
assuming a circular fan, merged completeness, or a facet/edge table.

The finite unit-ray union is constructed internally. It is not sorted here.
This does not yet construct maximal-facet dimensions, the lateral incidence
cycle, or the final chart/certificate package. No unfolding theorem is used.
-/

open Set
open scoped BigOperators
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open EuclideanPrismatoidCoordinates

namespace CommonSupportMerge
noncomputable section

/-! ## A compact slice has active endpoint constraints. -/

def scalarSlice (f g : ℝ → ℝ) : Set ℝ :=
  {t | t ∈ Icc (0 : ℝ) 1 ∧ f t ≤ 0 ∧ g t ≤ 0}

lemma strict_slice_neighbors (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hft : f t < 0) (hgt : g t < 0) :
    (∃ l ∈ scalarSlice f g, l < t) ∧ (∃ u ∈ scalarSlice f g, t < u) := by
  let O : Set ℝ := {x | 0 < x ∧ x < 1 ∧ f x < 0 ∧ g x < 0}
  have hO : IsOpen O :=
    isOpen_lt continuous_const continuous_id |>.inter
      ((isOpen_lt continuous_id continuous_const).inter
        ((isOpen_lt hf continuous_const).inter (isOpen_lt hg continuous_const)))
  obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.mp hO t ⟨ht0, ht1, hft, hgt⟩
  have hl : t-e/2 ∈ O := hball (by
    rw [Metric.mem_ball, Real.dist_eq]
    have ha : |t-e/2-t| = e/2 := by rw [abs_of_nonpos (by linarith)]; ring
    rw [ha]; linarith)
  have hu : t+e/2 ∈ O := hball (by
    rw [Metric.mem_ball, Real.dist_eq]
    have ha : |t+e/2-t| = e/2 := by rw [abs_of_nonneg (by linarith)]; ring
    rw [ha]; linarith)
  exact ⟨⟨t-e/2, ⟨⟨hl.1.le, hl.2.1.le⟩, hl.2.2.1.le, hl.2.2.2.le⟩, by linarith⟩,
    ⟨t+e/2, ⟨⟨hu.1.le, hu.2.1.le⟩, hu.2.2.1.le, hu.2.2.2.le⟩, by linarith⟩⟩

/-- Includes singleton slices; no nonempty-interior premise is hidden here. -/
theorem slice_active_endpoints (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    {t : ℝ} (ht : t ∈ scalarSlice f g) :
    ∃ l u : ℝ, l ∈ scalarSlice f g ∧ u ∈ scalarSlice f g ∧ l ≤ t ∧ t ≤ u ∧
      (l = 0 ∨ l = 1 ∨ f l = 0 ∨ g l = 0) ∧
      (u = 0 ∨ u = 1 ∨ f u = 0 ∨ g u = 0) := by
  have hc : IsCompact (scalarSlice f g) := by
    change IsCompact (Icc (0 : ℝ) 1 ∩ {x | f x ≤ 0 ∧ g x ≤ 0})
    exact isCompact_Icc.inter_right
      ((isClosed_le hf continuous_const).inter (isClosed_le hg continuous_const))
  obtain ⟨l, hl⟩ := hc.exists_isLeast ⟨t, ht⟩
  obtain ⟨u, hu⟩ := hc.exists_isGreatest ⟨t, ht⟩
  have active : ∀ v ∈ scalarSlice f g,
      ((∀ x ∈ scalarSlice f g, v ≤ x) ∨ (∀ x ∈ scalarSlice f g, x ≤ v)) →
      v = 0 ∨ v = 1 ∨ f v = 0 ∨ g v = 0 := by
    intro v hv hvext
    by_contra hn
    push_neg at hn
    obtain ⟨⟨a, ha, hav⟩, ⟨b, hb, hvb⟩⟩ := strict_slice_neighbors f g hf hg
      (lt_of_le_of_ne hv.1.1 (Ne.symm hn.1))
      (lt_of_le_of_ne hv.1.2 hn.2.1)
      (lt_of_le_of_ne hv.2.1 hn.2.2.1)
      (lt_of_le_of_ne hv.2.2 hn.2.2.2)
    rcases hvext with h | h
    · exact (not_lt_of_ge (h a ha)) hav
    · exact (not_lt_of_ge (h b hb)) hvb
  exact ⟨l, u, hl.1, hu.1, hl.2 ht, hu.2 ht,
    active l hl.1 (Or.inl (fun _ hx => hl.2 hx)),
    active u hu.1 (Or.inr (fun _ hx => hu.2 hx))⟩

/-! ## Local cones and their common slice. -/
section Single
variable {n : ℕ} [NeZero n] (P : ReducedConvexPolygon n)

def normalBlend (i : Fin n) (t : ℝ) : Plane :=
  (1-t) • outwardNormal P.vertex (prev i) + t • outwardNormal P.vertex i

lemma incident_det (i : Fin n) :
    det (outwardNormal P.vertex (prev i)) (outwardNormal P.vertex i) =
      -det (back P i) (ahead P i) := by
  simp only [outwardNormal, edgeVector, next_prev]
  simp [rotateCW, det, back, ahead]
  <;> ring

lemma normalBlend_ne_zero (i : Fin n) {t : ℝ} : normalBlend P i t ≠ 0 := by
  intro hz
  have hd := corner_det_pos P i
  have he := congrArg (fun x => det (outwardNormal P.vertex (prev i)) x) hz
  have hcalc : det (outwardNormal P.vertex (prev i)) (normalBlend P i t) =
      t * det (outwardNormal P.vertex (prev i)) (outwardNormal P.vertex i) := by
    simp [normalBlend, det]
    <;> ring
  have he' : t * det (outwardNormal P.vertex (prev i)) (outwardNormal P.vertex i) = 0 := by
    rw [hcalc] at he
    simpa [det] using he
  rw [incident_det P i] at he'
  have ht : t = 0 := (mul_eq_zero.mp he').resolve_right (by linarith)
  apply P.outwardNormal_ne_zero (prev i)
  simpa [normalBlend, ht] using hz

lemma maximizes_iff_two (w : Plane) (i : Fin n) : Maximizes P w i ↔
    inner ℝ w (back P i) ≤ 0 ∧ inner ℝ w (ahead P i) ≤ 0 := by
  constructor
  · intro hm
    have ha : inner ℝ w (back P i) ≤ 0 := by
      simpa [back, inner_sub_right, sub_nonpos] using
        hm _ (P.vertex_mem_body (prev i))
    have hb : inner ℝ w (ahead P i) ≤ 0 := by
      simpa [ahead, inner_sub_right, sub_nonpos] using
        hm _ (P.vertex_mem_body (next i))
    exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩
    apply (normalCone_iff P w i).mpr
    have hd := corner_det_pos P i
    refine ⟨-inner ℝ w (ahead P i)/det (back P i) (ahead P i),
      -inner ℝ w (back P i)/det (back P i) (ahead P i),
      div_nonneg (neg_nonneg.mpr hb) hd.le,
      div_nonneg (neg_nonneg.mpr ha) hd.le, ?_⟩
    have hn : outwardNormal P.vertex (prev i) = rotateCW (-back P i) := by
      simp only [outwardNormal, edgeVector, next_prev, back, neg_sub]
    rw [hn]
    exact normal_reconstruct _ _ _ hd.ne'

lemma blend_maximizes (i : Fin n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Maximizes P (normalBlend P i t) i :=
  (normalCone_iff P _ i).mpr ⟨1-t, t, by linarith [ht.2], ht.1, rfl⟩

lemma maximizes_of_pos_smul (w : Plane) (i : Fin n) {c : ℝ} (hc : 0 < c)
    (hm : Maximizes P (c • w) i) : Maximizes P w i := by
  intro x hx
  have h := hm x hx
  simp only [real_inner_smul_left] at h
  nlinarith

/-- A nonzero common boundary direction is a POSITIVE input normal ray. -/
lemma boundary_normal_ray (w : Plane) (i : Fin n) (hw : w ≠ 0)
    (hm : Maximizes P w i)
    (he : inner ℝ w (back P i) = 0 ∨ inner ℝ w (ahead P i) = 0) :
    ∃ k : Fin n, ∃ c : ℝ, 0 < c ∧ w = c • outwardNormal P.vertex k := by
  have htwo := (maximizes_iff_two P w i).mp hm
  have hd := corner_det_pos P i
  have hn : outwardNormal P.vertex (prev i) = rotateCW (-back P i) := by
    simp only [outwardNormal, edgeVector, next_prev, back, neg_sub]
  have hrec := normal_reconstruct (back P i) (ahead P i) w hd.ne'
  rcases he with ha | hb
  · let c := -inner ℝ w (ahead P i)/det (back P i) (ahead P i)
    have heq : w = c • outwardNormal P.vertex (prev i) := by
      rw [ha] at hrec
      simpa [c, hn] using hrec
    have hc : 0 < c := by
      have hcn : 0 ≤ c := div_nonneg (neg_nonneg.mpr htwo.2) hd.le
      by_contra hnot
      have hz : c = 0 := le_antisymm (by linarith) hcn
      exact hw (by simpa [hz] using heq)
    exact ⟨prev i, c, hc, heq⟩
  · let c := -inner ℝ w (back P i)/det (back P i) (ahead P i)
    have heq : w = c • outwardNormal P.vertex i := by
      rw [hb] at hrec
      simpa [c, outwardNormal, edgeVector, ahead] using hrec
    have hc : 0 < c := by
      have hcn : 0 ≤ c := div_nonneg (neg_nonneg.mpr htwo.1) hd.le
      by_contra hnot
      have hz : c = 0 := le_antisymm (by linarith) hcn
      exact hw (by simpa [hz] using heq)
    exact ⟨i, c, hc, heq⟩
end Single

section Pair
variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)

abbrev RayIndex := Fin nA ⊕ Fin nB

def inputNormal (k : RayIndex (nA := nA) (nB := nB)) : Plane :=
  Sum.elim (outwardNormal A.vertex) (outwardNormal B.vertex) k

lemma inputNormal_ne_zero (k : RayIndex (nA := nA) (nB := nB)) : inputNormal A B k ≠ 0 := by
  cases k with
  | inl i => exact A.outwardNormal_ne_zero i
  | inr j => exact B.outwardNormal_ne_zero j

/-- No ordering of the union, generic position, or strict common cone is assumed. -/
theorem common_input_ray_decomposition (w : Plane) (hw : w ≠ 0)
    (i : Fin nA) (j : Fin nB) (ha : Maximizes A w i) (hb : Maximizes B w j) :
    ∃ k l : RayIndex (nA := nA) (nB := nB), ∃ a b : ℝ,
      0 ≤ a ∧ 0 ≤ b ∧ w = a • inputNormal A B k + b • inputNormal A B l ∧
      Maximizes A (inputNormal A B k) i ∧ Maximizes B (inputNormal A B k) j ∧
      Maximizes A (inputNormal A B l) i ∧ Maximizes B (inputNormal A B l) j := by
  obtain ⟨lam, mu, hlam, hmu, hrec⟩ := (normalCone_iff A w i).mp ha
  let s := lam+mu
  have hs : 0 < s := by
    by_contra hn
    have hl0 : lam = 0 := by dsimp [s] at hn; linarith
    have hm0 : mu = 0 := by dsimp [s] at hn; linarith
    exact hw (by simpa [hl0, hm0] using hrec)
  let t := mu/s
  have ht : t ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hmu hs.le, (div_le_one hs).mpr (by dsimp [s]; linarith)⟩
  have hst : s*t = mu := by dsimp [t]; field_simp [hs.ne']
  have hsl : s*(1-t) = lam := by dsimp [s] at hst ⊢; nlinarith
  have hwt : w = s • normalBlend A i t := by
    rw [normalBlend, smul_add, smul_smul, smul_smul, hsl, hst]
    exact hrec
  have hbt : Maximizes B (normalBlend A i t) j :=
    maximizes_of_pos_smul B _ j hs (by rw [← hwt]; exact hb)
  let f : ℝ → ℝ := fun q => inner ℝ (normalBlend A i q) (back B j)
  let g : ℝ → ℝ := fun q => inner ℝ (normalBlend A i q) (ahead B j)
  have hf : Continuous f := by unfold f normalBlend; fun_prop
  have hg : Continuous g := by unfold g normalBlend; fun_prop
  have htf : t ∈ scalarSlice f g := ⟨ht, (maximizes_iff_two B _ j).mp hbt⟩
  obtain ⟨lo, hi, hlo, hhi, hlot, hthi, hloact, hhiact⟩ :=
    slice_active_endpoints f g hf hg htf
  have boundary : ∀ q ∈ scalarSlice f g,
      (q=0 ∨ q=1 ∨ f q=0 ∨ g q=0) →
      ∃ k : RayIndex (nA := nA) (nB := nB), ∃ c : ℝ,
        0 < c ∧ normalBlend A i q = c • inputNormal A B k ∧
        Maximizes A (inputNormal A B k) i ∧ Maximizes B (inputNormal A B k) j := by
    intro q hq hact
    have hqa := blend_maximizes A i hq.1
    have hqb := (maximizes_iff_two B _ j).mpr hq.2
    have hray : ∃ k : RayIndex (nA := nA) (nB := nB), ∃ c : ℝ,
        0 < c ∧ normalBlend A i q = c • inputNormal A B k := by
      rcases hact with h0 | h1 | hback | hahead
      · exact ⟨Sum.inl (prev i), 1, by norm_num, by simp [normalBlend, inputNormal, h0]⟩
      · exact ⟨Sum.inl i, 1, by norm_num, by simp [normalBlend, inputNormal, h1]⟩
      · obtain ⟨k,c,hc,he⟩ := boundary_normal_ray B _ j
          (normalBlend_ne_zero A i) hqb (Or.inl hback)
        exact ⟨Sum.inr k,c,hc,he⟩
      · obtain ⟨k,c,hc,he⟩ := boundary_normal_ray B _ j
          (normalBlend_ne_zero A i) hqb (Or.inr hahead)
        exact ⟨Sum.inr k,c,hc,he⟩
    obtain ⟨k,c,hc,he⟩ := hray
    exact ⟨k,c,hc,he, maximizes_of_pos_smul A _ i hc (by rw [← he]; exact hqa),
      maximizes_of_pos_smul B _ j hc (by rw [← he]; exact hqb)⟩
  obtain ⟨k,c,hc,hk,hka,hkb⟩ := boundary lo hlo hloact
  obtain ⟨l,d,hd,hl,hla,hlb⟩ := boundary hi hhi hhiact
  by_cases heq : lo = hi
  · have htlo : t = lo := by linarith
    refine ⟨k,l,s*c,0,mul_nonneg hs.le hc.le,le_rfl,?_,hka,hkb,hla,hlb⟩
    rw [zero_smul, add_zero, ← smul_smul, ← hk, ← htlo]
    exact hwt
  · have hgap : 0 < hi-lo := by
      exact sub_pos.mpr (lt_of_le_of_ne (hlot.trans hthi) heq)
    let a := (hi-t)/(hi-lo)
    let b := (t-lo)/(hi-lo)
    have han : 0 ≤ a := div_nonneg (sub_nonneg.mpr hthi) hgap.le
    have hbn : 0 ≤ b := div_nonneg (sub_nonneg.mpr hlot) hgap.le
    have hab : a+b=1 := by dsimp [a,b]; field_simp [hgap.ne']; ring
    have htcomb : a*lo+b*hi=t := by dsimp [a,b]; field_simp [hgap.ne']; ring
    have hblend : normalBlend A i t = a • normalBlend A i lo+b • normalBlend A i hi := by
      unfold normalBlend
      rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
      have hleft : a*(1-lo)+b*(1-hi) = 1-t := by nlinarith
      calc
        (1-t) • outwardNormal A.vertex (prev i)+t • outwardNormal A.vertex i =
          (a*(1-lo)+b*(1-hi)) • outwardNormal A.vertex (prev i)+
          (a*lo+b*hi) • outwardNormal A.vertex i := by rw [hleft,htcomb]
        _ = _ := by module
    refine ⟨k,l,s*a*c,s*b*d,mul_nonneg (mul_nonneg hs.le han) hc.le,
      mul_nonneg (mul_nonneg hs.le hbn) hd.le,?_,hka,hkb,hla,hlb⟩
    rw [hwt,hblend,hk,hl,smul_add,smul_smul,smul_smul,smul_smul,smul_smul]

/-! ## Canonical finite ray union and support values. -/

def unitRay (w : Plane) : Plane := ‖w‖⁻¹ • w

def mergedRays : Finset Plane :=
  Finset.univ.image (fun k : RayIndex (nA := nA) (nB := nB) => unitRay (inputNormal A B k))

lemma mem_mergedRays (u : Plane) : u ∈ mergedRays A B ↔
    ∃ k : RayIndex (nA := nA) (nB := nB), u = unitRay (inputNormal A B k) := by
  simp [mergedRays, eq_comm]

lemma unitRay_norm {w : Plane} (hw : w ≠ 0) : ‖unitRay w‖ = 1 := by
  simp [unitRay, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (norm_nonneg w), norm_ne_zero_iff.mpr hw]

lemma unitRay_eq_iff {v w : Plane} (hv : v ≠ 0) (hw : w ≠ 0) :
    unitRay v = unitRay w ↔ ∃ c : ℝ, 0 < c ∧ v = c • w := by
  constructor
  · intro he
    refine ⟨‖v‖/‖w‖, div_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hw), ?_⟩
    have ht := congrArg (fun x : Plane => ‖v‖ • x) he
    simpa [unitRay, smul_smul, div_eq_mul_inv, norm_ne_zero_iff.mpr hv] using ht
  · rintro ⟨c,hc,rfl⟩
    simp [unitRay,norm_smul,Real.norm_eq_abs,abs_of_pos hc,smul_smul,
      hc.ne',norm_ne_zero_iff.mpr hw,mul_inv_rev]

def supportIndex {n : ℕ} [NeZero n] (P : ReducedConvexPolygon n) (w : Plane) : Fin n :=
  Classical.choose (Finite.exists_max (fun i => inner ℝ w (P.vertex i)))

def supportValue {n : ℕ} [NeZero n] (P : ReducedConvexPolygon n) (w : Plane) : ℝ :=
  inner ℝ w (P.vertex (supportIndex P w))

lemma supportIndex_max {n : ℕ} [NeZero n] (P : ReducedConvexPolygon n) (w : Plane) :
    Maximizes P w (supportIndex P w) :=
  P.body_le_of_vertices (innerSL ℝ w).toLinearMap _
    (Classical.choose_spec (Finite.exists_max (fun i => inner ℝ w (P.vertex i))))

lemma supportValue_at {n : ℕ} [NeZero n] (P : ReducedConvexPolygon n)
    (w : Plane) (i : Fin n) (hi : Maximizes P w i) :
    supportValue P w = inner ℝ w (P.vertex i) :=
  le_antisymm (hi _ (P.vertex_mem_body _)) ((supportIndex_max P w) _ (P.vertex_mem_body i))

lemma supportValue_pos_smul {n : ℕ} [NeZero n] (P : ReducedConvexPolygon n)
    (w : Plane) {c : ℝ} (hc : 0 < c) : supportValue P (c • w) = c*supportValue P w := by
  have hm : Maximizes P (c • w) (supportIndex P w) := by
    intro x hx
    simpa only [real_inner_smul_left] using
      mul_le_mul_of_nonneg_left ((supportIndex_max P w) x hx) hc.le
  rw [supportValue_at P _ _ hm]
  simp only [real_inner_smul_left, supportValue]

/-! ## Exact sections from the finite input-normal rows. -/

def mixLinear (t : ℝ) : (Plane × Plane) →ₗ[ℝ] Plane where
  toFun p := (1-t) • p.1 + t • p.2
  map_add' := by
    intro p q
    change (1-t) • (p.1+q.1)+t • (p.2+q.2) =
      ((1-t) • p.1+t • p.2)+((1-t) • q.1+t • q.2)
    module
  map_smul' := by
    intro c p
    change (1-t) • (c • p.1)+t • (c • p.2) = c • ((1-t) • p.1+t • p.2)
    module

def sectionSet (t : ℝ) : Set Plane := mixLinear t '' (B.body ×ˢ A.body)

def rowBound (t : ℝ) (w : Plane) : ℝ :=
  (1-t)*supportValue B w+t*supportValue A w

def rowFeasible (t : ℝ) : Set Plane :=
  {x | ∀ k : RayIndex (nA := nA) (nB := nB), inner ℝ (inputNormal A B k) x ≤
      rowBound A B t (inputNormal A B k)}

def mergedFeasible (t : ℝ) : Set Plane :=
  {x | ∀ u ∈ mergedRays A B, inner ℝ u x ≤ rowBound A B t u}

lemma section_convex (t : ℝ) : Convex ℝ (sectionSet A B t) :=
  (B.body_convex.prod A.body_convex).linear_image (mixLinear t)

lemma section_compact (t : ℝ) : IsCompact (sectionSet A B t) := by
  have ha := (Set.finite_range A.vertex).isCompact_convexHull ℝ
  have hb := (Set.finite_range B.vertex).isCompact_convexHull ℝ
  apply (hb.prod ha).image
  change Continuous (fun p : Plane × Plane => (1-t) • p.1+t • p.2)
  fun_prop

lemma section_support_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (w : Plane)
    {x : Plane} (hx : x ∈ sectionSet A B t) : inner ℝ w x ≤ rowBound A B t w := by
  obtain ⟨⟨b,a⟩,⟨hb,ha⟩,rfl⟩ := hx
  change inner ℝ w ((1-t) • b+t • a) ≤ _
  simp only [inner_add_right,inner_smul_right,rowBound]
  exact add_le_add
    (mul_le_mul_of_nonneg_left ((supportIndex_max B w) b hb) (by linarith [ht.2]))
    (mul_le_mul_of_nonneg_left ((supportIndex_max A w) a ha) ht.1)

/-- The raw merged rows imply every directional support inequality. -/
theorem all_supports_of_input_rows {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {x : Plane} (hx : x ∈ rowFeasible A B t) (w : Plane) :
    inner ℝ w x ≤ rowBound A B t w := by
  by_cases hw : w=0
  · simp [hw,rowBound,supportValue]
  let i := supportIndex A w
  let j := supportIndex B w
  obtain ⟨k,l,a,b,ha,hb,he,hka,hkb,hla,hlb⟩ := common_input_ray_decomposition A B w hw
    i j (supportIndex_max A w) (supportIndex_max B w)
  have hbound : rowBound A B t w =
      a*rowBound A B t (inputNormal A B k)+b*rowBound A B t (inputNormal A B l) := by
    unfold rowBound
    rw [supportValue_at B _ j (supportIndex_max B w),
      supportValue_at A _ i (supportIndex_max A w),
      supportValue_at B _ j hkb,supportValue_at A _ i hka,
      supportValue_at B _ j hlb,supportValue_at A _ i hla,he]
    simp only [inner_add_left,real_inner_smul_left]
    ring
  rw [hbound,he,inner_add_left,real_inner_smul_left,real_inner_smul_left]
  exact add_le_add (mul_le_mul_of_nonneg_left (hx k) ha)
    (mul_le_mul_of_nonneg_left (hx l) hb)

/-- Finite merged-row section completeness. The section is defined independently. -/
theorem section_eq_input_halfspaces {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    sectionSet A B t = rowFeasible A B t := by
  ext x
  constructor
  · intro hx k
    exact section_support_le A B ht _ hx
  · intro hx
    by_contra hout
    obtain ⟨f,c,hfc,hcx⟩ := geometric_hahn_banach_closed_point
      (section_convex A B t) (section_compact A B t).isClosed hout
    let w : Plane := WithLp.toLp 2 ![f (WithLp.toLp 2 ![1,0]),f (WithLp.toLp 2 ![0,1])]
    have hf : ∀ y : Plane, f y = inner ℝ w y := by
      intro y
      have hy : y = y 0 • (WithLp.toLp 2 ![1,0] : Plane)+
          y 1 • (WithLp.toLp 2 ![0,1] : Plane) := by
        ext k; fin_cases k <;> simp
      rw [hy,map_add,map_smul,map_smul]
      simp [w,inner,Fin.sum_univ_two]
      <;> ring
    let y := mixLinear t (B.vertex (supportIndex B w), A.vertex (supportIndex A w))
    have hy : y ∈ sectionSet A B t :=
      ⟨_,⟨B.vertex_mem_body _,A.vertex_mem_body _⟩,rfl⟩
    have hye : f y = rowBound A B t w := by
      rw [hf]
      simp [y,mixLinear,rowBound,supportValue,inner_add_right,inner_smul_right]
    have hlt := hfc y hy
    rw [hye] at hlt
    rw [hf] at hcx
    have hle := all_supports_of_input_rows A B ht hx w
    linarith

/-- Unit normalization merges positive duplicates, without identifying opposite rays. -/
theorem input_eq_merged_halfspaces (t : ℝ) : rowFeasible A B t = mergedFeasible A B t := by
  ext x
  constructor
  · intro hx u hu
    obtain ⟨k,rfl⟩ := (mem_mergedRays A B u).mp hu
    let c := ‖inputNormal A B k‖⁻¹
    have hc : 0 < c := inv_pos.mpr (norm_pos_iff.mpr (inputNormal_ne_zero A B k))
    change inner ℝ (c • inputNormal A B k) x ≤ rowBound A B t (c • inputNormal A B k)
    rw [real_inner_smul_left]
    unfold rowBound
    rw [supportValue_pos_smul B _ hc,supportValue_pos_smul A _ hc]
    have h := mul_le_mul_of_nonneg_left (hx k) hc.le
    dsimp [rowBound] at h
    nlinarith
  · intro hx k
    have h := hx (unitRay (inputNormal A B k)) ((mem_mergedRays A B _).mpr ⟨k,rfl⟩)
    let c := ‖inputNormal A B k‖⁻¹
    have hc : 0 < c := inv_pos.mpr (norm_pos_iff.mpr (inputNormal_ne_zero A B k))
    change inner ℝ (c • inputNormal A B k) x ≤ rowBound A B t (c • inputNormal A B k) at h
    rw [real_inner_smul_left] at h
    unfold rowBound at h
    rw [supportValue_pos_smul B _ hc,supportValue_pos_smul A _ hc] at h
    have h' : c*inner ℝ (inputNormal A B k) x ≤ c*rowBound A B t (inputNormal A B k) := by
      dsimp [rowBound]; nlinarith [h]
    nlinarith

/-- PRINCIPAL PLANAR ENDPOINT: actual Minkowski section = internally merged rows. -/
theorem section_eq_merged_halfspaces {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    sectionSet A B t = mergedFeasible A B t :=
  (section_eq_input_halfspaces A B ht).trans (input_eq_merged_halfspaces A B t)

/-! ## Transfer exact sections to the independent physical Euclidean hull. -/

def lowerAffine : Plane →ᵃ[ℝ] Ambient where
  toFun := lowerLift
  linear := LinearMap.inl ℝ Plane ℝ
  map_vadd' := by intros; ext <;> simp [lowerLift, vadd_eq_add]

def upperAffine (h : ℝ) : Plane →ᵃ[ℝ] Ambient where
  toFun := upperLift h
  linear := LinearMap.inl ℝ Plane ℝ
  map_vadd' := by intros; ext <;> simp [upperLift, vadd_eq_add]

/-- Pure affine interpolation; no max-product metric is used as a physical metric. -/
theorem mem_prismatoid_iff {h : ℝ} (hh : 0 < h) (x : Plane) (z : ℝ) :
    (x,z) ∈ prismatoid A B h ↔ z/h ∈ Icc (0 : ℝ) 1 ∧ x ∈ sectionSet A B (z/h) := by
  have hl : Convex ℝ (lowerLift '' B.body) := B.body_convex.affine_image lowerAffine
  have hu : Convex ℝ (upperLift h '' A.body) := A.body_convex.affine_image (upperAffine h)
  have he := hl.convexHull_union hu (B.body_nonempty.image lowerLift)
    (A.body_nonempty.image (upperLift h))
  change (x,z) ∈ convexHull ℝ (lowerLift '' B.body ∪ upperLift h '' A.body) ↔ _
  rw [he,mem_convexJoin]
  constructor
  · rintro ⟨_,⟨b,hb,rfl⟩,_,⟨a,ha,rfl⟩,hs⟩
    rcases hs with ⟨r,s,hr,hs,hrs,hcoord⟩
    have hz : s*h=z := by
      have ht := congrArg Prod.snd hcoord
      simpa [lowerLift,upperLift,smul_eq_mul] using ht
    have hsval : z/h=s := (div_eq_iff hh.ne').mpr hz.symm
    have hrval : r=1-s := by linarith
    refine ⟨by rw [hsval]; exact ⟨hs,by linarith⟩,?_⟩
    refine ⟨(b,a),⟨hb,ha⟩,?_⟩
    have ht := congrArg Prod.fst hcoord
    simpa [mixLinear,lowerLift,upperLift,hsval,hrval] using ht
  · rintro ⟨ht,⟨⟨b,a⟩,⟨hb,ha⟩,hm⟩⟩
    refine ⟨lowerLift b,⟨b,hb,rfl⟩,upperLift h a,⟨a,ha,rfl⟩,
      1-z/h,z/h,by linarith [ht.2],ht.1,by ring,?_⟩
    apply Prod.ext
    · exact hm
    · change (1-z/h)*0+(z/h)*h=z
      field_simp [hh.ne']
      <;> ring

/-- Independently constructed finite halfspaces in TRUE Euclidean three-space. -/
def physicalRowBody (h : ℝ) : Set PhysicalAmbient :=
  {p | let q := unpack p
       q.2/h ∈ Icc (0 : ℝ) 1 ∧
       ∀ u ∈ mergedRays A B, inner ℝ u q.1 ≤ rowBound A B (q.2/h) u}

/-- WHOLE PACKET ENDPOINT. No supplied fan, row completeness, or 3D body equality.
The output is an exact finite, positive-ray-deduplicated Euclidean row body.
Maximal-face classification and a cyclic ordering are explicitly not asserted. -/
theorem physicalPrismatoid_eq_merged_halfspaces {h : ℝ} (hh : 0 < h) :
    physicalPrismatoid A B h = physicalRowBody A B h := by
  rw [← pack_prismatoid A B h]
  ext p
  have he : p ∈ pack '' prismatoid A B h ↔ unpack p ∈ prismatoid A B h := by
    constructor
    · rintro ⟨q,hq,rfl⟩
      have hcoord : unpack (pack q) = q := coordinateEquiv.symm_apply_apply q
      simpa only [hcoord] using hq
    · intro hp
      exact ⟨unpack p,hp,coordinateEquiv.apply_symm_apply p⟩
  rw [he,mem_prismatoid_iff A B hh]
  change (unpack p).2/h ∈ Icc (0 : ℝ) 1 ∧
      (unpack p).1 ∈ sectionSet A B ((unpack p).2/h) ↔
    (unpack p).2/h ∈ Icc (0 : ℝ) 1 ∧
      (unpack p).1 ∈ mergedFeasible A B ((unpack p).2/h)
  constructor <;> rintro ⟨ht,hx⟩
  · exact ⟨ht,by rwa [section_eq_merged_halfspaces A B ht] at hx⟩
  · exact ⟨ht,by rwa [← section_eq_merged_halfspaces A B ht] at hx⟩
end Pair
end
end CommonSupportMerge

#print axioms CommonSupportMerge.slice_active_endpoints
#print axioms CommonSupportMerge.common_input_ray_decomposition
#print axioms CommonSupportMerge.unitRay_eq_iff
#print axioms CommonSupportMerge.all_supports_of_input_rows
#print axioms CommonSupportMerge.section_eq_merged_halfspaces
#print axioms CommonSupportMerge.mem_prismatoid_iff
#print axioms CommonSupportMerge.physicalPrismatoid_eq_merged_halfspaces
#check @CommonSupportMerge.section_eq_merged_halfspaces
#check @CommonSupportMerge.physicalPrismatoid_eq_merged_halfspaces
