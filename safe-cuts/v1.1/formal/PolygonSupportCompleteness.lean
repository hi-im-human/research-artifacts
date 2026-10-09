import MergedNormalPrismatoid
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fintype.Lattice
import Mathlib.Analysis.Convex.Topology

/-!
# Polygon completeness without first sorting the circular normal fan

System, 2026-09-19. UNCOMPILED proof-script draft for the existing pins.

The raw source's rotateCW is actually (-y,x), a counterclockwise rotation.
Together with supports <= 0 this accepts CLOCKWISE cyclic lists. This file
uses those exact definitions unchanged. The sign is not silently corrected.

The two incident edge inequalities give nonnegative tangent coordinates at
EVERY vertex. At a vertex maximizing a separating functional these coordinates
exclude a feasible point outside the hull. No sorted fan or completeness
field is an input. The same two-vector calculation gives the exact local
normal cones and their global coverage, and the entire tight edge segment.
-/

open Set
open scoped BigOperators
open MergedNormalPrismatoid

namespace PolygonSupportCompleteness

noncomputable section

-- Keep all existing checked sources and raw fields unchanged.
def det (a b : Plane) : ℝ := a 0 * b 1 - a 1 * b 0

lemma inner_rotate (a b : Plane) :
    inner ℝ (rotateCW a) b = det a b := by
  simp [rotateCW, det, inner, Fin.sum_univ_two]
  <;> ring

lemma det_swap (a b : Plane) : det a b = -det b a := by
  dsimp [det]
  ring

lemma det_reconstruct (a b d : Plane) (hD : det a b ≠ 0) :
    d = (det d b / det a b) • a + (det a d / det a b) • b := by
  ext k
  fin_cases k
  · change d 0 = (det d b / det a b) * a 0 + (det a d / det a b) * b 0
    have hD' : b 1 * a 0 - b 0 * a 1 ≠ 0 := by
      dsimp [det] at hD
      intro hz
      apply hD
      calc
        a 0 * b 1 - a 1 * b 0 = b 1 * a 0 - b 0 * a 1 := by ring
        _ = 0 := hz
    dsimp [det] at hD ⊢
    field_simp [hD, hD']
    <;> ring
  · change d 1 = (det d b / det a b) * a 1 + (det a d / det a b) * b 1
    have hD' : b 1 * a 0 - b 0 * a 1 ≠ 0 := by
      dsimp [det] at hD
      intro hz
      apply hD
      calc
        a 0 * b 1 - a 1 * b 0 = b 1 * a 0 - b 0 * a 1 := by ring
        _ = 0 := hz
    dsimp [det] at hD ⊢
    field_simp [hD, hD']
    <;> ring

lemma normal_reconstruct (a b w : Plane) (hD : det a b ≠ 0) :
    w = (-inner ℝ w b / det a b) • rotateCW (-a) +
      (-inner ℝ w a / det a b) • rotateCW b := by
  have hab : inner ℝ w a = w 0 * a 0 + w 1 * a 1 := by
    simp [inner, Fin.sum_univ_two]
    ring
  have hbb : inner ℝ w b = w 0 * b 0 + w 1 * b 1 := by
    simp [inner, Fin.sum_univ_two]
    ring
  rw [hab, hbb]
  ext k
  fin_cases k
  · change w 0 = (-(w 0*b 0+w 1*b 1)/det a b) * (-(-a 1)) +
      (-(w 0*a 0+w 1*a 1)/det a b) * (-b 1)
    simp only [neg_neg]
    have hD' : b 1 * a 0 - b 0 * a 1 ≠ 0 := by
      dsimp [det] at hD
      intro hz
      apply hD
      calc
        a 0 * b 1 - a 1 * b 0 = b 1 * a 0 - b 0 * a 1 := by ring
        _ = 0 := hz
    dsimp [det] at hD ⊢
    field_simp [hD, hD']
    <;> ring
  · change w 1 = (-(w 0*b 0+w 1*b 1)/det a b) * (-a 0) +
      (-(w 0*a 0+w 1*a 1)/det a b) * b 0
    have hD' : b 1 * a 0 - b 0 * a 1 ≠ 0 := by
      dsimp [det] at hD
      intro hz
      apply hD
      calc
        a 0 * b 1 - a 1 * b 0 = b 1 * a 0 - b 0 * a 1 := by ring
        _ = 0 := hz
    dsimp [det] at hD ⊢
    field_simp [hD, hD']
    <;> ring

section Cyclic
variable {n : ℕ} [NeZero n]

def prev (i : Fin n) : Fin n :=
  if hi : i.val = 0 then ⟨n-1, by have := NeZero.pos n; omega⟩
  else ⟨i.val-1, by have := i.isLt; omega⟩

lemma next_val (i : Fin n) :
    (next i).val = if i.val+1 < n then i.val+1 else 0 := by
  dsimp [next]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have hEq : i.val+1 = n := by have := i.isLt; omega
    simp [hEq]

@[simp] lemma next_prev (i : Fin n) : next (prev i) = i := by
  apply Fin.ext
  by_cases hi : i.val = 0
  · have hn : 1 ≤ n := NeZero.pos n
    have he : n-1+1 = n := by omega
    simp [prev, hi, next, he]
  · have he : i.val-1+1 = i.val := by omega
    simp [prev, hi, next, he, Nat.mod_eq_of_lt i.isLt]

lemma next_ne (hn : 2 ≤ n) (i : Fin n) : next i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  rw [next_val] at hv
  split_ifs at hv <;> have := i.isLt <;> omega

lemma prev_ne (hn : 2 ≤ n) (i : Fin n) : prev i ≠ i := by
  intro h
  have he := congrArg next h
  rw [next_prev] at he
  exact next_ne hn i he.symm

lemma prev_ne_next (hn : 3 ≤ n) (i : Fin n) : prev i ≠ next i := by
  intro h
  have hv := congrArg Fin.val h
  rw [next_val] at hv
  by_cases hi : i.val = 0
  · simp [prev, hi] at hv
    split_ifs at hv <;> omega
  · simp only [prev, dif_neg hi] at hv
    split_ifs at hv <;> have := i.isLt <;> omega

lemma self_ne_next_next (hn : 3 ≤ n) (i : Fin n) : i ≠ next (next i) := by
  intro h
  have h1 := next_val i
  have h2 := next_val (next i)
  have hv := congrArg Fin.val h
  rw [h2, h1] at hv
  split_ifs at hv <;> have := i.isLt <;> omega

end Cyclic

namespace ReducedConvexPolygon
variable {n : ℕ} [NeZero n] (P : MergedNormalPrismatoid.ReducedConvexPolygon n)

def back (i : Fin n) : Plane := P.vertex (prev i) - P.vertex i
def ahead (i : Fin n) : Plane := P.vertex (next i) - P.vertex i

def feasible : Set Plane := {x | ∀ i, P.edgeRow i x ≤ 0}

lemma edgeRow_det (i : Fin n) (x : Plane) :
    P.edgeRow i x = det (edgeVector P.vertex i) (x-P.vertex i) := by
  rw [P.edgeRow_apply]
  exact inner_rotate _ _

lemma right_row (i : Fin n) (x : Plane) :
    P.edgeRow i x = -det (x-P.vertex i) (ahead P i) := by
  rw [edgeRow_det]
  exact det_swap _ _

lemma left_row (i : Fin n) (x : Plane) :
    P.edgeRow (prev i) x = -det (back P i) (x-P.vertex i) := by
  rw [edgeRow_det]
  dsimp [edgeVector]
  rw [next_prev]
  simp [det, back]
  <;> ring

/-- Strict reducedness supplies a genuine corner, not a flat tangent line. -/
theorem corner_det_pos (i : Fin n) : 0 < det (back P i) (ahead P i) := by
  have hle := P.body_edge_nonpos i (P.vertex_mem_body (prev i))
  have hne : P.edgeRow i (P.vertex (prev i)) ≠ 0 := by
    intro hz
    rcases (P.vertex_edge_eq_iff i (prev i)).mp hz with h | h
    · exact prev_ne (by have := P.three_le; omega) i h
    · exact prev_ne_next P.three_le i h
  have hlt : P.edgeRow i (P.vertex (prev i)) < 0 := by
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact False.elim (hne h)
  rw [right_row] at hlt
  change -det (back P i) (ahead P i) < 0 at hlt
  linarith

/-- Two local incident constraints imply nonnegative coordinates in the
inward tangent cone. No global fan/order/separation fact is assumed. -/
theorem local_tangent_coordinates (i : Fin n) (x : Plane)
    (hLeft : P.edgeRow (prev i) x ≤ 0) (hRight : P.edgeRow i x ≤ 0) :
    ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧
      x-P.vertex i = α • back P i + β • ahead P i := by
  have hD := corner_det_pos P i
  rw [left_row] at hLeft
  rw [right_row] at hRight
  refine ⟨det (x-P.vertex i) (ahead P i) / det (back P i) (ahead P i),
    det (back P i) (x-P.vertex i) / det (back P i) (ahead P i),
    div_nonneg (by linarith) hD.le, div_nonneg (by linarith) hD.le, ?_⟩
  exact det_reconstruct _ _ _ hD.ne'

/-- At a vertex that maximizes f over the raw vertices, any point satisfying
all edge constraints is also bounded by that SAME maximum. -/
theorem feasible_le_vertex_max (f : Plane →ₗ[ℝ] ℝ) (i : Fin n)
    (hm : ∀ j, f (P.vertex j) ≤ f (P.vertex i))
    {x : Plane} (hx : x ∈ feasible P) : f x ≤ f (P.vertex i) := by
  obtain ⟨α, β, hα, hβ, heq⟩ :=
    local_tangent_coordinates P i x (hx (prev i)) (hx i)
  have ha : f (back P i) ≤ 0 := by
    simpa [back, map_sub, sub_nonpos] using hm (prev i)
  have hb : f (ahead P i) ≤ 0 := by
    simpa [ahead, map_sub, sub_nonpos] using hm (next i)
  have hfd : f (x-P.vertex i) ≤ 0 := by
    rw [heq, map_add, map_smul, map_smul]
    change α*f (back P i) + β*f (ahead P i) ≤ 0
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hα ha)
      (mul_nonpos_of_nonneg_of_nonpos hβ hb)
  rw [map_sub] at hfd
  linarith

/-- MAIN REVERSE INCLUSION. The finite circular normal fan is not a premise.
A separating functional and its finite vertex maximum suffice. -/
theorem mem_body_of_edgeRows {x : Plane} (hx : ∀ i, P.edgeRow i x ≤ 0) :
    x ∈ P.body := by
  classical
  by_contra hnot
  have hclosed : IsClosed P.body := by
    exact ((Set.finite_range P.vertex).isCompact_convexHull ℝ).isClosed
  obtain ⟨f, c, hfc, hcx⟩ :=
    geometric_hahn_banach_closed_point P.body_convex hclosed hnot
  obtain ⟨i, hi⟩ := Finite.exists_max (fun j => f (P.vertex j))
  have hle := feasible_le_vertex_max P f.toLinearMap i hi hx
  change f x ≤ f (P.vertex i) at hle
  have hlt := hfc (P.vertex i) (P.vertex_mem_body i)
  linarith

/-- The independently defined convex hull equals the COMPUTED edge rows. -/
theorem body_eq_edgeHalfspaces : P.body = feasible P := by
  ext x
  exact ⟨fun hx i => P.body_edge_nonpos i hx, mem_body_of_edgeRows P⟩

/-- A supporting edge's full tight face, not just its tight listed vertices. -/
theorem edge_tight_eq_segment (i : Fin n) :
    {x ∈ P.body | P.edgeRow i x = 0} =
      AffineMap.lineMap (P.vertex i) (P.vertex (next i)) '' Icc (0 : ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨hx, hzero⟩
    obtain ⟨α, β, hα, hβ, heq⟩ := local_tangent_coordinates P i x
      (P.body_edge_nonpos (prev i) hx) (P.body_edge_nonpos i hx)
    have hD := corner_det_pos P i
    have halpha : α = 0 := by
      rw [right_row, heq] at hzero
      have hd : det (α • back P i + β • ahead P i) (ahead P i) =
          α * det (back P i) (ahead P i) := by
        simp [det]
        <;> ring
      rw [hd] at hzero
      rcases mul_eq_zero.mp (by linarith : α*det (back P i) (ahead P i)=0) with h | h
      · exact h
      · exact False.elim (hD.ne' h)
    rw [halpha, zero_smul, zero_add] at heq
    have hxline : x = P.vertex i + β • ahead P i := by
      have ht := congrArg (fun y : Plane => y + P.vertex i) heq
      simpa [add_comm] using ht
    have hcnon := P.body_edge_nonpos (next i) (P.vertex_mem_body i)
    have hcne : P.edgeRow (next i) (P.vertex i) ≠ 0 := by
      intro hz
      rcases (P.vertex_edge_eq_iff (next i) i).mp hz with hi | hi
      · exact next_ne (by have := P.three_le; omega) i hi.symm
      · exact self_ne_next_next P.three_le i hi
    have hc : P.edgeRow (next i) (P.vertex i) < 0 := by
      rcases lt_or_eq_of_le hcnon with h | h
      · exact h
      · exact False.elim (hcne h)
    have heval : P.edgeRow (next i) x =
        (1-β)*P.edgeRow (next i) (P.vertex i) := by
      rw [hxline]
      change P.edgeLinear (next i) (P.vertex i + β • (P.vertex (next i)-P.vertex i)) -
          P.edgeLinear (next i) (P.vertex (next i)) =
        (1-β)*(P.edgeLinear (next i) (P.vertex i)-P.edgeLinear (next i) (P.vertex (next i)))
      simp only [map_add, map_smul, map_sub, smul_eq_mul]
      ring
    have hb1 : β ≤ 1 := by
      have hrow := P.body_edge_nonpos (next i) hx
      rw [heval] at hrow
      by_contra hnot
      have hmul := mul_pos_of_neg_of_neg (by linarith : 1-β < 0) hc
      linarith
    refine ⟨β, ⟨hβ, hb1⟩, ?_⟩
    rw [AffineMap.lineMap_apply]
    simpa [vsub_eq_sub, vadd_eq_add, ahead, add_comm] using hxline.symm
  · rintro ⟨t, ht, rfl⟩
    have hm : AffineMap.lineMap (P.vertex i) (P.vertex (next i)) t ∈ P.body := by
      rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      have he : t • (P.vertex (next i)-P.vertex i)+P.vertex i =
          (1-t) • P.vertex i + t • P.vertex (next i) := by module
      rw [he]
      exact P.body_convex (P.vertex_mem_body i) (P.vertex_mem_body (next i))
        (by linarith [ht.2]) ht.1 (by ring)
    refine ⟨hm, ?_⟩
    rw [edgeRow_det, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    simp [det, edgeVector]
    <;> ring

/-- A vertex maximizes the direction w over the ACTUAL convex hull. -/
def Maximizes (w : Plane) (i : Fin n) : Prop :=
  ∀ x ∈ P.body, inner ℝ w x ≤ inner ℝ w (P.vertex i)

/-- Exact normal-cone description, derived without an angular ordering. -/
theorem normalCone_iff (w : Plane) (i : Fin n) : Maximizes P w i ↔
    ∃ lam μ : ℝ, 0 ≤ lam ∧ 0 ≤ μ ∧
      w = lam • outwardNormal P.vertex (prev i) + μ • outwardNormal P.vertex i := by
  have hD := corner_det_pos P i
  have hnleft : outwardNormal P.vertex (prev i) = rotateCW (-back P i) := by
    simp only [outwardNormal, edgeVector, next_prev, back, neg_sub]
  have hnright : outwardNormal P.vertex i = rotateCW (ahead P i) := rfl
  constructor
  · intro hm
    have ha : inner ℝ w (back P i) ≤ 0 := by
      simpa [back, inner_sub_right, sub_nonpos] using hm _ (P.vertex_mem_body (prev i))
    have hb : inner ℝ w (ahead P i) ≤ 0 := by
      simpa [ahead, inner_sub_right, sub_nonpos] using hm _ (P.vertex_mem_body (next i))
    refine ⟨-inner ℝ w (ahead P i) / det (back P i) (ahead P i),
      -inner ℝ w (back P i) / det (back P i) (ahead P i),
      div_nonneg (neg_nonneg.mpr hb) hD.le,
      div_nonneg (neg_nonneg.mpr ha) hD.le, ?_⟩
    rw [hnleft, hnright]
    exact normal_reconstruct _ _ _ hD.ne'
  · rintro ⟨lam, μ, hlam, hμ, rfl⟩ x hx
    have hleft := P.body_edge_nonpos (prev i) hx
    have hright := P.body_edge_nonpos i hx
    have hbase : P.edgeRow (prev i) (P.vertex i) = 0 :=
      (P.vertex_edge_eq_iff (prev i) i).mpr (Or.inr (next_prev i).symm)
    rw [P.edgeRow_apply] at hleft hright hbase
    have hleft' : inner ℝ (outwardNormal P.vertex (prev i)) (x-P.vertex i) ≤ 0 := by
      simp only [inner_sub_right] at hleft hbase ⊢
      linarith
    have hsum : inner ℝ
        (lam • outwardNormal P.vertex (prev i)+μ • outwardNormal P.vertex i)
        (x-P.vertex i) ≤ 0 := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hlam hleft')
        (mul_nonpos_of_nonneg_of_nonpos hμ hright)
    rw [inner_sub_right] at hsum
    linarith

/-- Global coverage of all directions by DERIVED adjacent normal cones. -/
theorem normalCones_cover (w : Plane) :
    ∃ i : Fin n, ∃ lam μ : ℝ, 0 ≤ lam ∧ 0 ≤ μ ∧
      w = lam • outwardNormal P.vertex (prev i) + μ • outwardNormal P.vertex i := by
  obtain ⟨i, hi⟩ := Finite.exists_max (fun j => inner ℝ w (P.vertex j))
  apply Exists.intro i
  apply (normalCone_iff P w i).mp
  exact P.body_le_of_vertices (innerSL ℝ w).toLinearMap _ hi

/-- Interior combinations of the two incident normals expose exactly the
vertex itself, on the full convex hull and not only its raw vertex list. -/
theorem positive_normal_exposes_singleton (i : Fin n) {lam μ : ℝ}
    (hlam : 0 < lam) (hμ : 0 < μ) :
    let w := lam • outwardNormal P.vertex (prev i)+μ • outwardNormal P.vertex i
    {x ∈ P.body | inner ℝ w x = inner ℝ w (P.vertex i)} = {P.vertex i} := by
  dsimp only
  ext x
  constructor
  · rintro ⟨hx, heq⟩
    have hl : P.edgeRow (prev i) x ≤ 0 := P.body_edge_nonpos _ hx
    have hr : P.edgeRow i x ≤ 0 := P.body_edge_nonpos _ hx
    have hb : P.edgeRow (prev i) (P.vertex i) = 0 :=
      (P.vertex_edge_eq_iff (prev i) i).mpr (Or.inr (next_prev i).symm)
    have hleft_at_i : P.edgeRow (prev i) x =
        inner ℝ (outwardNormal P.vertex (prev i)) x -
          inner ℝ (outwardNormal P.vertex (prev i)) (P.vertex i) := by
      rw [P.edgeRow_apply]
      rw [P.edgeRow_apply] at hb
      simp only [inner_sub_right] at hb ⊢
      linarith
    have hsum : lam*P.edgeRow (prev i) x+μ*P.edgeRow i x = 0 := by
      rw [hleft_at_i, P.edgeRow_apply, inner_sub_right]
      simp only [inner_add_left, real_inner_smul_left] at heq
      nlinarith
    have hl0 : P.edgeRow (prev i) x = 0 := by
      by_contra hne
      have hlt : P.edgeRow (prev i) x < 0 := by
        rcases lt_or_eq_of_le hl with h | h
        · exact h
        · exact False.elim (hne h)
      have hp := mul_neg_of_pos_of_neg hlam hlt
      have hm := mul_nonpos_of_nonneg_of_nonpos hμ.le hr
      linarith
    have hr0 : P.edgeRow i x = 0 := by
      rw [hl0, mul_zero, zero_add] at hsum
      exact (mul_eq_zero.mp hsum).resolve_left hμ.ne'
    rw [left_row] at hl0
    rw [right_row] at hr0
    have hdet1 : det (x-P.vertex i) (ahead P i) = 0 := by linarith
    have hdet2 : det (back P i) (x-P.vertex i) = 0 := by linarith
    have hre := det_reconstruct (back P i) (ahead P i) (x-P.vertex i)
      (corner_det_pos P i).ne'
    rw [hdet1, hdet2] at hre
    simp only [zero_div, zero_smul, zero_add] at hre
    exact Set.mem_singleton_iff.mpr (sub_eq_zero.mp hre)
  · rintro rfl
    exact ⟨P.vertex_mem_body i, rfl⟩

/-- Actual maximizer set, independent of any precomputed fan or support value. -/
def supportFace (w : Plane) : Set Plane :=
  {x ∈ P.body | ∀ y ∈ P.body, inner ℝ w y ≤ inner ℝ w x}

lemma supportFace_at_max (w : Plane) (i : Fin n) (hm : Maximizes P w i) :
    supportFace P w = {x ∈ P.body | inner ℝ w x = inner ℝ w (P.vertex i)} := by
  ext x
  constructor
  · rintro ⟨hx, hxmax⟩
    exact ⟨hx, le_antisymm (hm x hx) (hxmax _ (P.vertex_mem_body i))⟩
  · rintro ⟨hx, heq⟩
    refine ⟨hx, ?_⟩
    intro y hy
    rw [heq]
    exact hm y hy

/-- A positive multiple of a computed edge normal exposes the entire actual
edge, with no accidental vertex-only or extended-line interpretation. -/
theorem supportFace_positive_edge_normal (i : Fin n) {c : ℝ} (hc : 0 < c) :
    supportFace P (c • outwardNormal P.vertex i) =
      AffineMap.lineMap (P.vertex i) (P.vertex (next i)) '' Icc (0 : ℝ) 1 := by
  have hm : Maximizes P (c • outwardNormal P.vertex i) i := by
    intro x hx
    have hr := P.body_edge_nonpos i hx
    rw [P.edgeRow_apply, inner_sub_right] at hr
    simp only [real_inner_smul_left]
    exact mul_le_mul_of_nonneg_left (by linarith) hc.le
  rw [supportFace_at_max P _ i hm, ← edge_tight_eq_segment P i]
  ext x
  constructor
  · rintro ⟨hx, he⟩
    refine ⟨hx, ?_⟩
    rw [P.edgeRow_apply, inner_sub_right]
    simp only [real_inner_smul_left] at he
    have he' : c*(inner ℝ (outwardNormal P.vertex i) x -
        inner ℝ (outwardNormal P.vertex i) (P.vertex i)) = 0 := by nlinarith
    exact (mul_eq_zero.mp he').resolve_left hc.ne'
  · rintro ⟨hx, he⟩
    refine ⟨hx, ?_⟩
    rw [P.edgeRow_apply, inner_sub_right] at he
    simp only [real_inner_smul_left]
    rw [sub_eq_zero.mp he]

/-- COMPLETE PLANAR SUPPORT-FACE CLASSIFICATION. Every nonzero direction
exposes either one raw vertex or one full computed edge. Circular sorting
is not a prerequisite and no exposed-face classification is a premise. -/
theorem supportFace_classification (w : Plane) (hw : w ≠ 0) :
    (∃ i : Fin n, supportFace P w = {P.vertex i}) ∨
    (∃ i : Fin n, supportFace P w =
      AffineMap.lineMap (P.vertex i) (P.vertex (next i)) '' Icc (0 : ℝ) 1) := by
  obtain ⟨i, lam, μ, hlam, hμ, heq⟩ := normalCones_cover P w
  by_cases hl : lam = 0
  · have hm : 0 < μ := by
      by_contra hnot
      have hz : μ = 0 := le_antisymm (by linarith) hμ
      rw [hl, hz, zero_smul, zero_smul, zero_add] at heq
      exact hw heq
    right
    refine ⟨i, ?_⟩
    rw [heq, hl, zero_smul, zero_add]
    exact supportFace_positive_edge_normal P i hm
  · have hlampos : 0 < lam := by
      rcases lt_or_eq_of_le hlam with h | h
      · exact h
      · exact False.elim (hl h.symm)
    by_cases hr : μ = 0
    · right
      refine ⟨prev i, ?_⟩
      rw [heq, hr, zero_smul, add_zero]
      exact supportFace_positive_edge_normal P (prev i) hlampos
    · left
      refine ⟨i, ?_⟩
      have hm : Maximizes P w i := (normalCone_iff P w i).mpr ⟨lam, μ, hlam, hμ, heq⟩
      rw [supportFace_at_max P w i hm, heq]
      have hμpos : 0 < μ := by
        rcases lt_or_eq_of_le hμ with h | h
        · exact h
        · exact False.elim (hr h.symm)
      exact positive_normal_exposes_singleton P i hlampos hμpos

end ReducedConvexPolygon
end
end PolygonSupportCompleteness

#print axioms PolygonSupportCompleteness.ReducedConvexPolygon.local_tangent_coordinates
#print axioms PolygonSupportCompleteness.ReducedConvexPolygon.feasible_le_vertex_max
#print axioms PolygonSupportCompleteness.ReducedConvexPolygon.body_eq_edgeHalfspaces
#print axioms PolygonSupportCompleteness.ReducedConvexPolygon.edge_tight_eq_segment
#print axioms PolygonSupportCompleteness.ReducedConvexPolygon.normalCone_iff
#print axioms PolygonSupportCompleteness.ReducedConvexPolygon.normalCones_cover
#print axioms PolygonSupportCompleteness.ReducedConvexPolygon.positive_normal_exposes_singleton
#check @PolygonSupportCompleteness.ReducedConvexPolygon.body_eq_edgeHalfspaces
#check @PolygonSupportCompleteness.ReducedConvexPolygon.supportFace_classification

#print axioms PolygonSupportCompleteness.ReducedConvexPolygon.supportFace_positive_edge_normal
#print axioms PolygonSupportCompleteness.ReducedConvexPolygon.supportFace_classification
