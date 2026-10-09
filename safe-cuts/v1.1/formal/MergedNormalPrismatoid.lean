import PolyhedralInputBridge
import Mathlib.Analysis.Convex.Hull

/-!
# Raw cyclic polygon foundation for the merged-normal prismatoid constructor

This checkpoint deliberately starts at the permitted raw representation.  An
edge normal is computed from consecutive vertices; the structure stores only
the local facts that the chosen cyclic orientation makes every vertex lie in
that edge halfspace and that equality occurs only at its two endpoints.  It
does not contain a merged fan, a halfspace-completeness equality, a facet or
edge table, or any three-dimensional incidence assertion.

The checked part below proves that every edge row supports the independently
defined convex hull, identifies equality on the raw vertices, and establishes
the physical (unscaled) two-rim convex-hull body and its normalized height.
The circular merge/completeness and certificate constructor remain after this
foundation; see return 44. No external unfolding theorem is imported.
-/

open Set
open scoped BigOperators

namespace MergedNormalPrismatoid

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Ambient := Plane × ℝ

def next {n : ℕ} [NeZero n] (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩

def rotateCW (v : Plane) : Plane :=
  WithLp.toLp 2 ![-v 1, v 0]

def edgeVector {n : ℕ} [NeZero n] (v : Fin n → Plane) (i : Fin n) : Plane :=
  v (next i) - v i

def outwardNormal {n : ℕ} [NeZero n] (v : Fin n → Plane) (i : Fin n) : Plane :=
  rotateCW (edgeVector v i)

/-- A raw reduced counterclockwise cyclic polygon.  `supports` is ordinary
local convexity of the oriented edge list; `support_eq_vertices` is reducedness
(no third listed vertex lies on an edge).  Neither field states that the edge
halfspaces are complete for the convex hull. -/
structure ReducedConvexPolygon (n : ℕ) [NeZero n] where
  vertex : Fin n → Plane
  three_le : 3 ≤ n
  edge_ne : ∀ i, vertex (next i) ≠ vertex i
  supports : ∀ i j,
    inner ℝ (outwardNormal vertex i) (vertex j - vertex i) ≤ 0
  support_eq_vertices : ∀ i j,
    inner ℝ (outwardNormal vertex i) (vertex j - vertex i) = 0 →
      j = i ∨ j = next i

namespace ReducedConvexPolygon

variable {n : ℕ} [NeZero n] (P : ReducedConvexPolygon n)

def body : Set Plane := convexHull ℝ (range P.vertex)

noncomputable def edgeLinear (i : Fin n) : Plane →L[ℝ] ℝ :=
  innerSL ℝ (outwardNormal P.vertex i)

noncomputable def edgeRow (i : Fin n) (x : Plane) : ℝ :=
  P.edgeLinear i x - P.edgeLinear i (P.vertex i)

@[simp] lemma edgeRow_apply (i : Fin n) (x : Plane) :
    P.edgeRow i x = inner ℝ (outwardNormal P.vertex i) (x - P.vertex i) := by
  simp [edgeRow, edgeLinear, inner_sub_right]

lemma vertex_mem_body (i : Fin n) : P.vertex i ∈ P.body :=
  subset_convexHull ℝ (range P.vertex) (mem_range_self i)

lemma body_nonempty : P.body.Nonempty :=
  ⟨P.vertex 0, P.vertex_mem_body 0⟩

lemma body_convex : Convex ℝ P.body := convex_convexHull ℝ _

/-- Every linear support bound on the raw vertices extends to the polygon body.
This is the finite support-max reduction used before any fan is constructed. -/
theorem body_le_of_vertices (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (hv : ∀ j, f (P.vertex j) ≤ c) : ∀ x ∈ P.body, f x ≤ c := by
  intro x hx
  have hsub : range P.vertex ⊆ {y | f y ≤ c} := by
    rintro _ ⟨j, rfl⟩
    exact hv j
  exact (convexHull_min hsub (convex_halfSpace_le f.isLinear c)) hx

/-- Every raw oriented edge row supports the entire independently defined
convex hull. This is one direction of polygon halfspace completeness and does
not define the body by the rows. -/
theorem body_edge_nonpos (i : Fin n) {x : Plane} (hx : x ∈ P.body) :
    P.edgeRow i x ≤ 0 := by
  have hsub : range P.vertex ⊆
      {y | P.edgeLinear i y ≤ P.edgeLinear i (P.vertex i)} := by
    rintro _ ⟨j, rfl⟩
    simpa [edgeLinear, inner_sub_right] using P.supports i j
  have hconv : Convex ℝ
      {y | P.edgeLinear i y ≤ P.edgeLinear i (P.vertex i)} :=
    convex_halfSpace_le (P.edgeLinear i).toLinearMap.isLinear _
  have hx' := (convexHull_min hsub hconv) hx
  change P.edgeLinear i x ≤ P.edgeLinear i (P.vertex i) at hx'
  simpa [edgeRow] using sub_nonpos.mpr hx'

theorem body_edge_halfspace (i : Fin n) :
    P.body ⊆ {x | P.edgeRow i x ≤ 0} :=
  fun _ hx => P.body_edge_nonpos i hx

/-- On the raw vertex list, the supporting line contains exactly the two edge
endpoints. This is a derived theorem exposing the representation contract. -/
theorem vertex_edge_eq_iff (i j : Fin n) :
    P.edgeRow i (P.vertex j) = 0 ↔ j = i ∨ j = next i := by
  constructor
  · simpa [edgeRow_apply] using P.support_eq_vertices i j
  · rintro (rfl | rfl)
    · simp [edgeRow_apply]
    · simp [edgeRow_apply, outwardNormal, edgeVector, rotateCW, inner,
        Fin.sum_univ_two]
      ring

theorem outwardNormal_ne_zero (i : Fin n) : outwardNormal P.vertex i ≠ 0 := by
  intro h
  have hrot0 : rotateCW (edgeVector P.vertex i) = 0 := h
  have h0 := congrArg (fun x : Plane => x.ofLp (0 : Fin 2)) hrot0
  have h1 := congrArg (fun x : Plane => x.ofLp (1 : Fin 2)) hrot0
  have hv : edgeVector P.vertex i = 0 := by
    ext k
    fin_cases k
    · simpa [rotateCW] using h1
    · simpa [rotateCW] using neg_eq_zero.mp h0
  apply P.edge_ne i
  simpa [edgeVector, sub_eq_zero] using hv

end ReducedConvexPolygon

def lowerLift (x : Plane) : Ambient := (x, 0)
def upperLift (h : ℝ) (x : Plane) : Ambient := (x, h)

/-- The physical body is defined independently as the convex hull of the two
embedded polygon bodies. No halfspace representation occurs in this definition. -/
def prismatoid {nA nB : ℕ} [NeZero nA] [NeZero nB]
    (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB) (h : ℝ) :
    Set Ambient :=
  convexHull ℝ (lowerLift '' B.body ∪ upperLift h '' A.body)

lemma prismatoid_convex {nA nB : ℕ} [NeZero nA] [NeZero nB]
    (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB) (h : ℝ) :
    Convex ℝ (prismatoid A B h) := convex_convexHull ℝ _

lemma lower_mem_prismatoid {nA nB : ℕ} [NeZero nA] [NeZero nB]
    (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB) (h : ℝ)
    {b : Plane} (hb : b ∈ B.body) : lowerLift b ∈ prismatoid A B h :=
  subset_convexHull ℝ (lowerLift '' B.body ∪ upperLift h '' A.body)
    (Or.inl ⟨b, hb, rfl⟩)

lemma upper_mem_prismatoid {nA nB : ℕ} [NeZero nA] [NeZero nB]
    (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB) (h : ℝ)
    {a : Plane} (ha : a ∈ A.body) : upperLift h a ∈ prismatoid A B h :=
  subset_convexHull ℝ (lowerLift '' B.body ∪ upperLift h '' A.body)
    (Or.inr ⟨a, ha, rfl⟩)

lemma prismatoid_nonempty {nA nB : ℕ} [NeZero nA] [NeZero nB]
    (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB) (h : ℝ) :
    (prismatoid A B h).Nonempty :=
  ⟨lowerLift (B.vertex 0), lower_mem_prismatoid A B h (B.vertex_mem_body 0)⟩

def physicalHeight : Ambient →L[ℝ] ℝ :=
  ContinuousLinearMap.snd ℝ Plane ℝ

noncomputable def normalizedHeight (h : ℝ) : Ambient →L[ℝ] ℝ :=
  h⁻¹ • physicalHeight

@[simp] lemma physicalHeight_lower (x : Plane) : physicalHeight (lowerLift x) = 0 := rfl
@[simp] lemma physicalHeight_upper (h : ℝ) (x : Plane) :
    physicalHeight (upperLift h x) = h := rfl

@[simp] lemma normalizedHeight_lower (h : ℝ) (x : Plane) :
    normalizedHeight h (lowerLift x) = 0 := by simp [normalizedHeight]

@[simp] lemma normalizedHeight_upper {h : ℝ} (hh : h ≠ 0) (x : Plane) :
    normalizedHeight h (upperLift h x) = 1 := by
  simp [normalizedHeight, hh]

/-- A point explicitly interpolated between physical rim points has the
expected physical height. This keeps `h` in the ambient metric and normalizes
only the scalar height observable. -/
lemma physicalHeight_interpolate (b a : Plane) (h t : ℝ) :
    physicalHeight ((1 - t) • lowerLift b + t • upperLift h a) = t * h := by
  simp [lowerLift, upperLift, physicalHeight]

lemma normalizedHeight_interpolate {h : ℝ} (hh : h ≠ 0)
    (b a : Plane) (t : ℝ) :
    normalizedHeight h ((1 - t) • lowerLift b + t • upperLift h a) = t := by
  rw [map_add, map_smul, map_smul]
  simp [normalizedHeight, hh]

end MergedNormalPrismatoid

#print axioms MergedNormalPrismatoid.ReducedConvexPolygon.body_edge_nonpos
#print axioms MergedNormalPrismatoid.ReducedConvexPolygon.body_le_of_vertices
#print axioms MergedNormalPrismatoid.ReducedConvexPolygon.vertex_edge_eq_iff
#print axioms MergedNormalPrismatoid.ReducedConvexPolygon.outwardNormal_ne_zero
#print axioms MergedNormalPrismatoid.normalizedHeight_interpolate
#check @MergedNormalPrismatoid.ReducedConvexPolygon
#check @MergedNormalPrismatoid.prismatoid
