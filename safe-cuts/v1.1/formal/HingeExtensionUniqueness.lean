import Mathlib

/-!
# Hinge-side uniqueness for exact restriction

Status: local point lemmas and whole one-hinge affine-isometry uniqueness
kernel-checked by Forge against Lean/Mathlib v4.34.0; see return 17.

This file attacks the local geometric obligation identified in
`12 SYSTEM REVIEW RETURN.md`: once a hinge is fixed, the same-side branch of a
planar affine-isometric extension should be unique.

The key Mathlib ingredients already exist:
* `AffineSubspace.SSameSide` / `SOppSide` in `Mathlib.Analysis.Convex.Side`;
* `EuclideanGeometry.reflection` and `dist_reflection_eq_of_mem`;
* `EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two`.

The intended proof is deliberately local. It does not formalize Aloupis et al.
Theorem 10 or the finite-seam contradiction.
-/

open Set
open EuclideanGeometry
open scoped Affine

namespace HingeExtensionUniqueness

variable {V P : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/--
Reflection of a point not on an affine subspace lies strictly on the opposite
side of that subspace.

This should be a small wrapper around `reflection_apply'` and
`AffineSubspace.sOppSide_pointReflection`.
-/
theorem sOppSide_reflection
    (s : AffineSubspace ℝ P) [Nonempty s]
    [s.direction.HasOrthogonalProjection]
    {p : P} (hp : p ∉ s) :
    s.SOppSide p (reflection s p) := by
  rw [reflection_apply']
  exact AffineSubspace.sOppSide_pointReflection
    (orthogonalProjection_mem (s := s) p) hp

/--
In a two-dimensional Euclidean affine space, distances to two distinct hinge
points plus a strict same-side condition determine a point uniquely.

Geometric proof:
* reflect `p` across the hinge line;
* the reflected point has the same distances to both hinge endpoints;
* the two-circle theorem says any point with those two distances is either
  `p` or its reflection;
* strict same-side excludes the reflected branch.
-/
theorem eq_of_two_distances_of_sSameSide
    [FiniteDimensional ℝ V] (hd : Module.finrank ℝ V = 2)
    {c₁ c₂ p q : P}
    (hc : c₁ ≠ c₂)
    (hp : p ∉ line[ℝ, c₁, c₂])
    (hs : line[ℝ, c₁, c₂].SSameSide p q)
    (h₁ : dist p c₁ = dist q c₁)
    (h₂ : dist p c₂ = dist q c₂) :
    p = q := by
  let s : AffineSubspace ℝ P := line[ℝ, c₁, c₂]
  have hs_nonempty : (s : Set P).Nonempty := by
    exact ⟨c₁, left_mem_affineSpan_pair ℝ c₁ c₂⟩
  letI : Nonempty s := hs_nonempty.to_subtype
  letI : s.direction.HasOrthogonalProjection := by infer_instance

  have hc₁s : c₁ ∈ s := left_mem_affineSpan_pair ℝ c₁ c₂
  have hc₂s : c₂ ∈ s := right_mem_affineSpan_pair ℝ c₁ c₂

  have href_ne : reflection s p ≠ p := by
    intro h
    exact hp ((reflection_eq_self_iff p).1 h)

  have href_c₁ : dist (reflection s p) c₁ = dist p c₁ := by
    rw [dist_comm, dist_reflection_eq_of_mem s hc₁s p, dist_comm]
  have href_c₂ : dist (reflection s p) c₂ = dist p c₂ := by
    rw [dist_comm, dist_reflection_eq_of_mem s hc₂s p, dist_comm]

  have hcases :
      q = p ∨ q = reflection s p := by
    apply eq_of_dist_eq_of_dist_eq_of_finrank_eq_two hd
      (c₁ := c₁) (c₂ := c₂) (p₁ := p) (p₂ := reflection s p) (p := q)
      (r₁ := dist p c₁) (r₂ := dist p c₂)
    · exact hc
    · exact href_ne.symm
    · rfl
    · exact href_c₁
    · exact h₁.symm
    · rfl
    · exact href_c₂
    · exact h₂.symm

  rcases hcases with hqp | hqref
  · exact hqp.symm
  · exfalso
    have hopp : s.SOppSide p (reflection s p) :=
      sOppSide_reflection s hp
    exact hopp.not_sSameSide (by simpa [s, hqref] using hs)

/-!
## Whole one-hinge theorem

The theorem below uses the point theorem above to prove equality of two
planar affine isometries, following System's route 18.

Suppose:
* source and target affine spaces are both two-dimensional;
* `a ≠ b` are hinge points;
* `r` is off the source hinge line;
* affine isometries `f` and `g` agree at `a` and `b`;
* `f r` and `g r` lie strictly on the same side of the common target hinge.

Then `f r = g r` follows immediately from
`eq_of_two_distances_of_sSameSide`, because affine isometries preserve the two
distances to the hinge endpoints.

To conclude `f = g`, the two source vsubs form a basis, and `Module.Basis.ext`
identifies the linear parts. Agreement at `a` then identifies the affine maps.

Face-chain induction is outside this file's completed scope.
-/

variable {W Q : Type*}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [MetricSpace Q] [NormedAddTorsor W Q]

/-- Two planar affine isometries agreeing along a nondegenerate hinge and
choosing the same strict side at an off-hinge point are equal everywhere. -/
theorem affineIsometry_eq_of_hinge_sameSide
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (hdV : Module.finrank ℝ V = 2) (hdW : Module.finrank ℝ W = 2)
    (f g : P →ᵃⁱ[ℝ] Q) {a b r : P}
    (hab : a ≠ b) (hr : r ∉ line[ℝ, a, b])
    (ha : f a = g a) (hb : f b = g b)
    (hs : line[ℝ, f a, f b].SSameSide (f r) (g r)) : f = g := by
  have hfr : f r = g r := by
    apply eq_of_two_distances_of_sSameSide hdW
      (f.isometry.injective.ne hab) hs.left_notMem hs
    · calc
        dist (f r) (f a) = dist r a := f.isometry.dist_eq r a
        _ = dist (g r) (f a) := by rw [ha, g.isometry.dist_eq]
    · calc
        dist (f r) (f b) = dist r b := f.isometry.dist_eq r b
        _ = dist (g r) (f b) := by rw [hb, g.isometry.dist_eq]
  have hnotcol : ¬ Collinear ℝ ({a, b, r} : Set P) := by
    intro hcol
    exact hr (hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hab)
  have haff : AffineIndependent ℝ ![a, b, r] :=
    affineIndependent_iff_not_collinear_set.mpr hnotcol
  have hvsub :=
    (affineIndependent_iff_linearIndependent_vsub ℝ ![a, b, r] (0 : Fin 3)).mp haff
  rw [← linearIndependent_equiv (finSuccAboveEquiv (0 : Fin 3))] at hvsub
  have hli : LinearIndependent ℝ ![b -ᵥ a, r -ᵥ a] := by
    convert hvsub using 1
    ext i
    fin_cases i <;> rfl
  let vb : Module.Basis (Fin 2) ℝ V :=
    basisOfLinearIndependentOfCardEqFinrank'
      ![b -ᵥ a, r -ᵥ a] hli (by simpa using hdV.symm)
  have hlin : f.linearIsometry.toLinearMap = g.linearIsometry.toLinearMap := by
    apply vb.ext
    intro i
    fin_cases i
    · simp [vb, AffineIsometry.map_vsub, ha, hb]
    · simp [vb, AffineIsometry.map_vsub, ha, hfr]
  apply AffineIsometry.ext
  intro x
  have hx := LinearMap.congr_fun hlin (x -ᵥ a)
  have hv : f x -ᵥ f a = g x -ᵥ f a := by
    simpa only [LinearIsometry.coe_toLinearMap, AffineIsometry.map_vsub, ← ha] using hx
  have hx' := congrArg (fun v : W => v +ᵥ f a) hv
  simpa only [vsub_vadd] using hx'

end HingeExtensionUniqueness

#print axioms HingeExtensionUniqueness.sOppSide_reflection
#print axioms HingeExtensionUniqueness.eq_of_two_distances_of_sSameSide
#print axioms HingeExtensionUniqueness.affineIsometry_eq_of_hinge_sameSide
