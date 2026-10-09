import Mathlib

/-!
# Actual retained material for a height-trimmed convex face

System draft, 2026-09-19. NOT COMPILED in this runtime.
Pinned target: Lean 4.34.0 / Mathlib v4.34.0.

E is the vector space of ONE supporting face plane after choosing an origin.
It is not ambient three-space, and successive faces need not share E. No
basis, coordinate axes, metric deformation, or identification between face
planes is assumed. z is an arbitrary continuous affine normalized height.

Input c is an ORIGINAL face-interior seed, with positive original inward
support functional sigma. Retained points and a retained interior witness
are constructed, not postulated. The parent polytope must still supply the
original face data and its supporting-plane chart. This file does not prove
side compatibility of developments, root normalization, or safe-cut existence.
-/

open Set
open scoped Affine

namespace TrimmedFacetWitnesses

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def heightTrim (F : Set E) (z : E → ℝ) (d : ℝ) : Set E :=
  F ∩ {x | d ≤ z x ∧ z x ≤ 1 - d}

noncomputable def retainedLow (a b : E) (d : ℝ) : E :=
  AffineMap.lineMap a b ((1 : ℝ) / 4 + d / 2)

noncomputable def retainedHigh (a b : E) (d : ℝ) : E :=
  AffineMap.lineMap a b ((3 : ℝ) / 4 - d / 2)

noncomputable def inwardWitness (a b c : E) (d : ℝ) : E :=
  AffineMap.lineMap (AffineMap.lineMap a b ((1 : ℝ) / 2)) c ((1 : ℝ) / 2 - d)

lemma height_lineMap (z : E →ᵃ[ℝ] ℝ) {a b : E}
    (ha : z a = 0) (hb : z b = 1) (t : ℝ) :
    z (AffineMap.lineMap a b t) = t := by
  rw [z.apply_lineMap, ha, hb, AffineMap.lineMap_apply_ring]
  ring

lemma lineMap_mem_face {F : Set E} (hF : Convex ℝ F) {a b : E}
    (ha : a ∈ F) (hb : b ∈ F) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    AffineMap.lineMap a b t ∈ F := by
  rw [AffineMap.lineMap_apply_module]
  exact hF ha hb (sub_nonneg.mpr ht.2) ht.1 (by ring)

/-- A face-interior point strictly between trim levels is interior to the trim
in the SAME source plane. No ambient-three-space interior is used. -/
lemma interior_heightTrim {F : Set E} {z : E → ℝ} (hz : Continuous z)
    {x : E} {d : ℝ} (hx : x ∈ interior F)
    (hlo : d < z x) (hhi : z x < 1 - d) :
    x ∈ interior (heightTrim F z d) := by
  let O : Set E := interior F ∩ {y | d < z y ∧ z y < 1 - d}
  have hO : IsOpen O :=
    isOpen_interior.inter
      ((isOpen_lt continuous_const hz).inter (isOpen_lt hz continuous_const))
  have hsub : O ⊆ heightTrim F z d := by
    intro y hy
    exact ⟨interior_subset hy.1, hy.2.1.le, hy.2.2.le⟩
  exact (interior_maximal hsub hO) ⟨hx, hlo, hhi⟩

/-- Two distinct MATERIAL points survive strictly between the trim planes. -/
theorem retained_hinge_points {F : Set E} (hF : Convex ℝ F)
    (z : E →ᵃ[ℝ] ℝ) {a b : E} (ha : a ∈ F) (hb : b ∈ F)
    (hza : z a = 0) (hzb : z b = 1)
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ) / 2) :
    retainedLow a b d ∈ heightTrim F z d ∧
    retainedHigh a b d ∈ heightTrim F z d ∧
    retainedLow a b d ≠ retainedHigh a b d := by
  have hl : z (retainedLow a b d) = (1 : ℝ) / 4 + d / 2 :=
    height_lineMap z hza hzb _
  have hh : z (retainedHigh a b d) = (3 : ℝ) / 4 - d / 2 :=
    height_lineMap z hza hzb _
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨lineMap_mem_face hF ha hb ⟨by linarith, by linarith⟩, ?_, ?_⟩
    · rw [hl]; linarith
    · rw [hl]; linarith
  · refine ⟨lineMap_mem_face hF ha hb ⟨by linarith, by linarith⟩, ?_, ?_⟩
    · rw [hh]; linarith
    · rw [hh]; linarith
  · intro heq
    have he := congrArg z heq
    rw [hl, hh] at he
    linarith

/-- Quantitative bounds keep the constructed reference strictly in the slab. -/
lemma inward_height_bounds {d t : ℝ} (hd0 : 0 < d)
    (hd1 : d < (1 : ℝ) / 2) (ht : t ∈ Icc (0 : ℝ) 1) :
    d < (1 - ((1 : ℝ) / 2 - d)) * ((1 : ℝ) / 2) + ((1 : ℝ) / 2 - d) * t ∧
    (1 - ((1 : ℝ) / 2 - d)) * ((1 : ℝ) / 2) + ((1 : ℝ) / 2 - d) * t < 1 - d := by
  have he : 0 ≤ (1 : ℝ) / 2 - d := by linarith
  have hlo := mul_nonneg he ht.1
  have hhi := mul_nonneg he (sub_nonneg.mpr ht.2)
  constructor <;> nlinarith

/-- Move from the hinge midpoint toward an original interior seed by 1/2-d.
The result lies in both the original and retained face interiors. -/
theorem inward_witness_interior {F : Set E} (hF : Convex ℝ F)
    (z : E →ᵃ[ℝ] ℝ) (hz : Continuous z) {a b c : E}
    (ha : a ∈ F) (hb : b ∈ F) (hc : c ∈ interior F)
    (hza : z a = 0) (hzb : z b = 1) (hzc : z c ∈ Icc (0 : ℝ) 1)
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ) / 2) :
    inwardWitness a b c d ∈ interior F ∧
    inwardWitness a b c d ∈ interior (heightTrim F z d) := by
  have hm : AffineMap.lineMap a b ((1 : ℝ) / 2) ∈ F :=
    lineMap_mem_face hF ha hb ⟨by norm_num, by norm_num⟩
  have hi : inwardWitness a b c d ∈ interior F := by
    unfold inwardWitness
    rw [AffineMap.lineMap_apply_module]
    exact hF.combo_self_interior_mem_interior hm hc
      (by linarith) (by linarith) (by ring)
  have hzm := height_lineMap z hza hzb ((1 : ℝ) / 2)
  have hzr : z (inwardWitness a b c d) =
      (1 - ((1 : ℝ) / 2 - d)) * ((1 : ℝ) / 2) + ((1 : ℝ) / 2 - d) * z c := by
    unfold inwardWitness
    rw [z.apply_lineMap, hzm, AffineMap.lineMap_apply_ring]
  have hh := inward_height_bounds hd0 hd1 hzc
  refine ⟨hi, interior_heightTrim hz hi ?_ ?_⟩
  · rw [hzr]; exact hh.1
  · rw [hzr]; exact hh.2

/-- An affine scalar functional zero at both endpoints vanishes on their line. -/
lemma not_mem_line_of_positive (sigma : E →ᵃ[ℝ] ℝ) {a b r : E}
    (ha : sigma a = 0) (hb : sigma b = 0) (hr : 0 < sigma r) :
    r ∉ line[ℝ, a, b] := by
  intro hmem
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hmem
  have hzero : sigma r = 0 := by
    rw [← ht, sigma.apply_lineMap, ha, hb, AffineMap.lineMap_apply_ring]
    ring
  linarith

/-- The retained reference is off the line through the RETAINED hinge points.
Only positivity of the ORIGINAL seed under the inward functional is input. -/
theorem inward_witness_off_retained_hinge (sigma : E →ᵃ[ℝ] ℝ) {a b c : E}
    (ha : sigma a = 0) (hb : sigma b = 0) (hc : 0 < sigma c)
    {d : ℝ} (hd1 : d < (1 : ℝ) / 2) :
    inwardWitness a b c d ∉ line[ℝ, retainedLow a b d, retainedHigh a b d] := by
  have hzero (t : ℝ) : sigma (AffineMap.lineMap a b t) = 0 := by
    rw [sigma.apply_lineMap, ha, hb, AffineMap.lineMap_apply_ring]
    ring
  have hpos : 0 < sigma (inwardWitness a b c d) := by
    have he : 0 < (1 : ℝ) / 2 - d := by linarith
    have hs : sigma (inwardWitness a b c d) = ((1 : ℝ) / 2 - d) * sigma c := by
      unfold inwardWitness
      rw [sigma.apply_lineMap, hzero, AffineMap.lineMap_apply_ring]
      ring
    rw [hs]
    exact mul_pos he hc
  exact not_mem_line_of_positive sigma (hzero _) (hzero _) hpos

/-- Package concrete retained witnesses from original facet data. No retained
interior witness, retained nondegeneracy, or retained off-line premise is assumed. -/
theorem trimmed_witness_packet {F : Set E} (hF : Convex ℝ F)
    (z sigma : E →ᵃ[ℝ] ℝ) (hz : Continuous z) {a b c : E}
    (ha : a ∈ F) (hb : b ∈ F) (hc : c ∈ interior F)
    (hza : z a = 0) (hzb : z b = 1) (hzc : z c ∈ Icc (0 : ℝ) 1)
    (hsa : sigma a = 0) (hsb : sigma b = 0) (hsc : 0 < sigma c)
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ) / 2) :
    ∃ A B r : E, A ∈ heightTrim F z d ∧ B ∈ heightTrim F z d ∧ A ≠ B ∧
      r ∈ interior (heightTrim F z d) ∧ r ∉ line[ℝ, A, B] := by
  have hp := retained_hinge_points hF z ha hb hza hzb hd0 hd1
  have hi := inward_witness_interior hF z hz ha hb hc hza hzb hzc hd0 hd1
  have ho := inward_witness_off_retained_hinge sigma hsa hsb hsc hd1
  exact ⟨retainedLow a b d, retainedHigh a b d, inwardWitness a b c d,
    hp.1, hp.2.1, hp.2.2, hi.2, ho⟩

end TrimmedFacetWitnesses

#print axioms TrimmedFacetWitnesses.retained_hinge_points
#print axioms TrimmedFacetWitnesses.inward_witness_interior
#print axioms TrimmedFacetWitnesses.inward_witness_off_retained_hinge
#print axioms TrimmedFacetWitnesses.trimmed_witness_packet
