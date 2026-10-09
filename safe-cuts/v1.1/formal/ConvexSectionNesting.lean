import Mathlib

/-!
# Strict nesting of convex Minkowski sections

This file formalizes the narrow Lemma B requested in `LEAN HANDOFF.md`.
-/

open Set
open scoped Pointwise

namespace ConvexSectionNesting

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Minkowski section `(1 - u) B + u A`. -/
def minkowskiSection (A B : Set E) (u : ℝ) : Set E :=
  (1 - u) • B + u • A

/--
Later Minkowski sections lie in the interior of earlier sections when the top set lies in the
interior of the convex base set. This is the exact paper statement; compactness, finite
dimensionality, polygonality, and nonemptiness are not required.
-/
theorem section_strict_nesting
    {A B : Set E} (hB : Convex ℝ B) (hAB : A ⊆ interior B)
    {s t : ℝ} (_hs0 : 0 ≤ s) (hst : s < t) (ht1 : t < 1) :
    minkowskiSection A B t ⊆ interior (minkowskiSection A B s) := by
  rintro x ⟨xb, ⟨b, hb, rfl⟩, xa, ⟨a, ha, rfl⟩, rfl⟩
  let lam : ℝ := (1 - t) / (1 - s)
  let mu : ℝ := (t - s) / (1 - s)
  have hden : 0 < 1 - s := by linarith
  have hlam : 0 ≤ lam := by
    dsimp [lam]
    exact div_nonneg (by linarith) hden.le
  have hmu : 0 < mu := by
    dsimp [mu]
    exact div_pos (sub_pos.mpr hst) hden
  have hlammu : lam + mu = 1 := by
    dsimp [lam, mu]
    field_simp [ne_of_gt hden]
    ring
  let b' : E := lam • b + mu • a
  have hb' : b' ∈ interior B := by
    dsimp [b']
    exact hB.combo_self_interior_mem_interior hb (hAB ha) hlam hmu hlammu
  have hscaled : (1 - s) • b' ∈ interior ((1 - s) • B) := by
    rw [interior_smul₀ (ne_of_gt hden)]
    exact smul_mem_smul_set hb'
  have hsum : (1 - s) • b' + s • a ∈ interior ((1 - s) • B) + s • A :=
    add_mem_add hscaled (smul_mem_smul_set ha)
  have hinterior : (1 - s) • b' + s • a ∈ interior (minkowskiSection A B s) := by
    exact subset_interior_add_left hsum
  have hlamScale : (1 - s) * lam = 1 - t := by
    dsimp [lam]
    field_simp [ne_of_gt hden]
  have hmuScale : (1 - s) * mu + s = t := by
    dsimp [mu]
    field_simp [ne_of_gt hden]
    ring
  have hx : (1 - t) • b + t • a = (1 - s) • b' + s • a := by
    calc
      (1 - t) • b + t • a = ((1 - s) * lam) • b + (((1 - s) * mu) + s) • a := by
        rw [hlamScale, hmuScale]
      _ = (1 - s) • b' + s • a := by
        dsimp [b']
        module
  change (1 - t) • b + t • a ∈ interior (minkowskiSection A B s)
  rw [hx]
  exact hinterior

/-- The prismatoid truncation used in the paper is an immediate specialization. -/
theorem truncated_section_strict_nesting
    {A B : Set E} (hB : Convex ℝ B) (hAB : A ⊆ interior B)
    {δ : ℝ} (hδ0 : 0 < δ) (hδhalf : δ < 1 / 2) :
    minkowskiSection A B (1 - δ) ⊆ interior (minkowskiSection A B δ) := by
  apply section_strict_nesting hB hAB hδ0.le
  · linarith
  · linarith

/--
Mutation witness: weakening `A ⊆ interior B` to `A ⊆ B` is false, even for the convex
singleton `A = B = {0}` in `ℝ`. Every section is `{0}`, whose ambient interior is empty.
-/
theorem subset_base_not_enough :
    ¬minkowskiSection ({0} : Set ℝ) {0} (1 / 2) ⊆
      interior (minkowskiSection ({0} : Set ℝ) {0} 0) := by
  simp [minkowskiSection]

#print axioms section_strict_nesting
#print axioms truncated_section_strict_nesting
#print axioms subset_base_not_enough

end ConvexSectionNesting
