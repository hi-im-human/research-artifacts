import HingeExtensionUniqueness

/-!
# Uniqueness along an opened face chain

System draft, 2026-09-19. NOT compiled in this runtime.
Target: Lean 4.34.0 / Mathlib v4.34.0, without changing pins.

The two developments below are independently supplied. Their equality is a
conclusion, not a field of the admissibility data. Each face keeps its own
source plane. Only the target Euclidean plane is shared.

This proves a conditional uniqueness statement. It does not construct a
polyhedron, prove existence of developments, or certify that actual trimmed
facets instantiate the endpoint and side conditions. See checkpoint 19.
-/

open Set
open scoped Affine

namespace FaceChainRestriction

/-- Copies of two common material hinge points and a side witness in each face.
The right points must be distinct and the right witness off their line;
those hypotheses are supplied explicitly to the theorems below. -/
structure HingeData (L R : Type*) where
  leftA : L
  leftB : L
  leftRef : L
  rightA : R
  rightB : R
  rightRef : R

section OneStep

variable {W Q : Type*}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [MetricSpace Q] [NormedAddTorsor W Q]

/-- Endpoint gluing and an actual opposite-side condition within one development.
This definition says nothing about equality with a second development. -/
def Compatible {L R : Type*} (h : HingeData L R) (u : L → Q) (v : R → Q) : Prop :=
  v h.rightA = u h.leftA ∧
  v h.rightB = u h.leftB ∧
  (line[ℝ, v h.rightA, v h.rightB]).SOppSide (u h.leftRef) (v h.rightRef)

/-- Two independently admissible placements agree on the next entire face plane
when they agree on the previous one. The next maps' same-side condition is
DERIVED by composing their opposite-side conditions through the common witness. -/
theorem next_eq_of_previous_eq
    {L V R : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace R] [NormedAddTorsor V R]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (hdV : Module.finrank ℝ V = 2) (hdW : Module.finrank ℝ W = 2)
    (h : HingeData L R) (u u' : L → Q) (v v' : R →ᵃⁱ[ℝ] Q)
    (hab : h.rightA ≠ h.rightB)
    (hr : h.rightRef ∉ line[ℝ, h.rightA, h.rightB])
    (hprev : ∀ p, u p = u' p)
    (hc : Compatible h u v) (hc' : Compatible h u' v') : v = v' := by
  rcases hc with ⟨ha, hb, hop⟩
  rcases hc' with ⟨ha', hb', hop'⟩
  have hA : v h.rightA = v' h.rightA := by
    calc
      v h.rightA = u h.leftA := ha
      _ = u' h.leftA := hprev h.leftA
      _ = v' h.rightA := ha'.symm
  have hB : v h.rightB = v' h.rightB := by
    calc
      v h.rightB = u h.leftB := hb
      _ = u' h.leftB := hprev h.leftB
      _ = v' h.rightB := hb'.symm
  have hopCommon :
      (line[ℝ, v h.rightA, v h.rightB]).SOppSide
        (u h.leftRef) (v' h.rightRef) := by
    rw [hA, hB, hprev h.leftRef]
    exact hop'
  have hs :
      (line[ℝ, v h.rightA, v h.rightB]).SSameSide
        (v h.rightRef) (v' h.rightRef) :=
    hop.symm.trans hopCommon
  exact HingeExtensionUniqueness.affineIsometry_eq_of_hinge_sameSide
    hdV hdW v v' hab hr hA hB hs

end OneStep

section Chain

variable {n : ℕ} {V P : Fin (n + 1) → Type*}
  [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℝ (V i)]
  [∀ i, MetricSpace (P i)] [∀ i, NormedAddTorsor (V i) (P i)]
  [∀ i, FiniteDimensional ℝ (V i)]
  {W Q : Type*}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [MetricSpace Q] [NormedAddTorsor W Q] [FiniteDimensional ℝ W]

/-- A nonempty finite chain has at most one normalized admissible development.
There are `n + 1` face planes and `n` hinges. No cycle-closing condition, cap,
nonoverlap assumption, or face-placement existence theorem is imported. -/
theorem faceChain_unique
    (hdP : ∀ i, Module.finrank ℝ (V i) = 2)
    (hdQ : Module.finrank ℝ W = 2)
    (H : (j : Fin n) → HingeData (P j.castSucc) (P j.succ))
    (U T : (i : Fin (n + 1)) → P i →ᵃⁱ[ℝ] Q)
    (hDistinct : ∀ j, (H j).rightA ≠ (H j).rightB)
    (hOff : ∀ j, (H j).rightRef ∉ line[ℝ, (H j).rightA, (H j).rightB])
    (hU : ∀ j, Compatible (H j) (U j.castSucc) (U j.succ))
    (hT : ∀ j, Compatible (H j) (T j.castSucc) (T j.succ))
    (hRoot : U 0 = T 0) : ∀ i, U i = T i := by
  intro i
  refine Fin.induction hRoot ?_ i
  intro j ih
  exact next_eq_of_previous_eq
    (hdP j.succ) hdQ (H j)
    (U j.castSucc) (T j.castSucc) (U j.succ) (T j.succ)
    (hDistinct j) (hOff j)
    (fun p => congrArg (fun f : P j.castSucc →ᵃⁱ[ℝ] Q => f p) ih)
    (hU j) (hT j)

/-- Restriction equality is a CONSEQUENCE of chain uniqueness for independently
supplied maps. Instantiating `D` with actual trimmed facets is a separate
geometric interface obligation, not a definition of `T` in terms of `U`. -/
theorem faceChain_restriction
    (hdP : ∀ i, Module.finrank ℝ (V i) = 2)
    (hdQ : Module.finrank ℝ W = 2)
    (H : (j : Fin n) → HingeData (P j.castSucc) (P j.succ))
    (U T : (i : Fin (n + 1)) → P i →ᵃⁱ[ℝ] Q)
    (hDistinct : ∀ j, (H j).rightA ≠ (H j).rightB)
    (hOff : ∀ j, (H j).rightRef ∉ line[ℝ, (H j).rightA, (H j).rightB])
    (hU : ∀ j, Compatible (H j) (U j.castSucc) (U j.succ))
    (hT : ∀ j, Compatible (H j) (T j.castSucc) (T j.succ))
    (hRoot : U 0 = T 0)
    (D : (i : Fin (n + 1)) → Set (P i)) :
    ∀ i, (fun x : D i => T i x.val) = (fun x : D i => U i x.val) := by
  have hEq := faceChain_unique hdP hdQ H U T hDistinct hOff hU hT hRoot
  intro i
  funext x
  exact congrArg (fun f : P i →ᵃⁱ[ℝ] Q => f x.val) (hEq i).symm

end Chain

end FaceChainRestriction

#print axioms FaceChainRestriction.next_eq_of_previous_eq
#print axioms FaceChainRestriction.faceChain_unique
#print axioms FaceChainRestriction.faceChain_restriction
