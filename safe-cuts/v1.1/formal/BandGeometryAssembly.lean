import FaceChainRestriction
import TrimmedFacetWitnesses

/-!
# Assembling original face data and independent developments

System, 2026-09-19. UNCOMPILED DRAFT against Lean/Mathlib v4.34.0.

This is one integrated interface, not a new sequence of isolated requests.
The target `normalized_exactRestriction` constructs retained material,
obtains local side compatibility from convex separation, normalizes by ONE
common planar isometry, and applies the checked finite-chain theorem.

The original convex face/chart/edge inputs and the existence of the two
independent developments remain inputs. No polytope incidence extraction,
Aloupis theorem, or universal safe-cut theorem is claimed in this file.
No same-side agreement between developments, propagation axiom, or retained
witness is assumed in the final statement.
-/

open Set
open scoped Affine
open TrimmedFacetWitnesses FaceChainRestriction

namespace BandGeometryAssembly

section AffineMaterial
variable {E A : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]

lemma map_retainedLow (f : E →ᵃ[ℝ] A) (a b : E) (d : ℝ) :
    f (retainedLow a b d) = retainedLow (f a) (f b) d := by
  unfold retainedLow
  exact f.apply_lineMap a b _

lemma map_retainedHigh (f : E →ᵃ[ℝ] A) (a b : E) (d : ℝ) :
    f (retainedHigh a b d) = retainedHigh (f a) (f b) d := by
  unfold retainedHigh
  exact f.apply_lineMap a b _

/-- The deterministic pair, not arbitrary existential choices, is natural
under two possibly different affine charts with matching original endpoints. -/
theorem retained_material_correspondence
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (f : E →ᵃ[ℝ] A) (g : E' →ᵃ[ℝ] A) {a b : E} {a' b' : E'}
    (ha : f a = g a') (hb : f b = g b') (d : ℝ) :
    f (retainedLow a b d) = g (retainedLow a' b' d) ∧
    f (retainedHigh a b d) = g (retainedHigh a' b' d) := by
  constructor
  · rw [map_retainedLow, map_retainedLow, ha, hb]
  · rw [map_retainedHigh, map_retainedHigh, ha, hb]

/-- Distinct retained points lie on, and span, the original hinge line. -/
theorem retained_line_eq {a b : E} {d : ℝ}
    (hne : retainedLow a b d ≠ retainedHigh a b d) :
    line[ℝ, retainedLow a b d, retainedHigh a b d] = line[ℝ, a, b] := by
  apply affineSpan_pair_eq_of_mem_of_mem_of_ne _ _ hne
  · exact mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨_, rfl⟩
  · exact mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨_, rfl⟩

lemma heightTrim_convex {F : Set E} (hF : Convex ℝ F)
    (z : E →ᵃ[ℝ] ℝ) (d : ℝ) : Convex ℝ (heightTrim F z d) := by
  change Convex ℝ (F ∩ z ⁻¹' Icc d (1 - d))
  exact hF.inter ((convex_Icc d (1 - d)).affine_preimage z)

end AffineMaterial

section Separation
variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [FiniteDimensional ℝ Q]

/-- An affine scalar functional constant at the two endpoints is constant
on their entire affine line. -/
lemma value_on_line (f : Q →ᵃ[ℝ] ℝ) {a b : Q} {k : ℝ}
    (ha : f a = k) (hb : f b = k) {p : Q}
    (hp : p ∈ line[ℝ, a, b]) : f p = k := by
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hp
  rw [← ht, f.apply_lineMap, ha, hb, AffineMap.lineMap_same_apply]

/-- In dimension two, a nonconstant affine level containing two distinct
points is exactly their line. The off-level point constructs a basis; no
unproved hyperplane-dimension assertion is used. -/
lemma mem_line_of_level_eq (hd : Module.finrank ℝ Q = 2)
    (f : Q →ᵃ[ℝ] ℝ) {a b c p : Q} {k : ℝ}
    (hab : a ≠ b) (ha : f a = k) (hb : f b = k)
    (hc : f c ≠ k) (hp : f p = k) : p ∈ line[ℝ, a, b] := by
  have hcOff : c ∉ line[ℝ, a, b] := fun hm => hc (value_on_line f ha hb hm)
  have hncol : ¬ Collinear ℝ ({a, b, c} : Set Q) := by
    intro h
    exact hcOff (h.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hab)
  have haff : AffineIndependent ℝ ![a, b, c] :=
    affineIndependent_iff_not_collinear_set.mpr hncol
  have hli :=
    (affineIndependent_iff_linearIndependent_vsub ℝ ![a, b, c] (0 : Fin 3)).mp haff
  rw [← linearIndependent_equiv (finSuccAboveEquiv (0 : Fin 3))] at hli
  have hpair : LinearIndependent ℝ ![b - a, c - a] := by
    convert hli using 1
    ext i
    fin_cases i <;> rfl
  let B : Module.Basis (Fin 2) ℝ Q :=
    basisOfLinearIndependentOfCardEqFinrank' ![b - a, c - a] hpair
      (by simpa using hd.symm)
  have expand (v : Q) : v = B.repr v 0 • (b - a) + B.repr v 1 • (c - a) := by
    simpa [B, Fin.sum_univ_two] using (B.sum_repr v).symm
  have hba : f.linear (b - a) = 0 := by
    simpa [ha, hb] using f.linearMap_vsub b a
  have hca : f.linear (c - a) = f c - k := by
    simpa [ha] using f.linearMap_vsub c a
  have hpa : f.linear (p - a) = 0 := by
    simpa [ha, hp] using f.linearMap_vsub p a
  have hprod : B.repr (p - a) 1 * (f c - k) = 0 := by
    have h := congrArg f.linear (expand (p - a))
    simpa [map_add, map_smul, hba, hca, hpa] using h.symm
  have hcoeff : B.repr (p - a) 1 = 0 :=
    (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hc)
  have hvec : p - a = B.repr (p - a) 0 • (b - a) := by
    simpa only [hcoeff, zero_smul, add_zero] using expand (p - a)
  apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
  refine ⟨B.repr (p - a) 0, ?_⟩
  rw [AffineMap.lineMap_apply_module', ← hvec]
  exact sub_add_cancel p a

/-- Local correspondence to an independently obtained flat placement.
Disjoint convex interiors and a shared nondegenerate segment force the
interior witnesses onto opposite sides of its line. No polygon coordinates,
side-selection premise, or global nonoverlap hypothesis is required. -/
theorem convex_sharedEdge_opposite (hd : Module.finrank ℝ Q = 2)
    {S T : Set Q} (hS : Convex ℝ S) (hT : Convex ℝ T)
    {a b x y : Q} (hab : a ≠ b)
    (haS : a ∈ S) (haT : a ∈ T) (hbS : b ∈ S) (hbT : b ∈ T)
    (hx : x ∈ interior S) (hy : y ∈ interior T)
    (hdisj : Disjoint (interior S) (interior T)) :
    (line[ℝ, a, b]).SOppSide x y := by
  obtain ⟨l, k, hlt, hgt⟩ := geometric_hahn_banach_open_open
    hS.interior isOpen_interior hT.interior isOpen_interior hdisj
  have hle : ∀ p ∈ S, l p ≤ k := by
    have hclosed : IsClosed {p : Q | l p ≤ k} :=
      isClosed_le l.continuous continuous_const
    have hsub : closure (interior S) ⊆ {p : Q | l p ≤ k} :=
      closure_minimal (fun p hp => (hlt p hp).le) hclosed
    intro p hp
    apply hsub
    rw [hS.closure_interior_eq_closure_of_nonempty_interior ⟨x, hx⟩]
    exact subset_closure hp
  have hge : ∀ p ∈ T, k ≤ l p := by
    have hclosed : IsClosed {p : Q | k ≤ l p} :=
      isClosed_le continuous_const l.continuous
    have hsub : closure (interior T) ⊆ {p : Q | k ≤ l p} :=
      closure_minimal (fun p hp => (hgt p hp).le) hclosed
    intro p hp
    apply hsub
    rw [hT.closure_interior_eq_closure_of_nonempty_interior ⟨y, hy⟩]
    exact subset_closure hp
  have hla : l a = k := le_antisymm (hle a haS) (hge a haT)
  have hlb : l b = k := le_antisymm (hle b hbS) (hge b hbT)
  have hlx : l x < k := hlt x hx
  have hly : k < l y := hgt y hy
  let f : Q →ᵃ[ℝ] ℝ := l.toLinearMap.toAffineMap
  have hxOff : x ∉ line[ℝ, a, b] := by
    intro h
    exact hlx.ne (value_on_line f hla hlb h)
  have hyOff : y ∉ line[ℝ, a, b] := by
    intro h
    exact hly.ne' (value_on_line f hla hlb h)
  let t : ℝ := (k - l x) / (l y - l x)
  have hden : 0 < l y - l x := sub_pos.mpr (hlx.trans hly)
  have ht0 : 0 < t := div_pos (sub_pos.mpr hlx) hden
  have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
  have hlevel : f (AffineMap.lineMap x y t) = k := by
    rw [f.apply_lineMap, AffineMap.lineMap_apply_ring]
    change (1 - t) * l x + t * l y = k
    dsimp [t]
    field_simp [ne_of_gt hden] <;> ring
  have hm : AffineMap.lineMap x y t ∈ line[ℝ, a, b] :=
    mem_line_of_level_eq hd f hab hla hlb hlx.ne hlevel
  have hbtw : Wbtw ℝ x (AffineMap.lineMap x y t) y :=
    ⟨t, ⟨ht0.le, ht1.le⟩, rfl⟩
  exact ⟨hbtw.wOppSide₁₃ hm, hxOff, hyOff⟩

end Separation

section LocalData
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- ORIGINAL local face/edge data only. No retained points, side agreement
of two layouts, or chain-compatibility conclusion occurs in this structure. -/
structure EdgeSeed (F : Set E) (z : E →ᵃ[ℝ] ℝ) where
  a : E
  b : E
  c : E
  sigma : E →ᵃ[ℝ] ℝ
  a_mem : a ∈ F
  b_mem : b ∈ F
  c_int : c ∈ interior F
  za : z a = 0
  zb : z b = 1
  zc : z c ∈ Icc (0 : ℝ) 1
  sa : sigma a = 0
  sb : sigma b = 0
  sc : 0 < sigma c

lemma EdgeSeed.valid {F : Set E} {z : E →ᵃ[ℝ] ℝ}
    (s : EdgeSeed F z) (hF : Convex ℝ F) (hz : Continuous z)
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2) :
    retainedLow s.a s.b d ∈ heightTrim F z d ∧
    retainedHigh s.a s.b d ∈ heightTrim F z d ∧
    retainedLow s.a s.b d ≠ retainedHigh s.a s.b d ∧
    inwardWitness s.a s.b s.c d ∈ interior F ∧
    inwardWitness s.a s.b s.c d ∈ interior (heightTrim F z d) ∧
    inwardWitness s.a s.b s.c d ∉
      line[ℝ, retainedLow s.a s.b d, retainedHigh s.a s.b d] := by
  have hp := retained_hinge_points hF z s.a_mem s.b_mem s.za s.zb hd0 hd1
  have hi := inward_witness_interior hF z hz s.a_mem s.b_mem s.c_int
    s.za s.zb s.zc hd0 hd1
  have ho := inward_witness_off_retained_hinge s.sigma s.sa s.sb s.sc hd1
  exact ⟨hp.1, hp.2.1, hp.2.2, hi.1, hi.2, ho⟩

end LocalData

section Compatibility
variable {L R Q A : Type*}
  [NormedAddCommGroup L] [InnerProductSpace ℝ L]
  [NormedAddCommGroup R] [InnerProductSpace ℝ R]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [FiniteDimensional ℝ Q]
  [NormedAddCommGroup A] [NormedSpace ℝ A]

lemma image_interior_eq (e : L ≃ᵃⁱ[ℝ] Q) (S : Set L) :
    e '' interior S = interior (e '' S) := by
  simpa only [AffineIsometryEquiv.coe_toHomeomorph] using
    e.toHomeomorph.image_interior S

/-- Derive the checked chain's local contract from each layout's OWN
material gluing and adjacent interior nonoverlap. -/
theorem compatible_from_material
    (hd : Module.finrank ℝ Q = 2)
    (H : HingeData L R) (iL : L →ᵃ[ℝ] A) (iR : R →ᵃ[ℝ] A)
    (u : L ≃ᵃⁱ[ℝ] Q) (v : R ≃ᵃⁱ[ℝ] Q)
    {DL : Set L} {DR : Set R} (hDL : Convex ℝ DL) (hDR : Convex ℝ DR)
    (haL : H.leftA ∈ DL) (hbL : H.leftB ∈ DL)
    (haR : H.rightA ∈ DR) (hbR : H.rightB ∈ DR)
    (hrL : H.leftRef ∈ interior DL) (hrR : H.rightRef ∈ interior DR)
    (hab : H.rightA ≠ H.rightB)
    (hmA : iL H.leftA = iR H.rightA) (hmB : iL H.leftB = iR H.rightB)
    (hGlue : ∀ x ∈ DL, ∀ y ∈ DR, iL x = iR y → u x = v y)
    (hDisj : Disjoint (interior (u '' DL)) (interior (v '' DR))) :
    Compatible H u v := by
  have hA : v H.rightA = u H.leftA := (hGlue _ haL _ haR hmA).symm
  have hB : v H.rightB = u H.leftB := (hGlue _ hbL _ hbR hmB).symm
  refine ⟨hA, hB, ?_⟩
  apply convex_sharedEdge_opposite hd
    (hDL.affine_image u.toAffineEquiv.toAffineMap)
    (hDR.affine_image v.toAffineEquiv.toAffineMap) (v.injective.ne hab)
  · rw [hA]; exact ⟨_, haL, rfl⟩
  · exact ⟨_, haR, rfl⟩
  · rw [hB]; exact ⟨_, hbL, rfl⟩
  · exact ⟨_, hbR, rfl⟩
  · change u H.leftRef ∈ interior (u '' DL)
    rw [← image_interior_eq u DL]; exact ⟨_, hrL, rfl⟩
  · change v H.rightRef ∈ interior (v '' DR)
    rw [← image_interior_eq v DR]; exact ⟨_, hrR, rfl⟩
  · exact hDisj

/-- One common rigid change of the target plane preserves each local contract. -/
lemma compatible_postcompose (H : HingeData L R) (u : L → Q) (v : R → Q)
    (C : Q ≃ᵃⁱ[ℝ] Q) (h : Compatible H u v) :
    Compatible H (fun p => C (u p)) (fun p => C (v p)) := by
  rcases h with ⟨hA, hB, hSide⟩
  refine ⟨congrArg C hA, congrArg C hB, ?_⟩
  let f := C.toAffineEquiv.toAffineMap
  have hi : Function.Injective f := C.injective
  have hh : ((line[ℝ, v H.rightA, v H.rightB]).map f).SOppSide
      (f (u H.leftRef)) (f (v H.rightRef)) := hi.sOppSide_map_iff.mpr hSide
  simpa [AffineSubspace.map_span, f] using hh

end Compatibility

section EmbeddingAdapter
variable {E Q : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [FiniteDimensional ℝ Q]

/-- Equal finite dimension upgrades a plane embedding to an equivalence
without changing its underlying map. Surjectivity is not an extra geometric
hypothesis of the final embedding-level theorem. -/
noncomputable def planeEquiv (hd : Module.finrank ℝ E = Module.finrank ℝ Q)
    (f : E →ᵃⁱ[ℝ] Q) : E ≃ᵃⁱ[ℝ] Q := by
  let e : E ≃ₗ[ℝ] Q := f.linearIsometry.toLinearMap.linearEquivOfInjective
    f.linearIsometry.injective hd
  let eI : E ≃ₗᵢ[ℝ] Q :=
    { e with norm_map' := fun x => f.linearIsometry.norm_map x }
  exact AffineIsometryEquiv.mk' f eI (0 : E) (by
    intro x
    change f x = f.linearIsometry (x -ᵥ (0 : E)) +ᵥ f 0
    rw [f.map_vsub, vsub_vadd])

@[simp] lemma planeEquiv_apply
    (hd : Module.finrank ℝ E = Module.finrank ℝ Q)
    (f : E →ᵃⁱ[ℝ] Q) (x : E) : planeEquiv hd f x = f x := rfl

end EmbeddingAdapter

section Assembly
variable {n : ℕ} {E : Fin (n + 1) → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]
  {Q A : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
  [FiniteDimensional ℝ Q] [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- Gluing is required only between adjacent uncut faces and only on material
that belongs to the current domains. No removed rim endpoints or closing seam
are implicitly glued. Adjacent nonoverlap permits distant face overlap. -/
def DevelopmentOn
    (iota : (i : Fin (n + 1)) → E i →ᵃ[ℝ] A)
    (D : (i : Fin (n + 1)) → Set (E i))
    (U : (i : Fin (n + 1)) → E i → Q) : Prop :=
  (∀ j : Fin n, ∀ x ∈ D j.castSucc, ∀ y ∈ D j.succ,
    iota j.castSucc x = iota j.succ y → U j.castSucc x = U j.succ y) ∧
  (∀ j : Fin n, Disjoint (interior (U j.castSucc '' D j.castSucc))
    (interior (U j.succ '' D j.succ)))

/-- End-to-end exact restriction for original local convex-facet inputs.
The two developments are independent; even their root placements need not
agree initially. ONE global planar isometry is constructed from the roots.
The affine chart, original edge/seed data and development existence are
upstream inputs, not conclusions about an arbitrary prismatoid. -/
theorem normalized_exactRestriction
    (hdE : ∀ i, Module.finrank ℝ (E i) = 2) (hdQ : Module.finrank ℝ Q = 2)
    (F : (i : Fin (n + 1)) → Set (E i))
    (z : (i : Fin (n + 1)) → E i →ᵃ[ℝ] ℝ)
    (hF : ∀ i, Convex ℝ (F i)) (hz : ∀ i, Continuous (z i))
    (iota : (i : Fin (n + 1)) → E i →ᵃ[ℝ] A)
    (sL : (j : Fin n) → EdgeSeed (F j.castSucc) (z j.castSucc))
    (sR : (j : Fin n) → EdgeSeed (F j.succ) (z j.succ))
    (hmA : ∀ j, iota j.castSucc (sL j).a = iota j.succ (sR j).a)
    (hmB : ∀ j, iota j.castSucc (sL j).b = iota j.succ (sR j).b)
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2)
    (U T : (i : Fin (n + 1)) → E i ≃ᵃⁱ[ℝ] Q)
    (hU : DevelopmentOn iota F (fun i => U i))
    (hT : DevelopmentOn iota (fun i => heightTrim (F i) (z i) d) (fun i => T i)) :
    ∃ C : Q ≃ᵃⁱ[ℝ] Q,
      (∀ i, ∀ x : E i, C (T i x) = U i x) ∧
      (∀ i, (fun x : heightTrim (F i) (z i) d => C (T i x.val)) =
        (fun x : heightTrim (F i) (z i) d => U i x.val)) := by
  let H : (j : Fin n) → HingeData (E j.castSucc) (E j.succ) := fun j =>
    { leftA := retainedLow (sL j).a (sL j).b d
      leftB := retainedHigh (sL j).a (sL j).b d
      leftRef := inwardWitness (sL j).a (sL j).b (sL j).c d
      rightA := retainedLow (sR j).a (sR j).b d
      rightB := retainedHigh (sR j).a (sR j).b d
      rightRef := inwardWitness (sR j).a (sR j).b (sR j).c d }
  have hL j := (sL j).valid (hF j.castSucc) (hz j.castSucc) hd0 hd1
  have hR j := (sR j).valid (hF j.succ) (hz j.succ) hd0 hd1
  have hm j := retained_material_correspondence
    (iota j.castSucc) (iota j.succ) (hmA j) (hmB j) d
  have hDistinct : ∀ j, (H j).rightA ≠ (H j).rightB := fun j => (hR j).2.2.1
  have hOff : ∀ j, (H j).rightRef ∉ line[ℝ, (H j).rightA, (H j).rightB] :=
    fun j => (hR j).2.2.2.2.2
  have hUC : ∀ j, Compatible (H j) (U j.castSucc) (U j.succ) := by
    intro j
    exact compatible_from_material hdQ (H j) (iota j.castSucc) (iota j.succ)
      (U j.castSucc) (U j.succ) (hF j.castSucc) (hF j.succ)
      (hL j).1.1 (hL j).2.1.1 (hR j).1.1 (hR j).2.1.1
      (hL j).2.2.2.1 (hR j).2.2.2.1
      (hDistinct j) (hm j).1 (hm j).2 (hU.1 j) (hU.2 j)
  have hTC : ∀ j, Compatible (H j) (T j.castSucc) (T j.succ) := by
    intro j
    exact compatible_from_material hdQ (H j) (iota j.castSucc) (iota j.succ)
      (T j.castSucc) (T j.succ)
      (heightTrim_convex (hF j.castSucc) (z j.castSucc) d)
      (heightTrim_convex (hF j.succ) (z j.succ) d)
      (hL j).1 (hL j).2.1 (hR j).1 (hR j).2.1
      (hL j).2.2.2.2.1 (hR j).2.2.2.2.1
      (hDistinct j) (hm j).1 (hm j).2 (hT.1 j) (hT.2 j)
  let C : Q ≃ᵃⁱ[ℝ] Q := (T 0).symm.trans (U 0)
  let N : (i : Fin (n + 1)) → E i →ᵃⁱ[ℝ] Q :=
    fun i => ((T i).trans C).toAffineIsometry
  have hNC : ∀ j, Compatible (H j) (N j.castSucc) (N j.succ) := by
    intro j
    exact compatible_postcompose (H j) (T j.castSucc) (T j.succ) C (hTC j)
  have hRoot : (U 0).toAffineIsometry = N 0 := by
    apply AffineIsometry.ext
    intro x
    change U 0 x = U 0 ((T 0).symm (T 0 x))
    rw [(T 0).symm_apply_apply]
  have hEq := FaceChainRestriction.faceChain_unique hdE hdQ H
    (fun i => (U i).toAffineIsometry) N hDistinct hOff hUC hNC hRoot
  have hAll : ∀ i, ∀ x : E i, C (T i x) = U i x := by
    intro i x
    exact congrArg (fun f : E i →ᵃⁱ[ℝ] Q => f x) (hEq i).symm
  refine ⟨C, hAll, ?_⟩
  intro i
  funext x
  exact hAll i x.val


/-- The same assembled result for the original `AffineIsometry` embedding
interface. The plane-equivalence adapter proves the normalization is available
from equal dimensions; no surjectivity premise has been added. -/
theorem exactRestriction_of_planeEmbeddings
    (hdE : ∀ i, Module.finrank ℝ (E i) = 2) (hdQ : Module.finrank ℝ Q = 2)
    (F : (i : Fin (n + 1)) → Set (E i))
    (z : (i : Fin (n + 1)) → E i →ᵃ[ℝ] ℝ)
    (hF : ∀ i, Convex ℝ (F i)) (hz : ∀ i, Continuous (z i))
    (iota : (i : Fin (n + 1)) → E i →ᵃ[ℝ] A)
    (sL : (j : Fin n) → EdgeSeed (F j.castSucc) (z j.castSucc))
    (sR : (j : Fin n) → EdgeSeed (F j.succ) (z j.succ))
    (hmA : ∀ j, iota j.castSucc (sL j).a = iota j.succ (sR j).a)
    (hmB : ∀ j, iota j.castSucc (sL j).b = iota j.succ (sR j).b)
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2)
    (U T : (i : Fin (n + 1)) → E i →ᵃⁱ[ℝ] Q)
    (hU : DevelopmentOn iota F (fun i => U i))
    (hT : DevelopmentOn iota (fun i => heightTrim (F i) (z i) d) (fun i => T i)) :
    ∃ C : Q ≃ᵃⁱ[ℝ] Q,
      (∀ i, ∀ x : E i, C (T i x) = U i x) ∧
      (∀ i, (fun x : heightTrim (F i) (z i) d => C (T i x.val)) =
        (fun x : heightTrim (F i) (z i) d => U i x.val)) := by
  let UE : (i : Fin (n + 1)) → E i ≃ᵃⁱ[ℝ] Q :=
    fun i => planeEquiv ((hdE i).trans hdQ.symm) (U i)
  let TE : (i : Fin (n + 1)) → E i ≃ᵃⁱ[ℝ] Q :=
    fun i => planeEquiv ((hdE i).trans hdQ.symm) (T i)
  have hUE : DevelopmentOn iota F (fun i => UE i) := hU
  have hTE : DevelopmentOn iota (fun i => heightTrim (F i) (z i) d)
      (fun i => TE i) := hT
  obtain ⟨C, hAll, hRes⟩ := normalized_exactRestriction hdE hdQ F z hF hz iota
    sL sR hmA hmB hd0 hd1 UE TE hUE hTE
  exact ⟨C, hAll, hRes⟩

end Assembly

end BandGeometryAssembly

#print axioms BandGeometryAssembly.retained_material_correspondence
#print axioms BandGeometryAssembly.retained_line_eq
#print axioms BandGeometryAssembly.convex_sharedEdge_opposite
#print axioms BandGeometryAssembly.compatible_from_material
#print axioms BandGeometryAssembly.normalized_exactRestriction

#print axioms BandGeometryAssembly.exactRestriction_of_planeEmbeddings
