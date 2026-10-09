import PolyhedralInputBridge

/-!
# Recover a safe full layout and every uncut supporting-edge connection

System, 2026-09-19. UNCOMPILED DRAFT for Lean/Mathlib v4.34.0.

No family of full developments U or proofs hU is supplied to the endpoint.
A finite-label cofinality argument selects a seam that occurs at arbitrarily
small depths. One of its actual trimmed layouts supplies the plane maps.
Two-trim rigidity and fixed overlap witnesses prove the full maps are safe.
Affine extrapolation extends gluing of every other retained supporting edge
all the way to its original endpoints, including non-neighbor edge pairs.

The NEW external input explicitly carries all-uncut-edge gluing, not only
DevelopmentOn's adjacent gluing. This property belongs to a genuine single-
cut ordinary unfolding; it is NOT inferred from Safe or from face coverage.
Old theorem statements, definitions and pins are unchanged. Universal facet
certificate/order extraction and application of the external theorem remain
unproved here. No limit of maps, per-face normalization or new axiom is used.
-/

open Set
open scoped Affine
open TrimmedFacetWitnesses FaceChainRestriction BandGeometryAssembly
open FiniteWitnessClosure PolyhedralInputBridge

namespace SingleCutRecovery

section DomainRestriction
variable {E : Type*}

lemma heightTrim_antitone {F : Set E} {z : E → ℝ} {d m : ℝ} (hdm : d ≤ m) :
    heightTrim F z m ⊆ heightTrim F z d := by
  intro x hx
  exact ⟨hx.1, hdm.trans hx.2.1, by linarith [hx.2.2]⟩

end DomainRestriction

section RestrictDevelopment
variable {n : ℕ} {E : Fin (n+1) → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]
  {A Q : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [FiniteDimensional ℝ Q]

/-- Restrict one actual development to smaller material domains. -/
lemma developmentOn_mono
    (iota : (i : Fin (n+1)) → E i →ᵃ[ℝ] A)
    (D D' : (i : Fin (n+1)) → Set (E i)) (U : (i : Fin (n+1)) → E i → Q)
    (hSub : ∀ i, D' i ⊆ D i) (hU : DevelopmentOn iota D U) :
    DevelopmentOn iota D' U := by
  constructor
  · intro j x hx y hy hxy
    exact hU.1 j x (hSub j.castSucc hx) y (hSub j.succ hy) hxy
  · intro j
    apply (hU.2 j).mono
    · exact interior_mono (Set.image_mono (hSub j.castSucc))
    · exact interior_mono (Set.image_mono (hSub j.succ))

/-- Two independent trimmed layouts, possibly at DIFFERENT depths, have the
same plane maps after one global rigid alignment. Compare them on the common
retained band at max(d1,d2), not on a falsely enlarged band at min(d1,d2). -/
theorem two_trims_align
    (hdE : ∀ i, Module.finrank ℝ (E i) = 2) (hdQ : Module.finrank ℝ Q = 2)
    (F : (i : Fin (n+1)) → Set (E i))
    (z : (i : Fin (n+1)) → E i →ᵃ[ℝ] ℝ)
    (hF : ∀ i, Convex ℝ (F i)) (hz : ∀ i, Continuous (z i))
    (iota : (i : Fin (n+1)) → E i →ᵃ[ℝ] A)
    (sL : (j : Fin n) → EdgeSeed (F j.castSucc) (z j.castSucc))
    (sR : (j : Fin n) → EdgeSeed (F j.succ) (z j.succ))
    (hmA : ∀ j, iota j.castSucc (sL j).a = iota j.succ (sR j).a)
    (hmB : ∀ j, iota j.castSucc (sL j).b = iota j.succ (sR j).b)
    {d1 d2 : ℝ} (hd10 : 0 < d1) (hd11 : d1 < (1 : ℝ)/2)
    (hd20 : 0 < d2) (hd21 : d2 < (1 : ℝ)/2)
    (U T : (i : Fin (n+1)) → E i →ᵃⁱ[ℝ] Q)
    (hU : DevelopmentOn iota (fun i => heightTrim (F i) (z i) d1) (fun i => U i))
    (hT : DevelopmentOn iota (fun i => heightTrim (F i) (z i) d2) (fun i => T i)) :
    ∃ C : Q ≃ᵃⁱ[ℝ] Q, ∀ i, ∀ x : E i, C (T i x) = U i x := by
  let m : ℝ := max d1 d2
  have hm0 : 0 < m := hd10.trans_le (le_max_left _ _)
  have hm1 : m < (1 : ℝ)/2 := max_lt hd11 hd21
  let D : (i : Fin (n+1)) → Set (E i) := fun i => heightTrim (F i) (z i) m
  have hUM : DevelopmentOn iota D (fun i => U i) :=
    developmentOn_mono iota _ D _
      (fun i => heightTrim_antitone (le_max_left d1 d2)) hU
  have hTM : DevelopmentOn iota D (fun i => T i) :=
    developmentOn_mono iota _ D _
      (fun i => heightTrim_antitone (le_max_right d1 d2)) hT
  let UE : (i : Fin (n+1)) → E i ≃ᵃⁱ[ℝ] Q :=
    fun i => planeEquiv ((hdE i).trans hdQ.symm) (U i)
  let TE : (i : Fin (n+1)) → E i ≃ᵃⁱ[ℝ] Q :=
    fun i => planeEquiv ((hdE i).trans hdQ.symm) (T i)
  let H : (j : Fin n) → HingeData (E j.castSucc) (E j.succ) := fun j =>
    { leftA := retainedLow (sL j).a (sL j).b m
      leftB := retainedHigh (sL j).a (sL j).b m
      leftRef := inwardWitness (sL j).a (sL j).b (sL j).c m
      rightA := retainedLow (sR j).a (sR j).b m
      rightB := retainedHigh (sR j).a (sR j).b m
      rightRef := inwardWitness (sR j).a (sR j).b (sR j).c m }
  have hL j := (sL j).valid (hF j.castSucc) (hz j.castSucc) hm0 hm1
  have hR j := (sR j).valid (hF j.succ) (hz j.succ) hm0 hm1
  have hm j := retained_material_correspondence (iota j.castSucc) (iota j.succ)
    (hmA j) (hmB j) m
  have hDistinct : ∀ j, (H j).rightA ≠ (H j).rightB := fun j => (hR j).2.2.1
  have hOff : ∀ j, (H j).rightRef ∉ line[ℝ, (H j).rightA, (H j).rightB] :=
    fun j => (hR j).2.2.2.2.2
  have hUC : ∀ j, Compatible (H j) (UE j.castSucc) (UE j.succ) := by
    intro j
    exact compatible_from_material hdQ (H j) (iota j.castSucc) (iota j.succ)
      (UE j.castSucc) (UE j.succ)
      (heightTrim_convex (hF j.castSucc) (z j.castSucc) m)
      (heightTrim_convex (hF j.succ) (z j.succ) m)
      (hL j).1 (hL j).2.1 (hR j).1 (hR j).2.1
      (hL j).2.2.2.2.1 (hR j).2.2.2.2.1
      (hDistinct j) (hm j).1 (hm j).2 (hUM.1 j) (hUM.2 j)
  have hTC : ∀ j, Compatible (H j) (TE j.castSucc) (TE j.succ) := by
    intro j
    exact compatible_from_material hdQ (H j) (iota j.castSucc) (iota j.succ)
      (TE j.castSucc) (TE j.succ)
      (heightTrim_convex (hF j.castSucc) (z j.castSucc) m)
      (heightTrim_convex (hF j.succ) (z j.succ) m)
      (hL j).1 (hL j).2.1 (hR j).1 (hR j).2.1
      (hL j).2.2.2.2.1 (hR j).2.2.2.2.1
      (hDistinct j) (hm j).1 (hm j).2 (hTM.1 j) (hTM.2 j)
  let C : Q ≃ᵃⁱ[ℝ] Q := (TE 0).symm.trans (UE 0)
  let N : (i : Fin (n+1)) → E i →ᵃⁱ[ℝ] Q :=
    fun i => ((TE i).trans C).toAffineIsometry
  have hNC : ∀ j, Compatible (H j) (N j.castSucc) (N j.succ) := by
    intro j
    exact compatible_postcompose (H j) (TE j.castSucc) (TE j.succ) C (hTC j)
  have hRoot : (UE 0).toAffineIsometry = N 0 := by
    apply AffineIsometry.ext
    intro x
    change UE 0 x = UE 0 ((TE 0).symm (TE 0 x))
    rw [(TE 0).symm_apply_apply]
  have hEq := FaceChainRestriction.faceChain_unique hdE hdQ H
    (fun i => (UE i).toAffineIsometry) N hDistinct hOff hUC hNC hRoot
  refine ⟨C, ?_⟩
  intro i x
  exact congrArg (fun f : E i →ᵃⁱ[ℝ] Q => f x) (hEq i).symm

end RestrictDevelopment

/-- Occurs at arbitrarily small POSITIVE depths, not at every depth. -/
def CofinalSmall {S : Type*} (G : S → ℝ → Prop) (e : S) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ d : ℝ,
    0 < d ∧ d < eps ∧ d < (1 : ℝ)/2 ∧ G e d

/-- A finite label family with an available label at every small depth has
at least one label occurring arbitrarily close to zero. This does not choose
the same safe label at every depth. Reuse the checked finite-threshold lemma. -/
theorem finite_some_label_cofinal {S : Type*} [Finite S] (G : S → ℝ → Prop)
    (hG : ∀ d : ℝ, 0 < d → d < (1 : ℝ)/2 → ∃ e, G e d) :
    ∃ e, CofinalSmall G e := by
  classical
  apply finite_persistence_forces_good (CofinalSmall G) G hG
  intro e hbad
  simp only [CofinalSmall, not_forall, not_exists, not_and, not_imp] at hbad
  obtain ⟨eps, heps, hNo⟩ := hbad
  refine ⟨min eps ((1 : ℝ)/2), lt_min heps (by norm_num), min_le_right _ _, ?_⟩
  intro d hd0 hd
  exact hNo d hd0 (hd.trans_le (min_le_left _ _))
    (hd.trans_le (min_le_right _ _))

section Recover
variable {S : Type*} [Finite S] {n : ℕ} {E : S → Fin (n+1) → Type*}
  [∀ e i, NormedAddCommGroup (E e i)] [∀ e i, InnerProductSpace ℝ (E e i)]
  [∀ e i, FiniteDimensional ℝ (E e i)]
  {A Q : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [FiniteDimensional ℝ Q]

/-- Full plane maps are RECOVERED from one selected trimmed development.
Extra records an additional property of that reference layout; this theorem
does not assume an extension law for Extra. The geometric application below
proves the edge-gluing extension separately by affine extrapolation. -/
theorem safe_full_extension_from_cofinal_trims
    (hdE : ∀ e i, Module.finrank ℝ (E e i) = 2) (hdQ : Module.finrank ℝ Q = 2)
    (F : (e : S) → (i : Fin (n+1)) → Set (E e i))
    (z : (e : S) → (i : Fin (n+1)) → E e i →ᵃ[ℝ] ℝ)
    (hF : ∀ e i, Convex ℝ (F e i)) (hz : ∀ e i, Continuous (z e i))
    (hBounds : ∀ e i, ∀ x ∈ F e i, z e i x ∈ Icc (0 : ℝ) 1)
    (hLevels : ∀ e i, ∃ a b : E e i, z e i a = 0 ∧ z e i b = 1)
    (iota : (e : S) → (i : Fin (n+1)) → E e i →ᵃ[ℝ] A)
    (sL : (e : S) → (j : Fin n) → EdgeSeed (F e j.castSucc) (z e j.castSucc))
    (sR : (e : S) → (j : Fin n) → EdgeSeed (F e j.succ) (z e j.succ))
    (hmA : ∀ e j, iota e j.castSucc (sL e j).a = iota e j.succ (sR e j).a)
    (hmB : ∀ e j, iota e j.castSucc (sL e j).b = iota e j.succ (sR e j).b)
    (Extra : (e : S) → ℝ → ((i : Fin (n+1)) → E e i →ᵃⁱ[ℝ] Q) → Prop)
    (hTrim : ∀ d : ℝ, 0 < d → d < (1 : ℝ)/2 →
      ∃ e : S, ∃ T : (i : Fin (n+1)) → E e i →ᵃⁱ[ℝ] Q,
        DevelopmentOn (iota e) (fun i => heightTrim (F e i) (z e i) d) (fun i => T i) ∧
        Safe (fun i => heightTrim (F e i) (z e i) d) (fun i => T i) ∧ Extra e d T) :
    ∃ e : S, ∃ d0 : ℝ, 0 < d0 ∧ d0 < (1 : ℝ)/2 ∧
      ∃ U : (i : Fin (n+1)) → E e i →ᵃⁱ[ℝ] Q,
        DevelopmentOn (iota e) (fun i => heightTrim (F e i) (z e i) d0) (fun i => U i) ∧
        Extra e d0 U ∧ Safe (F e) (fun i => U i) := by
  classical
  let G : S → ℝ → Prop := fun e d =>
    ∃ T : (i : Fin (n+1)) → E e i →ᵃⁱ[ℝ] Q,
      DevelopmentOn (iota e) (fun i => heightTrim (F e i) (z e i) d) (fun i => T i) ∧
      Safe (fun i => heightTrim (F e i) (z e i) d) (fun i => T i) ∧ Extra e d T
  obtain ⟨e, hCof⟩ := finite_some_label_cofinal G hTrim
  obtain ⟨d0, hd00, _, hd01, U, hU, _, hExtra⟩ := hCof ((1 : ℝ)/2) (by norm_num)
  refine ⟨e, d0, hd00, hd01, U, hU, hExtra, ?_⟩
  by_contra hBad
  have hd : ∀ i, Module.finrank ℝ (E e i) = Module.finrank ℝ Q :=
    fun i => (hdE e i).trans hdQ.symm
  have hw := overlap_of_not_safe hd U hBad
  obtain ⟨eps, heps, _, hSurvive⟩ := fixed_overlap_survives
    (F e) (z e) (hz e) (hBounds e) (hLevels e) (fun i => U i) hw
  obtain ⟨d, hd0, hdlt, hd1, T, hT, hSafe, _⟩ := hCof eps heps
  obtain ⟨C, hAlign⟩ := two_trims_align (hdE e) hdQ (F e) (z e) (hF e) (hz e)
    (iota e) (sL e) (sR e) (hmA e) (hmB e) hd00 hd01 hd0 hd1 U T hU hT
  exact not_safe_of_overlap hd T
    (overlap_under_common_alignment C hAlign (hSurvive d hd0 hdlt)) hSafe

end Recover

section Extrapolation
variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- Agreement at two parameters determines affine maps on the entire real
line. Extrapolation outside the sampled interval is explicitly justified. -/
theorem affine_eq_of_two_parameters (f g : ℝ →ᵃ[ℝ] Q) {l u : ℝ}
    (hne : l ≠ u) (hl : f l = g l) (hu : f u = g u) : f = g := by
  apply AffineMap.ext
  intro t
  let s : ℝ := (t-l)/(u-l)
  have hp : AffineMap.lineMap l u s = t := by
    rw [AffineMap.lineMap_apply_ring']
    dsimp [s]
    field_simp [sub_ne_zero.mpr hne.symm] <;> ring
  calc
    f t = f (AffineMap.lineMap l u s) := congrArg f hp.symm
    _ = AffineMap.lineMap (f l) (f u) s := f.apply_lineMap _ _ _
    _ = AffineMap.lineMap (g l) (g u) s := by rw [hl, hu]
    _ = g (AffineMap.lineMap l u s) := (g.apply_lineMap _ _ _).symm
    _ = g t := congrArg g hp

end Extrapolation

section AllEdges
variable {K A : Type*} [Fintype K] [DecidableEq K]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  {H : HalfspaceData (K := K) (A := A)}
  {L R Q : Type*}
  [NormedAddCommGroup L] [NormedSpace ℝ L]
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- Gluing a nondegenerate retained interval forces gluing of the whole
ORIGINAL supporting edge, including its removed rim endpoints. -/
theorem edge_gluing_extends
    {CL : FacetCertificate H L} {CR : FacetCertificate H R}
    (ed : OriginalEdge CL CR) (u : L →ᵃ[ℝ] Q) (v : R →ᵃ[ℝ] Q)
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2)
    (hGlue : ∀ t ∈ Icc d (1-d),
      u (AffineMap.lineMap ed.aL ed.bL t) = v (AffineMap.lineMap ed.aR ed.bR t)) :
    ∀ t : ℝ, u (AffineMap.lineMap ed.aL ed.bL t) =
      v (AffineMap.lineMap ed.aR ed.bR t) := by
  let l : ℝ := (1 : ℝ)/4 + d/2
  let r : ℝ := (3 : ℝ)/4 - d/2
  have hl : l ∈ Icc d (1-d) := ⟨by dsimp [l]; linarith, by dsimp [l]; linarith⟩
  have hr : r ∈ Icc d (1-d) := ⟨by dsimp [r]; linarith, by dsimp [r]; linarith⟩
  have hne : l ≠ r := by dsimp [l, r]; linarith
  have he := affine_eq_of_two_parameters
    (u.comp (AffineMap.lineMap ed.aL ed.bL))
    (v.comp (AffineMap.lineMap ed.aR ed.bR)) hne (hGlue l hl) (hGlue r hr)
  intro t
  exact congrArg (fun f : ℝ →ᵃ[ℝ] Q => f t) he

/-- Parametric gluing implies equality at ALL shared material points, not
only at the two tested samples. OriginalEdge's checked intersection identity
and faithful charts supply the common parameter. -/
theorem edge_material_gluing [FiniteDimensional ℝ L]
    {CL : FacetCertificate H L} {CR : FacetCertificate H R}
    (hdL : Module.finrank ℝ L = 2) (ed : OriginalEdge CL CR)
    (u : L → Q) (v : R → Q)
    (hGlue : ∀ t ∈ Icc (0 : ℝ) 1,
      u (AffineMap.lineMap ed.aL ed.bL t) = v (AffineMap.lineMap ed.aR ed.bR t)) :
    ∀ x ∈ CL.domain, ∀ y ∈ CR.domain, CL.chart x = CR.chart y → u x = v y := by
  intro x hx y hy hxy
  have hp : CL.chart x ∈ (CL.chart '' CL.domain) ∩ (CR.chart '' CR.domain) :=
    ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy.symm⟩⟩
  rw [ed.common_material_edge hdL] at hp
  obtain ⟨t, ht, htp⟩ := hp
  have hxline : AffineMap.lineMap ed.aL ed.bL t = x := by
    apply CL.chart.injective
    exact (CL.chart.toAffineMap.apply_lineMap _ _ _).trans htp
  have hyline : AffineMap.lineMap ed.aR ed.bR t = y := by
    apply CR.chart.injective
    calc
      CR.chart (AffineMap.lineMap ed.aR ed.bR t) =
          AffineMap.lineMap (CR.chart ed.aR) (CR.chart ed.bR) t :=
        CR.chart.toAffineMap.apply_lineMap _ _ _
      _ = AffineMap.lineMap (CL.chart ed.aL) (CL.chart ed.bL) t := by
        rw [← ed.match_a, ← ed.match_b]
      _ = CL.chart x := htp
      _ = CR.chart y := hxy
  simpa only [hxline, hyline] using hGlue t ht

end AllEdges

/-- The exception is one unordered pair of original supporting faces. Their
intersection is already proved to be the one designated original edge. -/
def CutPair {n : ℕ} (i j : Fin (n+1)) : Prop :=
  (i = Fin.last n ∧ j = 0) ∨ (i = 0 ∧ j = Fin.last n)

section GluingFamily
variable {K A Q : Type*} [Fintype K] [DecidableEq K]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  {n : ℕ} {E : Fin (n+1) → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  {H : HalfspaceData (K := K) (A := A)}

/-- EVERY other supporting edge is glued at depth d, regardless of whether
its two faces are consecutive in the selected chain. This is stronger than
adjacent gluing, and is explicit in the new ordinary-unfolding input. -/
def AllUncutGlued (C : (i : Fin (n+1)) → FacetCertificate H (E i))
    (d : ℝ) (U : (i : Fin (n+1)) → E i → Q) : Prop :=
  ∀ i j, ¬ CutPair i j → ∀ ed : OriginalEdge (C i) (C j),
    ∀ t ∈ Icc d (1-d), U i (AffineMap.lineMap ed.aL ed.bL t) =
      U j (AffineMap.lineMap ed.aR ed.bR t)

theorem all_uncut_gluing_extends (C : (i : Fin (n+1)) → FacetCertificate H (E i))
    (U : (i : Fin (n+1)) → E i →ᵃ[ℝ] Q)
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2)
    (hGlue : AllUncutGlued C d (fun i => U i)) :
    AllUncutGlued C 0 (fun i => U i) := by
  intro i j hNot ed t _
  exact edge_gluing_extends ed (U i) (U j) hd0 hd1 (hGlue i j hNot ed) t

theorem all_uncut_material_gluing [∀ i, FiniteDimensional ℝ (E i)]
    (C : (i : Fin (n+1)) → FacetCertificate H (E i))
    (hdE : ∀ i, Module.finrank ℝ (E i) = 2)
    (U : (i : Fin (n+1)) → E i → Q) (hGlue : AllUncutGlued C 0 U) :
    ∀ i j, ¬ CutPair i j → ∀ ed : OriginalEdge (C i) (C j),
      ∀ x ∈ (C i).domain, ∀ y ∈ (C j).domain,
        (C i).chart x = (C j).chart y → U i x = U j y := by
  intro i j hNot ed
  apply edge_material_gluing (hdE i) ed (U i) (U j)
  intro t ht
  exact hGlue i j hNot ed t (by simpa only [sub_zero] using ht)

/-- The edge test can be supplied by RAW ambient endpoint membership rather
than assuming somebody already enumerated all OriginalEdge certificates. -/
theorem gluing_of_ambient_endpoints [∀ i, FiniteDimensional ℝ (E i)]
    (C : (i : Fin (n+1)) → FacetCertificate H (E i))
    (hdE : ∀ i, Module.finrank ℝ (E i) = 2)
    (U : (i : Fin (n+1)) → E i → Q) (hGlue : AllUncutGlued C 0 U)
    {i j : Fin (n+1)} (hNot : ¬ CutPair i j) (hRows : (C i).row ≠ (C j).row)
    {a b : A}
    (ha : a ∈ ((C i).chart '' (C i).domain) ∩ ((C j).chart '' (C j).domain))
    (hb : b ∈ ((C i).chart '' (C i).domain) ∩ ((C j).chart '' (C j).domain))
    (hza : H.height a = 0) (hzb : H.height b = 1) :
    ∀ x ∈ (C i).domain, ∀ y ∈ (C j).domain,
      (C i).chart x = (C j).chart y → U i x = U j y := by
  rcases ha with ⟨⟨aL, haL, haLp⟩, ⟨aR, haR, haRp⟩⟩
  rcases hb with ⟨⟨bL, hbL, hbLp⟩, ⟨bR, hbR, hbRp⟩⟩
  let ed : OriginalEdge (C i) (C j) :=
    { aL := aL, bL := bL, aR := aR, bR := bR
      aL_mem := haL, bL_mem := hbL, aR_mem := haR, bR_mem := hbR
      a_height := by change H.height ((C i).chart aL) = 0; rw [haLp]; exact hza
      b_height := by change H.height ((C i).chart bL) = 1; rw [hbLp]; exact hzb
      match_a := haLp.trans haRp.symm
      match_b := hbLp.trans hbRp.symm
      distinct_rows := hRows }
  exact all_uncut_material_gluing C hdE U hGlue i j hNot ed

end GluingFamily

lemma adjacent_not_cutPair {n : ℕ} (hn : 2 ≤ n) (j : Fin n) :
    ¬ CutPair j.castSucc j.succ := by
  rintro (⟨_, hz⟩ | ⟨hz, hl⟩)
  · have hv := congrArg Fin.val hz
    change j.val + 1 = 0 at hv
    omega
  · have h0 := congrArg Fin.val hz
    have h1 := congrArg Fin.val hl
    change j.val = 0 at h0
    change j.val + 1 = n at h1
    omega

section Endpoint
variable {K J S A Q : Type*} [Fintype K] [DecidableEq K] [Finite S]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [FiniteDimensional ℝ Q]
  {n : ℕ} {E : J → Type*}
  [∀ j, NormedAddCommGroup (E j)] [∀ j, InnerProductSpace ℝ (E j)]
  [∀ j, FiniteDimensional ℝ (E j)]

/-- ENDPOINT: recover U and its full-domain development, Safe and ALL uncut
supporting-edge gluing from genuine all-uncut-glued trimmed inputs. No U/hU
premise remains. Original geometric certificates, finite candidate orders,
and the explicitly stronger ordinary-unfolding input are still required.

hn rules out one/two-face bookkeeping where the omitted last/first pair
would also be an uncut chain pair. Intended 3D bands have at least 3 faces.
-/
theorem exists_safe_glued_table_from_trimmed_unfoldings
    (H : HalfspaceData (K := K) (A := A))
    (C : (j : J) → FacetCertificate H (E j))
    (rows : J ≃ {k : K // k ≠ H.lower ∧ k ≠ H.upper})
    (hRows : ∀ j, (C j).row = (rows j).val)
    (hn : 2 ≤ n)
    (hdE : ∀ j, Module.finrank ℝ (E j) = 2) (hdQ : Module.finrank ℝ Q = 2)
    (order : S → (Fin (n+1) ≃ J))
    (hinge : (e : S) → (j : Fin n) →
      OriginalEdge (C (order e j.castSucc)) (C (order e j.succ)))
    (cut : (e : S) → OriginalEdge (C (order e (Fin.last n))) (C (order e 0)))
    (hTrimmedUnfolding : ∀ d : ℝ, 0 < d → d < (1 : ℝ)/2 →
      ∃ e : S, ∃ T : (i : Fin (n+1)) → E (order e i) →ᵃⁱ[ℝ] Q,
        DevelopmentOn (fun i => (C (order e i)).chart.toAffineMap)
          (fun i => heightTrim (C (order e i)).domain (C (order e i)).height d)
          (fun i => T i) ∧
        Safe (fun i => heightTrim (C (order e i)).domain (C (order e i)).height d)
          (fun i => T i) ∧
        AllUncutGlued (fun i => C (order e i)) d (fun i => T i)) :
    ∃ e : S, ∃ U : (i : Fin (n+1)) → E (order e i) →ᵃⁱ[ℝ] Q,
      DevelopmentOn (fun i => (C (order e i)).chart.toAffineMap)
        (fun i => (C (order e i)).domain) (fun i => U i) ∧
      Safe (fun i => (C (order e i)).domain) (fun i => U i) ∧
      AllUncutGlued (fun i => C (order e i)) 0 (fun i => U i) ∧
      (∀ i j, ¬ CutPair i j →
        ∀ ed : OriginalEdge (C (order e i)) (C (order e j)),
        ∀ x ∈ (C (order e i)).domain, ∀ y ∈ (C (order e j)).domain,
          (C (order e i)).chart x = (C (order e j)).chart y → U i x = U j y) ∧
      (((C (order e (Fin.last n))).chart '' (C (order e (Fin.last n))).domain) ∩
        ((C (order e 0)).chart '' (C (order e 0)).domain) =
          AffineMap.lineMap ((C (order e (Fin.last n))).chart (cut e).aL)
            ((C (order e (Fin.last n))).chart (cut e).bL) '' Icc (0 : ℝ) 1) ∧
      (⋃ i, (C (order e i)).chart '' (C (order e i)).domain) = lateralBoundary H := by
  have hLevels : ∀ e i, ∃ a b : E (order e i),
      (C (order e i)).height a = 0 ∧ (C (order e i)).height b = 1 := by
    intro e i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact ⟨(cut e).aL, (cut e).bL, (cut e).a_height, (cut e).b_height⟩
    · exact ⟨(hinge e j).aL, (hinge e j).bL,
        (hinge e j).a_height, (hinge e j).b_height⟩
  obtain ⟨e, d0, hd0, hd1, U, _, hExtra, hSafe⟩ :=
    safe_full_extension_from_cofinal_trims
      (fun e i => hdE (order e i)) hdQ
      (fun e i => (C (order e i)).domain)
      (fun e i => (C (order e i)).height)
      (fun e i => (C (order e i)).domain_convex)
      (fun e i => (C (order e i)).height_continuous)
      (fun e i _ hx => (C (order e i)).height_bounds hx) hLevels
      (fun e i => (C (order e i)).chart.toAffineMap)
      (fun e j => (hinge e j).leftSeed) (fun e j => (hinge e j).rightSeed)
      (fun e j => (hinge e j).match_a) (fun e j => (hinge e j).match_b)
      (fun e d T => AllUncutGlued (fun i => C (order e i)) d (fun i => T i))
      hTrimmedUnfolding
  have hFullGlue : AllUncutGlued (fun i => C (order e i)) 0 (fun i => U i) :=
    all_uncut_gluing_extends (fun i => C (order e i))
      (fun i => (U i).toAffineMap) hd0 hd1 hExtra
  have hMaterial := all_uncut_material_gluing (fun i => C (order e i))
    (fun i => hdE (order e i)) (fun i => U i) hFullGlue
  have hDev : DevelopmentOn (fun i => (C (order e i)).chart.toAffineMap)
      (fun i => (C (order e i)).domain) (fun i => U i) := by
    constructor
    · intro j
      exact hMaterial j.castSucc j.succ (adjacent_not_cutPair hn j) (hinge e j)
    · intro j
      have hne : j.castSucc ≠ j.succ := by
        intro h
        have hv := congrArg Fin.val h
        change j.val = j.val + 1 at hv
        omega
      exact hSafe j.castSucc j.succ hne
  refine ⟨e, U, hDev, hSafe, hFullGlue, hMaterial,
    (cut e).common_material_edge (hdE _), ?_⟩
  rw [material_union_reindex (fun j => (C j).chart '' (C j).domain) (order e)]
  exact material_band_eq H C rows hRows

end Endpoint
end SingleCutRecovery

#print axioms SingleCutRecovery.two_trims_align
#print axioms SingleCutRecovery.finite_some_label_cofinal
#print axioms SingleCutRecovery.safe_full_extension_from_cofinal_trims
#print axioms SingleCutRecovery.edge_gluing_extends
#print axioms SingleCutRecovery.all_uncut_material_gluing
#print axioms SingleCutRecovery.gluing_of_ambient_endpoints
#print axioms SingleCutRecovery.exists_safe_glued_table_from_trimmed_unfoldings
#check @SingleCutRecovery.exists_safe_glued_table_from_trimmed_unfoldings
