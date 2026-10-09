import BandGeometryAssembly

/-!
# Fixed overlap witnesses and the finite-seam closure

System, 2026-09-19. UNCOMPILED DRAFT for Lean/Mathlib v4.34.0.

Endpoint: `exists_safe_original_seam_of_trimmed_existence`.
This closes the downstream implication from ORIGINAL encoded face data,
independent full developments, and the explicit trimmed-existence premise.
It calls the checked assembly theorem; exact restriction is not assumed anew.

The seam type is fixed and finite before the trim depth is chosen. Each seam
may order its own dependent face-plane family. The geometric construction of
these data from ONE prismatoid, the original-edge identity across trims, and
the imported ordinary-band theorem remain upstream obligations. No axiom
representing the imported paper is declared here.

`Safe` uses actual planar IMAGE interiors. `Overlaps` uses source-plane
interior witnesses; their equivalence is proved for equal-dimensional plane
embeddings. Boundary contacts are allowed. The witness material points stay
fixed in the full development. The trimmed layout's unnormalized common
image can change with its ONE global rigid normalizer.
-/

open Set
open scoped Affine
open TrimmedFacetWitnesses BandGeometryAssembly

namespace FiniteWitnessClosure

section Height
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Original height-0/height-1 points make the affine height onto R. The
interpolating point may be outside the face; this is a statement about the
whole supporting space, not a claim that the face has unbounded height. -/
lemma height_surjective_of_endpoints (z : E →ᵃ[ℝ] ℝ) {a b : E}
    (ha : z a = 0) (hb : z b = 1) : Function.Surjective z := by
  intro t
  exact ⟨AffineMap.lineMap a b t, height_lineMap z ha hb t⟩

/-- Strict height of every original interior point is DERIVED from bounded
face height and a nonconstant affine height, not assumed for overlap witnesses.
Finite-dimensional real spaces are complete, so the pinned affine open-map
lemma applies. -/
theorem interior_height_strict {F : Set E} (z : E →ᵃ[ℝ] ℝ)
    (hz : Continuous z) (hSurj : Function.Surjective z)
    (hBounds : ∀ x ∈ F, z x ∈ Icc (0 : ℝ) 1)
    {x : E} (hx : x ∈ interior F) : 0 < z x ∧ z x < 1 := by
  have hImage : z '' interior F ⊆ Icc (0 : ℝ) 1 := by
    rintro y ⟨p, hp, rfl⟩
    exact hBounds p (interior_subset hp)
  have hOpen : IsOpenMap z := z.isOpenMap hz hSurj
  have hzint : z x ∈ interior (Icc (0 : ℝ) 1) :=
    (interior_maximal hImage (hOpen (interior F) isOpen_interior)) ⟨x, hx, rfl⟩
  simpa only [interior_Icc, mem_Ioo] using hzint

end Height

section Witnesses
variable {ι : Type*} {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]
  {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
  [FiniteDimensional ℝ Q]

/-- No strict overlap of any distinct developed faces, not merely neighbors. -/
def Safe (F : (i : ι) → Set (E i)) (U : (i : ι) → E i → Q) : Prop :=
  ∀ i j, i ≠ j → Disjoint (interior (U i '' F i)) (interior (U j '' F j))

/-- Equal images of two ORIGINAL face-interior material points. -/
def Overlaps (F : (i : ι) → Set (E i)) (U : (i : ι) → E i → Q) : Prop :=
  ∃ i j, i ≠ j ∧ ∃ p ∈ interior (F i), ∃ q ∈ interior (F j), U i p = U j q

lemma embedding_image_interior
    {i : ι} (hd : Module.finrank ℝ (E i) = Module.finrank ℝ Q)
    (f : E i →ᵃⁱ[ℝ] Q) (F : Set (E i)) :
    f '' interior F = interior (f '' F) := by
  exact image_interior_eq (planeEquiv hd f) F

/-- Bridge from material witnesses to the declared planar-image predicate. -/
theorem not_safe_of_overlap
    (hd : ∀ i, Module.finrank ℝ (E i) = Module.finrank ℝ Q)
    {F : (i : ι) → Set (E i)} (U : (i : ι) → E i →ᵃⁱ[ℝ] Q)
    (hw : Overlaps F (fun i => U i)) : ¬ Safe F (fun i => U i) := by
  rcases hw with ⟨i, j, hij, p, hp, q, hq, heq⟩
  change U i p = U j q at heq
  intro hs
  have hpi : U i p ∈ interior (U i '' F i) := by
    rw [← embedding_image_interior (hd i) (U i) (F i)]
    exact ⟨p, hp, rfl⟩
  have hqj : U i p ∈ interior (U j '' F j) := by
    rw [heq, ← embedding_image_interior (hd j) (U j) (F j)]
    exact ⟨q, hq, rfl⟩
  exact (Set.disjoint_left.mp (hs i j hij)) hpi hqj

/-- A genuine strict planar overlap supplies source-interior witnesses.
The equal-dimension plane adapter is reused, not supplied as a new assumption. -/
theorem overlap_of_not_safe
    (hd : ∀ i, Module.finrank ℝ (E i) = Module.finrank ℝ Q)
    {F : (i : ι) → Set (E i)} (U : (i : ι) → E i →ᵃⁱ[ℝ] Q)
    (hbad : ¬ Safe F (fun i => U i)) : Overlaps F (fun i => U i) := by
  classical
  by_contra hw
  apply hbad
  intro i j hij
  apply Set.disjoint_left.mpr
  intro y hyi hyj
  change y ∈ interior (U i '' F i) at hyi
  change y ∈ interior (U j '' F j) at hyj
  rw [← embedding_image_interior (hd i) (U i) (F i)] at hyi
  rw [← embedding_image_interior (hd j) (U j) (F j)] at hyj
  rcases hyi with ⟨p, hp, hpy⟩
  rcases hyj with ⟨q, hq, hqy⟩
  exact hw ⟨i, j, hij, p, hp, q, hq, hpy.trans hqy.symm⟩

/-- The SAME material overlap survives all sufficiently light trims. Height
bounds/nonconstancy are original data for every face, not retained witnesses. -/
theorem fixed_overlap_survives
    (F : (i : ι) → Set (E i)) (z : (i : ι) → E i →ᵃ[ℝ] ℝ)
    (hz : ∀ i, Continuous (z i))
    (hBounds : ∀ i, ∀ x ∈ F i, z i x ∈ Icc (0 : ℝ) 1)
    (hLevels : ∀ i, ∃ a b : E i, z i a = 0 ∧ z i b = 1)
    (U : (i : ι) → E i → Q) (hw : Overlaps F U) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ (1 : ℝ)/2 ∧
      ∀ d : ℝ, 0 < d → d < eps →
        Overlaps (fun i => heightTrim (F i) (z i) d) U := by
  rcases hw with ⟨i, j, hij, p, hp, q, hq, heq⟩
  have hSurj (k : ι) : Function.Surjective (z k) := by
    obtain ⟨a, b, ha, hb⟩ := hLevels k
    exact height_surjective_of_endpoints (z k) ha hb
  have hpi := interior_height_strict (z i) (hz i) (hSurj i) (hBounds i) hp
  have hqj := interior_height_strict (z j) (hz j) (hSurj j) (hBounds j) hq
  let ep : ℝ := min (z i p) (1 - z i p)
  let eq : ℝ := min (z j q) (1 - z j q)
  let eps : ℝ := min ((1 : ℝ)/2) (min ep eq)
  have hep : 0 < ep := lt_min hpi.1 (sub_pos.mpr hpi.2)
  have heqpos : 0 < eq := lt_min hqj.1 (sub_pos.mpr hqj.2)
  have heps : 0 < eps := lt_min (by norm_num) (lt_min hep heqpos)
  have hleP : eps ≤ ep := (min_le_right _ _).trans (min_le_left _ _)
  have hleQ : eps ≤ eq := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨eps, heps, min_le_left _ _, ?_⟩
  intro d _hd0 hd
  have hpLo : d < z i p := hd.trans_le (hleP.trans (min_le_left _ _))
  have hpUp : d < 1 - z i p := hd.trans_le (hleP.trans (min_le_right _ _))
  have hqLo : d < z j q := hd.trans_le (hleQ.trans (min_le_left _ _))
  have hqUp : d < 1 - z j q := hd.trans_le (hleQ.trans (min_le_right _ _))
  exact ⟨i, j, hij, p, interior_heightTrim (hz i) hp hpLo (by linarith),
    q, interior_heightTrim (hz j) hq hqLo (by linarith), heq⟩

/-- One common injective target alignment preserves the witness equality.
Different per-face alignments would NOT justify this implication. -/
lemma overlap_under_common_alignment
    {D : (i : ι) → Set (E i)} {U T : (i : ι) → E i → Q}
    (C : Q ≃ᵃⁱ[ℝ] Q) (hAlign : ∀ i, ∀ x : E i, C (T i x) = U i x)
    (hw : Overlaps D U) : Overlaps D T := by
  rcases hw with ⟨i, j, hij, p, hp, q, hq, heq⟩
  refine ⟨i, j, hij, p, hp, q, hq, C.injective ?_⟩
  calc
    C (T i p) = U i p := hAlign i p
    _ = U j q := heq
    _ = C (T j q) := (hAlign j q).symm

end Witnesses

section SingleSeam
variable {n : ℕ} {E : Fin (n + 1) → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]
  {Q A : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
  [FiniteDimensional ℝ Q] [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- The full development's bad seam stays bad in EVERY independently supplied
admissible trimmed development below its threshold. Exact restriction is
obtained by calling the checked assembly theorem, not by an input axiom. -/
theorem unsafe_persists_in_independent_trims
    (hdE : ∀ i, Module.finrank ℝ (E i) = 2) (hdQ : Module.finrank ℝ Q = 2)
    (F : (i : Fin (n + 1)) → Set (E i))
    (z : (i : Fin (n + 1)) → E i →ᵃ[ℝ] ℝ)
    (hF : ∀ i, Convex ℝ (F i)) (hz : ∀ i, Continuous (z i))
    (hBounds : ∀ i, ∀ x ∈ F i, z i x ∈ Icc (0 : ℝ) 1)
    (hLevels : ∀ i, ∃ a b : E i, z i a = 0 ∧ z i b = 1)
    (iota : (i : Fin (n + 1)) → E i →ᵃ[ℝ] A)
    (sL : (j : Fin n) → EdgeSeed (F j.castSucc) (z j.castSucc))
    (sR : (j : Fin n) → EdgeSeed (F j.succ) (z j.succ))
    (hmA : ∀ j, iota j.castSucc (sL j).a = iota j.succ (sR j).a)
    (hmB : ∀ j, iota j.castSucc (sL j).b = iota j.succ (sR j).b)
    (U : (i : Fin (n + 1)) → E i →ᵃⁱ[ℝ] Q)
    (hU : DevelopmentOn iota F (fun i => U i))
    (hbad : ¬ Safe F (fun i => U i)) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ (1 : ℝ)/2 ∧
      ∀ d : ℝ, 0 < d → d < eps →
      ∀ T : (i : Fin (n + 1)) → E i →ᵃⁱ[ℝ] Q,
        DevelopmentOn iota (fun i => heightTrim (F i) (z i) d) (fun i => T i) →
        ¬ Safe (fun i => heightTrim (F i) (z i) d) (fun i => T i) := by
  have hd : ∀ i, Module.finrank ℝ (E i) = Module.finrank ℝ Q :=
    fun i => (hdE i).trans hdQ.symm
  have hw := overlap_of_not_safe hd U hbad
  obtain ⟨eps, heps, hcap, hpersist⟩ :=
    fixed_overlap_survives F z hz hBounds hLevels (fun i => U i) hw
  refine ⟨eps, heps, hcap, ?_⟩
  intro d hd0 hdlt T hT
  have hd1 : d < (1 : ℝ)/2 := hdlt.trans_le hcap
  obtain ⟨C, hAlign, _⟩ := exactRestriction_of_planeEmbeddings hdE hdQ
    F z hF hz iota sL sR hmA hmB hd0 hd1 U T hU hT
  exact not_safe_of_overlap hd T
    (overlap_under_common_alignment C hAlign (hpersist d hd0 hdlt))

end SingleSeam

/-- Finite logical closure. `goodTrim` may choose a different label for every
depth. Finiteness supplies ONE depth below ALL bad-label thresholds. -/
theorem finite_persistence_forces_good
    {S : Type*} [Finite S] (goodFull : S → Prop) (goodTrim : S → ℝ → Prop)
    (hSmall : ∀ d : ℝ, 0 < d → d < (1 : ℝ)/2 → ∃ e, goodTrim e d)
    (hPersist : ∀ e, ¬ goodFull e →
      ∃ eps : ℝ, 0 < eps ∧ eps ≤ (1 : ℝ)/2 ∧
        ∀ d : ℝ, 0 < d → d < eps → ¬ goodTrim e d) :
    ∃ e, goodFull e := by
  classical
  by_contra hNo
  have hBad : ∀ e, ¬ goodFull e := by simpa only [not_exists] using hNo
  choose eps hPos hCap hBadTrim using fun e => hPersist e (hBad e)
  have hn : Nonempty S := by
    obtain ⟨e, _⟩ := hSmall ((1 : ℝ)/4) (by norm_num) (by norm_num)
    exact ⟨e⟩
  letI : Nonempty S := hn
  obtain ⟨e0, hMin⟩ := Finite.exists_min eps
  have hd0 : 0 < eps e0 / 2 := half_pos (hPos e0)
  have hdSelf : eps e0 / 2 < eps e0 := half_lt_self (hPos e0)
  have hd1 : eps e0 / 2 < (1 : ℝ)/2 := hdSelf.trans_le (hCap e0)
  obtain ⟨e, hGood⟩ := hSmall (eps e0 / 2) hd0 hd1
  exact hBadTrim e (eps e0 / 2) hd0 (hdSelf.trans_le (hMin e)) hGood

section FiniteSeams
variable {S : Type*} [Finite S] {n : ℕ}
  {E : S → Fin (n + 1) → Type*}
  [∀ e i, NormedAddCommGroup (E e i)] [∀ e i, InnerProductSpace ℝ (E e i)]
  [∀ e i, FiniteDimensional ℝ (E e i)]
  {Q A : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
  [FiniteDimensional ℝ Q] [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- ENDPOINT. Safe original seam from the original encoded data and the
explicit ordinary-trim existence premise. The premise is the slot for the
EXTERNAL ordinary nested-band theorem; it is not an axiom declared here.
No exact-restriction, persistent-overlap, safe full seam, or global full-layout
nonoverlap assumption occurs in this statement. -/
theorem exists_safe_original_seam_of_trimmed_existence
    (hdE : ∀ e i, Module.finrank ℝ (E e i) = 2) (hdQ : Module.finrank ℝ Q = 2)
    (F : (e : S) → (i : Fin (n + 1)) → Set (E e i))
    (z : (e : S) → (i : Fin (n + 1)) → E e i →ᵃ[ℝ] ℝ)
    (hF : ∀ e i, Convex ℝ (F e i)) (hz : ∀ e i, Continuous (z e i))
    (hBounds : ∀ e i, ∀ x ∈ F e i, z e i x ∈ Icc (0 : ℝ) 1)
    (hLevels : ∀ e i, ∃ a b : E e i, z e i a = 0 ∧ z e i b = 1)
    (iota : (e : S) → (i : Fin (n + 1)) → E e i →ᵃ[ℝ] A)
    (sL : (e : S) → (j : Fin n) → EdgeSeed (F e j.castSucc) (z e j.castSucc))
    (sR : (e : S) → (j : Fin n) → EdgeSeed (F e j.succ) (z e j.succ))
    (hmA : ∀ e j, iota e j.castSucc (sL e j).a = iota e j.succ (sR e j).a)
    (hmB : ∀ e j, iota e j.castSucc (sL e j).b = iota e j.succ (sR e j).b)
    (U : (e : S) → (i : Fin (n + 1)) → E e i →ᵃⁱ[ℝ] Q)
    (hU : ∀ e, DevelopmentOn (iota e) (F e) (fun i => U e i))
    (hTrimmedExistence : ∀ d : ℝ, 0 < d → d < (1 : ℝ)/2 →
      ∃ e : S, ∃ T : (i : Fin (n + 1)) → E e i →ᵃⁱ[ℝ] Q,
        DevelopmentOn (iota e) (fun i => heightTrim (F e i) (z e i) d)
          (fun i => T i) ∧
        Safe (fun i => heightTrim (F e i) (z e i) d) (fun i => T i)) :
    ∃ e : S, Safe (F e) (fun i => U e i) := by
  apply finite_persistence_forces_good
    (fun e => Safe (F e) (fun i => U e i))
    (fun e d => ∃ T : (i : Fin (n + 1)) → E e i →ᵃⁱ[ℝ] Q,
      DevelopmentOn (iota e) (fun i => heightTrim (F e i) (z e i) d)
        (fun i => T i) ∧
      Safe (fun i => heightTrim (F e i) (z e i) d) (fun i => T i))
    hTrimmedExistence
  intro e hbad
  obtain ⟨eps, heps, hcap, hpersist⟩ := unsafe_persists_in_independent_trims
    (hdE e) hdQ (F e) (z e) (hF e) (hz e) (hBounds e) (hLevels e)
    (iota e) (sL e) (sR e) (hmA e) (hmB e) (U e) (hU e) hbad
  refine ⟨eps, heps, hcap, ?_⟩
  intro d hd0 hdlt hGood
  rcases hGood with ⟨T, hT, hSafe⟩
  exact hpersist d hd0 hdlt T hT hSafe

end FiniteSeams
end FiniteWitnessClosure

#print axioms FiniteWitnessClosure.interior_height_strict
#print axioms FiniteWitnessClosure.not_safe_of_overlap
#print axioms FiniteWitnessClosure.overlap_of_not_safe
#print axioms FiniteWitnessClosure.fixed_overlap_survives
#print axioms FiniteWitnessClosure.unsafe_persists_in_independent_trims
#print axioms FiniteWitnessClosure.finite_persistence_forces_good
#print axioms FiniteWitnessClosure.exists_safe_original_seam_of_trimmed_existence
