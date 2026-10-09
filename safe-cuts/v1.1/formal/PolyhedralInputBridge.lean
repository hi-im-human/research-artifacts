import FiniteWitnessClosure

/-!
# One half-space body supplies the original local face inputs

System, 2026-09-19. UNCOMPILED DRAFT for Lean/Mathlib v4.34.0.

This is a certificate-based upstream bridge, not an algorithm extracting the
facet lattice of an arbitrary vertex polytope. A single finite half-space
body and a fixed table of faithful supporting-plane charts supply all cuts.
Finite feasible samples replace assumed interior seeds: their average is
proved interior by strict slack against every OTHER supporting inequality.
An original adjacent pair is proved to intersect in its actual height-0/1
segment; clipping that segment preserves its identity. The endpoint calls
the already-checked finite-witness closure on the derived original inputs.

Still explicit: the certificates/charts and cut orders must be supplied,
full developments must exist, and the ordinary-band theorem must supply the
independent safe-trim premise. No external theorem or new axiom is declared.
-/

open Set
open scoped BigOperators Affine
open TrimmedFacetWitnesses BandGeometryAssembly FiniteWitnessClosure

namespace PolyhedralInputBridge

section Mean
variable {I E : Type*} [Fintype I] [Nonempty I]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def average (v : I → E) : E :=
  (Fintype.card I : ℝ)⁻¹ • ∑ i, v i

/-- Affine maps preserve the equal-weight average; the nonempty index matters. -/
lemma average_affine (f : E →ᵃ[ℝ] ℝ) (v : I → E) :
    f (average v) = (Fintype.card I : ℝ)⁻¹ * ∑ i, f (v i) := by
  have hN : (Fintype.card I : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hf (x : E) : f x = f.linear x + f 0 := by
    have h := f.linearMap_vsub x (0 : E)
    change f.linear (x - 0) = f x - f 0 at h
    rw [sub_zero] at h
    linarith
  calc
    f (average v) = (Fintype.card I : ℝ)⁻¹ * ∑ i, f.linear (v i) + f 0 := by
      rw [hf]
      simp only [average, map_smul, map_sum, smul_eq_mul]
    _ = (Fintype.card I : ℝ)⁻¹ * ∑ i, (f.linear (v i) + f 0) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp [hN]
      <;> ring
    _ = (Fintype.card I : ℝ)⁻¹ * ∑ i, f (v i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (hf (v i)).symm

lemma average_positive (f : E →ᵃ[ℝ] ℝ) (v : I → E)
    (hNonneg : ∀ i, 0 ≤ f (v i)) (hPositive : ∃ i, 0 < f (v i)) :
    0 < f (average v) := by
  rw [average_affine]
  have hN : 0 < (Fintype.card I : ℝ) := by
    exact_mod_cast Fintype.card_pos
  apply mul_pos (inv_pos.mpr hN)
  obtain ⟨i, hi⟩ := hPositive
  exact hi.trans_le (Finset.single_le_sum (fun j _ => hNonneg j) (Finset.mem_univ i))

end Mean

section Halfspaces
variable {K A : Type*} [Fintype K] [DecidableEq K]
  [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- Original half-space data. The lower/upper rows encode normalized height.
No witness, face interior, unfolding, or safe-seam conclusion is an input. -/
structure HalfspaceData where
  row : K → A →ᵃ[ℝ] ℝ
  row_continuous : ∀ k, Continuous (row k)
  height : A →ᵃ[ℝ] ℝ
  height_continuous : Continuous height
  lower : K
  upper : K
  lower_eq : ∀ p, row lower p = height p
  upper_eq : ∀ p, row upper p = 1 - height p

namespace HalfspaceData
variable (H : HalfspaceData (K := K) (A := A))

def body : Set A := {p | ∀ k, 0 ≤ H.row k p}

lemma body_convex : Convex ℝ H.body := by
  have heq : H.body = ⋂ k : K, (H.row k) ⁻¹' Ici (0 : ℝ) := by
    ext p
    simp [body]
  rw [heq]
  exact convex_iInter (fun k => (convex_Ici (0 : ℝ)).affine_preimage (H.row k))

lemma height_bounds {p : A} (hp : p ∈ H.body) : H.height p ∈ Icc (0 : ℝ) 1 := by
  have hl := hp H.lower
  have hu := hp H.upper
  rw [H.lower_eq] at hl
  rw [H.upper_eq] at hu
  exact ⟨hl, by linarith⟩

end HalfspaceData

/-- A faithful whole-plane chart plus finite feasible samples. For each other
inequality, some sample is strictly inside that half-space. This condition
is checked on ORIGINAL samples, not on the average or a retained face.
An irredundant facet description with all original facet vertices supplies
such data; universal extraction of that description is not proved here. -/
structure FacetCertificate (H : HalfspaceData (K := K) (A := A))
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  row : K
  chart : E →ᵃⁱ[ℝ] A
  chart_range : Set.range chart = {p | H.row row p = 0}
  sampleCount : ℕ
  samples : Fin (sampleCount + 1) → E
  feasible : ∀ t, chart (samples t) ∈ H.body
  strict_sample : ∀ k, k ≠ row → ∃ t, 0 < H.row k (chart (samples t))

namespace FacetCertificate
variable {H : HalfspaceData (K := K) (A := A)} {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  (C : FacetCertificate H E)

def domain : Set E := C.chart ⁻¹' H.body

def height : E →ᵃ[ℝ] ℝ := H.height.comp C.chart.toAffineMap

def pullrow (k : K) : E →ᵃ[ℝ] ℝ := (H.row k).comp C.chart.toAffineMap

noncomputable def center : E := average C.samples

lemma own_zero (x : E) : H.row C.row (C.chart x) = 0 := by
  have hx : C.chart x ∈ Set.range C.chart := ⟨x, rfl⟩
  rw [C.chart_range] at hx
  exact hx

lemma domain_convex : Convex ℝ C.domain :=
  H.body_convex.affine_preimage C.chart.toAffineMap

lemma height_continuous : Continuous C.height :=
  H.height_continuous.comp C.chart.isometry.continuous

lemma height_bounds {x : E} (hx : x ∈ C.domain) : C.height x ∈ Icc (0 : ℝ) 1 :=
  H.height_bounds hx

lemma center_strict {k : K} (hk : k ≠ C.row) : 0 < C.pullrow k C.center := by
  apply average_positive (C.pullrow k) C.samples
  · intro t
    exact C.feasible t k
  · exact C.strict_sample k hk

/-- DERIVED original relative interior. Every non-own inequality is strictly
satisfied at the average; finitely many open half-spaces give a neighborhood. -/
theorem center_interior : C.center ∈ interior C.domain := by
  let O : Set E := ⋂ k : {k : K // k ≠ C.row}, {x | 0 < C.pullrow k.val x}
  have hO : IsOpen O :=
    isOpen_iInter_of_finite (fun k =>
      isOpen_lt continuous_const ((H.row_continuous k.val).comp C.chart.isometry.continuous))
  have hsub : O ⊆ C.domain := by
    intro x hx k
    by_cases hk : k = C.row
    · subst k
      exact (C.own_zero x).ge
    · exact (Set.mem_iInter.mp hx ⟨k, hk⟩).le
  have hc : C.center ∈ O := Set.mem_iInter.mpr (fun k => C.center_strict k.property)
  exact (interior_maximal hsub hO) hc

/-- The charted domain really is the original body's supporting face, not an
unrelated convex set carrying the same name. -/
theorem material_facet : C.chart '' C.domain = H.body ∩ {p | H.row C.row p = 0} := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, C.own_zero x⟩
  · rintro ⟨hp, hzero⟩
    have hr : p ∈ Set.range C.chart := by
      rw [C.chart_range]
      exact hzero
    obtain ⟨x, rfl⟩ := hr
    exact ⟨x, hp, rfl⟩

/-- Construct the old EdgeSeed from original finite inequalities and samples.
In particular neither original c_int nor sigma(c)>0 is a new input here. -/
noncomputable def edgeSeed (k : K) (hk : k ≠ C.row) (a b : E)
    (ha : a ∈ C.domain) (hb : b ∈ C.domain)
    (hza : C.height a = 0) (hzb : C.height b = 1)
    (hsa : C.pullrow k a = 0) (hsb : C.pullrow k b = 0) :
    EdgeSeed C.domain C.height where
  a := a
  b := b
  c := C.center
  sigma := C.pullrow k
  a_mem := ha
  b_mem := hb
  c_int := C.center_interior
  za := hza
  zb := hzb
  zc := C.height_bounds (interior_subset C.center_interior)
  sa := hsa
  sb := hsb
  sc := C.center_strict hk

end FacetCertificate

section Edges
variable {H : HalfspaceData (K := K) (A := A)} {L R : Type*}
  [NormedAddCommGroup L] [NormedSpace ℝ L]
  [NormedAddCommGroup R] [NormedSpace ℝ R]

/-- ORIGINAL endpoint data for two distinct supporting faces of ONE body.
No interior seed, retained point, or equality of intersection with a segment
is assumed: those are derived. Right heights follow from material identity. -/
structure OriginalEdge (CL : FacetCertificate H L) (CR : FacetCertificate H R) where
  aL : L
  bL : L
  aR : R
  bR : R
  aL_mem : aL ∈ CL.domain
  bL_mem : bL ∈ CL.domain
  aR_mem : aR ∈ CR.domain
  bR_mem : bR ∈ CR.domain
  a_height : CL.height aL = 0
  b_height : CL.height bL = 1
  match_a : CL.chart aL = CR.chart aR
  match_b : CL.chart bL = CR.chart bR
  distinct_rows : CL.row ≠ CR.row

namespace OriginalEdge
variable {CL : FacetCertificate H L} {CR : FacetCertificate H R}
  (e : OriginalEdge CL CR)

lemma right_height_a : CR.height e.aR = 0 := by
  change H.height (CR.chart e.aR) = 0
  rw [← e.match_a]
  exact e.a_height

lemma right_height_b : CR.height e.bR = 1 := by
  change H.height (CR.chart e.bR) = 1
  rw [← e.match_b]
  exact e.b_height

noncomputable def leftSeed : EdgeSeed CL.domain CL.height :=
  CL.edgeSeed CR.row e.distinct_rows.symm e.aL e.bL e.aL_mem e.bL_mem
    e.a_height e.b_height
    (by change H.row CR.row (CL.chart e.aL) = 0; rw [e.match_a]; exact CR.own_zero _)
    (by change H.row CR.row (CL.chart e.bL) = 0; rw [e.match_b]; exact CR.own_zero _)

noncomputable def rightSeed : EdgeSeed CR.domain CR.height :=
  CR.edgeSeed CL.row e.distinct_rows e.aR e.bR e.aR_mem e.bR_mem
    e.right_height_a e.right_height_b
    (by change H.row CL.row (CR.chart e.aR) = 0; rw [← e.match_a]; exact CL.own_zero _)
    (by change H.row CL.row (CR.chart e.bR) = 0; rw [← e.match_b]; exact CL.own_zero _)

lemma left_ne : e.aL ≠ e.bL := by
  intro hab
  have h := congrArg CL.height hab
  rw [e.a_height, e.b_height] at h
  norm_num at h

/-- Two actual supporting faces intersect in the original lateral segment.
This rules out replacing an original edge by an arbitrary face diagonal. -/
theorem common_material_edge [FiniteDimensional ℝ L]
    (hdL : Module.finrank ℝ L = 2) :
    (CL.chart '' CL.domain) ∩ (CR.chart '' CR.domain) =
      AffineMap.lineMap (CL.chart e.aL) (CL.chart e.bL) '' Icc (0 : ℝ) 1 := by
  ext p
  constructor
  · rintro ⟨⟨x, hx, hxp⟩, ⟨y, hy, hyp⟩⟩
    have hxzero : CL.pullrow CR.row x = 0 := by
      change H.row CR.row (CL.chart x) = 0
      rw [hxp, ← hyp]
      exact CR.own_zero y
    have hline : x ∈ line[ℝ, e.aL, e.bL] :=
      mem_line_of_level_eq hdL (CL.pullrow CR.row) e.left_ne
        e.leftSeed.sa e.leftSeed.sb e.leftSeed.sc.ne' hxzero
    obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hline
    have hzt : CL.height x = t := by
      rw [← ht]
      exact height_lineMap CL.height e.a_height e.b_height t
    refine ⟨t, ?_, ?_⟩
    · rw [← hzt]
      exact CL.height_bounds hx
    · exact (CL.chart.toAffineMap.apply_lineMap e.aL e.bL t).symm.trans
        ((congrArg CL.chart ht).trans hxp)
  · rintro ⟨t, ht, rfl⟩
    constructor
    · exact ⟨AffineMap.lineMap e.aL e.bL t,
        lineMap_mem_face CL.domain_convex e.aL_mem e.bL_mem ht,
        CL.chart.toAffineMap.apply_lineMap _ _ _⟩
    · refine ⟨AffineMap.lineMap e.aR e.bR t,
        lineMap_mem_face CR.domain_convex e.aR_mem e.bR_mem ht, ?_⟩
      calc
        CR.chart (AffineMap.lineMap e.aR e.bR t) =
            AffineMap.lineMap (CR.chart e.aR) (CR.chart e.bR) t :=
          CR.chart.toAffineMap.apply_lineMap _ _ _
        _ = AffineMap.lineMap (CL.chart e.aL) (CL.chart e.bL) t := by
          rw [← e.match_a, ← e.match_b]

/-- The same ORIGINAL supporting-edge identity under an actual height trim.
The only change is the interpolation interval, not the ambient edge or labels. -/
theorem common_trimmed_edge [FiniteDimensional ℝ L]
    (hdL : Module.finrank ℝ L = 2) {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2) :
    (CL.chart '' heightTrim CL.domain CL.height d) ∩
      (CR.chart '' heightTrim CR.domain CR.height d) =
    AffineMap.lineMap (CL.chart e.aL) (CL.chart e.bL) '' Icc d (1-d) := by
  have hheight (t : ℝ) :
      H.height (AffineMap.lineMap (CL.chart e.aL) (CL.chart e.bL) t) = t :=
    height_lineMap H.height e.a_height e.b_height t
  ext p
  constructor
  · rintro ⟨⟨x, hx, hxp⟩, ⟨y, hy, hyp⟩⟩
    have hp : p ∈ (CL.chart '' CL.domain) ∩ (CR.chart '' CR.domain) :=
      ⟨⟨x, hx.1, hxp⟩, ⟨y, hy.1, hyp⟩⟩
    rw [e.common_material_edge hdL] at hp
    rcases hp with ⟨t, _, htp⟩
    have hz : H.height p = t := by rw [← htp]; exact hheight t
    have hxheight : CL.height x = t := by
      change H.height (CL.chart x) = t
      rw [hxp]
      exact hz
    refine ⟨t, ?_, htp⟩
    simpa only [Set.mem_setOf_eq, mem_Icc, hxheight] using hx.2
  · rintro ⟨t, ht, htp⟩
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hp : p ∈ (CL.chart '' CL.domain) ∩ (CR.chart '' CR.domain) := by
      rw [e.common_material_edge hdL]
      exact ⟨t, ht01, htp⟩
    rcases hp with ⟨⟨x, hx, hxp⟩, ⟨y, hy, hyp⟩⟩
    have hpx : CL.height x = t := by
      change H.height (CL.chart x) = t
      rw [hxp, ← htp]
      exact hheight t
    have hpy : CR.height y = t := by
      change H.height (CR.chart y) = t
      rw [hyp, ← htp]
      exact hheight t
    exact ⟨⟨x, ⟨hx, by simpa only [Set.mem_setOf_eq, mem_Icc, hpx] using ht⟩, hxp⟩,
      ⟨y, ⟨hy, by simpa only [Set.mem_setOf_eq, mem_Icc, hpy] using ht⟩, hyp⟩⟩

end OriginalEdge
end Edges
/-- The original side surface as the union of non-cap supporting faces. -/
def lateralBoundary (H : HalfspaceData (K := K) (A := A)) : Set A :=
  {p | p ∈ H.body ∧ ∃ k : K, k ≠ H.lower ∧ k ≠ H.upper ∧ H.row k p = 0}

/-- A bijection to all non-cap rows prevents the input table from quietly
omitting a face. This is a checked coverage statement about ONE original body. -/
theorem material_band_eq {J : Type*} {E : J → Type*}
    [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace ℝ (E j)]
    (H : HalfspaceData (K := K) (A := A))
    (C : (j : J) → FacetCertificate H (E j))
    (rows : J ≃ {k : K // k ≠ H.lower ∧ k ≠ H.upper})
    (hRows : ∀ j, (C j).row = (rows j).val) :
    (⋃ j, (C j).chart '' (C j).domain) = lateralBoundary H := by
  ext p
  constructor
  · intro hp
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp
    rw [(C j).material_facet] at hj
    refine ⟨hj.1, (rows j).val, (rows j).property.1, (rows j).property.2, ?_⟩
    simpa only [Set.mem_setOf_eq, hRows j] using hj.2
  · rintro ⟨hp, k, hkL, hkU, hk0⟩
    obtain ⟨j, hj⟩ := rows.surjective ⟨k, hkL, hkU⟩
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_⟩
    rw [(C j).material_facet]
    refine ⟨hp, ?_⟩
    have hrow : (C j).row = k := (hRows j).trans (congrArg Subtype.val hj)
    rw [hrow]
    exact hk0

end Halfspaces

section Reindex
variable {J I A : Type*}

/-- Reordering the one fixed face table cannot add, omit, or replace material. -/
theorem material_union_reindex (D : J → Set A) (order : I ≃ J) :
    (⋃ i, D (order i)) = ⋃ j, D j := by
  ext p
  simp only [mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨order i, hi⟩
  · rintro ⟨j, hj⟩
    obtain ⟨i, rfl⟩ := order.surjective j
    exact ⟨i, hj⟩

end Reindex

section Endpoint
variable {K J S A Q : Type*} [Fintype K] [DecidableEq K] [Finite S]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [FiniteDimensional ℝ Q]
  {n : ℕ} {E : J → Type*}
  [∀ j, NormedAddCommGroup (E j)] [∀ j, InnerProductSpace ℝ (E j)]
  [∀ j, FiniteDimensional ℝ (E j)]

/-- ENDPOINT: one original half-space body and one fixed facet table replace
unrelated seam-indexed face data. Original EdgeSeed inputs are CONSTRUCTED.
The chosen seam is backed by an original nondegenerate supporting segment.

Cut orders, endpoint certificates, full developments and the external safe-
trim existence premise remain explicit. This does not discover the facet
cycle of every prismatoid or formalize the imported 2008 theorem. -/
theorem exists_safe_face_table_of_halfspace_data
    (H : HalfspaceData (K := K) (A := A))
    (C : (j : J) → FacetCertificate H (E j))
    (rows : J ≃ {k : K // k ≠ H.lower ∧ k ≠ H.upper})
    (hRows : ∀ j, (C j).row = (rows j).val)
    (hdE : ∀ j, Module.finrank ℝ (E j) = 2) (hdQ : Module.finrank ℝ Q = 2)
    (order : S → (Fin (n+1) ≃ J))
    (hinge : (e : S) → (j : Fin n) →
      OriginalEdge (C (order e j.castSucc)) (C (order e j.succ)))
    (cut : (e : S) → OriginalEdge (C (order e (Fin.last n))) (C (order e 0)))
    (U : (e : S) → (i : Fin (n+1)) → E (order e i) →ᵃⁱ[ℝ] Q)
    (hU : ∀ e, DevelopmentOn (fun i => (C (order e i)).chart.toAffineMap)
      (fun i => (C (order e i)).domain) (fun i => U e i))
    (hTrimmedExistence : ∀ d : ℝ, 0 < d → d < (1 : ℝ)/2 →
      ∃ e : S, ∃ T : (i : Fin (n+1)) → E (order e i) →ᵃⁱ[ℝ] Q,
        DevelopmentOn (fun i => (C (order e i)).chart.toAffineMap)
          (fun i => heightTrim (C (order e i)).domain (C (order e i)).height d)
          (fun i => T i) ∧
        Safe (fun i => heightTrim (C (order e i)).domain (C (order e i)).height d)
          (fun i => T i)) :
    ∃ e : S,
      Safe (fun i => (C (order e i)).domain) (fun i => U e i) ∧
      ((C (order e (Fin.last n))).chart '' (C (order e (Fin.last n))).domain) ∩
          ((C (order e 0)).chart '' (C (order e 0)).domain) =
        AffineMap.lineMap ((C (order e (Fin.last n))).chart (cut e).aL)
          ((C (order e (Fin.last n))).chart (cut e).bL) '' Icc (0 : ℝ) 1 ∧
      (⋃ i, (C (order e i)).chart '' (C (order e i)).domain) = lateralBoundary H := by
  have hLevels : ∀ e i, ∃ a b : E (order e i),
      (C (order e i)).height a = 0 ∧ (C (order e i)).height b = 1 := by
    intro e i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact ⟨(cut e).aL, (cut e).bL, (cut e).a_height, (cut e).b_height⟩
    · exact ⟨(hinge e j).aL, (hinge e j).bL,
        (hinge e j).a_height, (hinge e j).b_height⟩
  obtain ⟨e, he⟩ := FiniteWitnessClosure.exists_safe_original_seam_of_trimmed_existence
    (fun e i => hdE (order e i)) hdQ
    (fun e i => (C (order e i)).domain)
    (fun e i => (C (order e i)).height)
    (fun e i => (C (order e i)).domain_convex)
    (fun e i => (C (order e i)).height_continuous)
    (fun e i _ hx => (C (order e i)).height_bounds hx) hLevels
    (fun e i => (C (order e i)).chart.toAffineMap)
    (fun e j => (hinge e j).leftSeed)
    (fun e j => (hinge e j).rightSeed)
    (fun e j => (hinge e j).match_a)
    (fun e j => (hinge e j).match_b)
    U hU hTrimmedExistence
  refine ⟨e, he, (cut e).common_material_edge (hdE _), ?_⟩
  rw [material_union_reindex (fun j => (C j).chart '' (C j).domain) (order e)]
  exact material_band_eq H C rows hRows

end Endpoint
end PolyhedralInputBridge

#print axioms PolyhedralInputBridge.FacetCertificate.center_interior
#print axioms PolyhedralInputBridge.FacetCertificate.material_facet
#print axioms PolyhedralInputBridge.OriginalEdge.common_material_edge
#print axioms PolyhedralInputBridge.OriginalEdge.common_trimmed_edge
#print axioms PolyhedralInputBridge.material_band_eq
#print axioms PolyhedralInputBridge.material_union_reindex
#print axioms PolyhedralInputBridge.exists_safe_face_table_of_halfspace_data
#check @PolyhedralInputBridge.exists_safe_face_table_of_halfspace_data
