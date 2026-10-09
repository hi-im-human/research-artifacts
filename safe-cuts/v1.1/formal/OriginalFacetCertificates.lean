import CommonSupportMerge
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Fintype.EquivFin

/-!
# Construct the original Euclidean facet certificates and recover shared edges

System, 2026-09-19. COMPLETE PROOF-SCRIPT DRAFT, NOT COMPILED HERE.

Inputs: only the unchanged raw clockwise polygons and positive physical height.
The merged unit rays, finite original samples, entire-plane isometric charts,
HalfspaceData and FacetCertificate family are CONSTRUCTED. No correct incidence,
precomputed facets, chart, interior seed or strict-sample field is supplied.

A shared point of two distinct side faces at interior height supplies BOTH
original rim endpoints internally, and hence the earlier OriginalEdge object.
This does not yet choose a cyclic enumeration or finish the one-cut application.
-/

open Set
open scoped BigOperators Classical
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open EuclideanPrismatoidCoordinates CommonSupportMerge PolyhedralInputBridge

namespace OriginalFacetCertificates
noncomputable section

section Planar
variable {n : ℕ} [NeZero n] (P : ReducedConvexPolygon n)

lemma tight_maximizes (u : Plane) (i : Fin n)
    (hi : inner ℝ u (P.vertex i) = supportValue P u) : Maximizes P u i := by
  intro x hx
  rw [hi]
  exact supportIndex_max P u x hx

/-- Supporting both ends of a real raw edge forces its POSITIVE normal ray. -/
theorem positive_ray_of_edge_maxima (w : Plane) (hw : w ≠ 0) (i : Fin n)
    (hi : Maximizes P w i) (hj : Maximizes P w (next i)) :
    ∃ c : ℝ, 0 < c ∧ w = c • outwardNormal P.vertex i := by
  have he : inner ℝ w (ahead P i) = 0 := by
    have h1 := hi _ (P.vertex_mem_body (next i))
    have h2 := hj _ (P.vertex_mem_body i)
    simp only [ahead, inner_sub_right]
    linarith
  have htwo := (maximizes_iff_two P w i).mp hi
  have hD := corner_det_pos P i
  let c := -inner ℝ w (back P i) / det (back P i) (ahead P i)
  have hrec := normal_reconstruct (back P i) (ahead P i) w hD.ne'
  have hwc : w = c • outwardNormal P.vertex i := by
    rw [he] at hrec
    simpa [c, outwardNormal, edgeVector, ahead] using hrec
  have hc0 : 0 ≤ c := div_nonneg (neg_nonneg.mpr htwo.1) hD.le
  have hc : 0 < c := by
    by_contra hn
    have hz : c = 0 := le_antisymm (by linarith) hc0
    exact hw (by simpa [hz] using hwc)
  exact ⟨c,hc,hwc⟩

lemma unit_edge_tight (i : Fin n) :
    inner ℝ (unitRay (outwardNormal P.vertex i)) (P.vertex i) =
        supportValue P (unitRay (outwardNormal P.vertex i)) ∧
    inner ℝ (unitRay (outwardNormal P.vertex i)) (P.vertex (next i)) =
        supportValue P (unitRay (outwardNormal P.vertex i)) := by
  let c := ‖outwardNormal P.vertex i‖⁻¹
  have hc : 0 < c := inv_pos.mpr (norm_pos_iff.mpr (P.outwardNormal_ne_zero i))
  have hm : Maximizes P (unitRay (outwardNormal P.vertex i)) i := by
    intro x hx
    have hr := P.body_edge_nonpos i hx
    rw [P.edgeRow_apply, inner_sub_right] at hr
    change inner ℝ (c • outwardNormal P.vertex i) x ≤
      inner ℝ (c • outwardNormal P.vertex i) (P.vertex i)
    simp only [real_inner_smul_left]
    exact mul_le_mul_of_nonneg_left (by linarith) hc.le
  have hs := supportValue_at P _ i hm
  have he := (P.vertex_edge_eq_iff i (next i)).mpr (Or.inr rfl)
  rw [P.edgeRow_apply, inner_sub_right] at he
  constructor
  · exact hs.symm
  · rw [hs]
    simp only [unitRay, real_inner_smul_left]
    rw [sub_eq_zero.mp he]

/-- A unit direction containing all the tight vertices of an edge normal is
that SAME unit direction. This will rule out redundant side certificates. -/
lemma unit_unique_on_edge (i : Fin n) (v : Plane) (hv : ‖v‖ = 1)
    (hcontain : ∀ j, inner ℝ (unitRay (outwardNormal P.vertex i)) (P.vertex j) =
      supportValue P (unitRay (outwardNormal P.vertex i)) →
      inner ℝ v (P.vertex j) = supportValue P v) :
    v = unitRay (outwardNormal P.vertex i) := by
  have hv0 : v ≠ 0 := by intro hz; simpa [hz] using hv
  have ht := unit_edge_tight P i
  obtain ⟨c,hc,he⟩ := positive_ray_of_edge_maxima P v hv0 i
    (tight_maximizes P v i (hcontain i ht.1))
    (tight_maximizes P v (next i) (hcontain (next i) ht.2))
  have hn := (unitRay_eq_iff hv0 (P.outwardNormal_ne_zero i)).mpr ⟨c,hc,he⟩
  simpa [unitRay,hv] using hn
end Planar

section Pair
variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)

abbrev Side := {u : Plane // u ∈ mergedRays A B}
abbrev Row := Fin 2 ⊕ Side A B
abbrev RawIndex := Fin nB ⊕ Fin nA

lemma side_unit (u : Side A B) : ‖u.val‖ = 1 := by
  obtain ⟨k,hk⟩ := (mem_mergedRays A B u.val).mp u.property
  rw [hk]
  exact unitRay_norm (inputNormal_ne_zero A B k)

lemma side_ne_zero (u : Side A B) : u.val ≠ 0 := by
  intro h
  have hu := side_unit A B u
  simpa [h] using hu

def flatLinear : PhysicalAmbient →ₗ[ℝ] Plane :=
  (LinearMap.fst ℝ Plane ℝ).comp coordinateEquiv.symm.toLinearMap

def heightLinear (h : ℝ) : PhysicalAmbient →ₗ[ℝ] ℝ :=
  h⁻¹ • (LinearMap.snd ℝ Plane ℝ).comp coordinateEquiv.symm.toLinearMap

def sideLinear (h : ℝ) (u : Plane) : PhysicalAmbient →ₗ[ℝ] ℝ :=
  (innerSL ℝ u).toLinearMap.comp flatLinear -
    (supportValue A u - supportValue B u) • heightLinear h

def sideRow (h : ℝ) (u : Plane) : PhysicalAmbient →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ PhysicalAmbient (supportValue B u) - (sideLinear A B h u).toAffineMap

def rowMap (h : ℝ) : Row A B → PhysicalAmbient →ᵃ[ℝ] ℝ
  | Sum.inl i => if i = 0 then (heightLinear h).toAffineMap
      else AffineMap.const ℝ PhysicalAmbient 1 - (heightLinear h).toAffineMap
  | Sum.inr u => sideRow A B h u.val

def halfspaces (h : ℝ) : HalfspaceData (K := Row A B) (A := PhysicalAmbient) where
  row := rowMap A B h
  row_continuous := fun k => (rowMap A B h k).continuous_of_finiteDimensional
  height := (heightLinear h).toAffineMap
  height_continuous := (heightLinear h).toAffineMap.continuous_of_finiteDimensional
  lower := Sum.inl 0
  upper := Sum.inl 1
  lower_eq := by intro p; simp [rowMap]
  upper_eq := by intro p; simp [rowMap]

lemma height_apply (h : ℝ) (p : PhysicalAmbient) :
    heightLinear h p = (unpack p).2 / h := by
  simp [heightLinear,coordinateEquiv,unpack,inv_mul_eq_div]

lemma sideRow_apply (h : ℝ) (u : Plane) (p : PhysicalAmbient) :
    sideRow A B h u p = rowBound A B ((unpack p).2/h) u - inner ℝ u (unpack p).1 := by
  simp [sideRow,sideLinear,flatLinear,heightLinear,coordinateEquiv,rowBound,inv_mul_eq_div]
  <;> ring

lemma sideRow_lower (h : ℝ) (u x : Plane) :
    sideRow A B h u (pack (lowerLift x)) = supportValue B u - inner ℝ u x := by
  rw [sideRow_apply]
  change rowBound A B (0 / h) u - inner ℝ u x =
    supportValue B u - inner ℝ u x
  simp [pack,unpack,lowerLift,rowBound]

lemma sideRow_upper {h : ℝ} (hh : 0 < h) (u x : Plane) :
    sideRow A B h u (pack (upperLift h x)) = supportValue A u - inner ℝ u x := by
  rw [sideRow_apply]
  change rowBound A B (h / h) u - inner ℝ u x =
    supportValue A u - inner ℝ u x
  simp [pack,unpack,upperLift,rowBound,hh.ne']

/-- The constructed HalfspaceData is faithful to the independently defined hull. -/
theorem halfspaces_body {h : ℝ} (hh : 0 < h) :
    (halfspaces A B h).body = physicalPrismatoid A B h := by
  rw [physicalPrismatoid_eq_merged_halfspaces A B hh]
  ext p
  constructor
  · intro hp
    have h0 := hp (Sum.inl 0)
    have h1 := hp (Sum.inl 1)
    change 0 ≤ heightLinear h p at h0
    change 0 ≤ 1-heightLinear h p at h1
    refine ⟨⟨?_,?_⟩,?_⟩
    · simpa [height_apply] using h0
    · have hh1 : 0 ≤ 1-heightLinear h p := h1
      rw [height_apply] at hh1
      linarith
    · intro u hu
      have hside := hp (Sum.inr ⟨u,hu⟩)
      change 0 ≤ sideRow A B h u p at hside
      rw [sideRow_apply] at hside
      linarith
  · rintro ⟨ht,hp⟩ k
    rcases k with i | u
    · fin_cases i
      · change 0 ≤ heightLinear h p
        simpa [height_apply] using ht.1
      · change 0 ≤ 1-heightLinear h p
        rw [height_apply]
        linarith [ht.2]
    · change 0 ≤ sideRow A B h u.val p
      rw [sideRow_apply]
      exact sub_nonneg.mpr (hp u.val u.property)

def rawPoint (h : ℝ) : RawIndex (nA := nA) (nB := nB) → PhysicalAmbient
  | Sum.inl j => pack (lowerLift (B.vertex j))
  | Sum.inr i => pack (upperLift h (A.vertex i))

def Tight (u : Plane) : RawIndex (nA := nA) (nB := nB) → Prop
  | Sum.inl j => inner ℝ u (B.vertex j) = supportValue B u
  | Sum.inr i => inner ℝ u (A.vertex i) = supportValue A u

abbrev Sample (u : Side A B) := {k : RawIndex (nA := nA) (nB := nB) // Tight A B u.val k}

instance sample_nonempty (u : Side A B) : Nonempty (Sample A B u) :=
  ⟨⟨Sum.inl (supportIndex B u.val),rfl⟩⟩

lemma rawPoint_mem {h : ℝ} (hh : 0 < h) (k : RawIndex (nA := nA) (nB := nB)) :
    rawPoint A B h k ∈ (halfspaces A B h).body := by
  rw [halfspaces_body A B hh,←pack_prismatoid A B h]
  cases k with
  | inl j => exact ⟨_,lower_mem_prismatoid A B h (B.vertex_mem_body j),rfl⟩
  | inr i => exact ⟨_,upper_mem_prismatoid A B h (A.vertex_mem_body i),rfl⟩

lemma rawPoint_tight_iff {h : ℝ} (hh : 0 < h) (u : Plane)
    (k : RawIndex (nA := nA) (nB := nB)) :
    sideRow A B h u (rawPoint A B h k) = 0 ↔ Tight A B u k := by
  cases k with
  | inl j => rw [rawPoint,sideRow_lower]; simp only [Tight,sub_eq_zero]; exact eq_comm
  | inr i => rw [rawPoint,sideRow_upper A B hh]; simp only [Tight,sub_eq_zero]; exact eq_comm

/-- The strict-other-row property is DERIVED from raw support vertices.
Keeping duplicate rays as separate rows would make this statement fail. -/
theorem samples_strict {h : ℝ} (hh : 0 < h) (u : Side A B)
    (k : Row A B) (hk : k ≠ Sum.inr u) :
    ∃ s : Sample A B u, 0 < (halfspaces A B h).row k (rawPoint A B h s.val) := by
  cases k with
  | inl i =>
      fin_cases i
      · refine ⟨⟨Sum.inr (supportIndex A u.val),rfl⟩,?_⟩
        change 0 < heightLinear h (pack (upperLift h (A.vertex (supportIndex A u.val))))
        rw [height_apply]
        simp [pack,unpack,upperLift,hh.ne']
      · refine ⟨⟨Sum.inl (supportIndex B u.val),rfl⟩,?_⟩
        change 0 < 1-heightLinear h (pack (lowerLift (B.vertex (supportIndex B u.val))))
        rw [height_apply]
        simp [pack,unpack,lowerLift]
  | inr v =>
      by_contra hn
      push_neg at hn
      have hzero : ∀ s : Sample A B u, sideRow A B h v.val (rawPoint A B h s.val) = 0 := by
        intro s
        exact le_antisymm (hn s) (rawPoint_mem A B hh s.val (Sum.inr v))
      have hcontains : ∀ j : RawIndex (nA := nA) (nB := nB),
          Tight A B u.val j → Tight A B v.val j := by
        intro j hj
        exact (rawPoint_tight_iff A B hh v.val j).mp (hzero ⟨j,hj⟩)
      obtain ⟨r,hr⟩ := (mem_mergedRays A B u.val).mp u.property
      have he : v.val = u.val := by
        cases r with
        | inl i =>
            have hu : u.val = unitRay (outwardNormal A.vertex i) := hr
            rw [hu]
            apply unit_unique_on_edge A i v.val (side_unit A B v)
            intro j hj
            apply hcontains (Sum.inr j)
            simpa [Tight,hu] using hj
        | inr j =>
            have hu : u.val = unitRay (outwardNormal B.vertex j) := hr
            rw [hu]
            apply unit_unique_on_edge B j v.val (side_unit A B v)
            intro i hi
            apply hcontains (Sum.inl i)
            simpa [Tight,hu] using hi
      exact hk (congrArg Sum.inr (Subtype.ext he))

/-! ## Genuine Euclidean full-plane charts, built rather than supplied. -/

abbrev FaceSpace (h : ℝ) (u : Side A B) := LinearMap.ker (sideLinear A B h u.val)

def origin (h : ℝ) (u : Side A B) : PhysicalAmbient :=
  rawPoint A B h (Sum.inl (supportIndex B u.val))

lemma origin_zero (h : ℝ) (u : Side A B) : sideRow A B h u.val (origin A B h u) = 0 := by
  rw [origin,rawPoint,sideRow_lower]
  simp [supportValue]

lemma origin_linear (h : ℝ) (u : Side A B) :
    sideLinear A B h u.val (origin A B h u) = supportValue B u.val := by
  have ho := origin_zero A B h u
  change supportValue B u.val - sideLinear A B h u.val (origin A B h u) = 0 at ho
  linarith

def chart (h : ℝ) (u : Side A B) : FaceSpace A B h u →ᵃⁱ[ℝ] PhysicalAmbient where
  toFun x := origin A B h u + x.val
  linear := (sideLinear A B h u.val).ker.subtype
  map_vadd' := by
    intro p v
    change origin A B h u + ((v : PhysicalAmbient) + (p : PhysicalAmbient)) =
      (v : PhysicalAmbient) + (origin A B h u + (p : PhysicalAmbient))
    abel
  norm_map := fun _ => rfl

/-- Subtracting the origin is only used on the actual zero plane. -/
def pull (h : ℝ) (u : Side A B) (p : PhysicalAmbient)
    (hp : sideRow A B h u.val p = 0) : FaceSpace A B h u :=
  ⟨p-origin A B h u,by
    change sideLinear A B h u.val (p-origin A B h u) = 0
    rw [map_sub,origin_linear]
    change supportValue B u.val-sideLinear A B h u.val p = 0 at hp
    linarith⟩

@[simp] lemma chart_pull (h : ℝ) (u : Side A B) (p : PhysicalAmbient) (hp) :
    chart A B h u (pull A B h u p hp) = p := by
  change origin A B h u + (p-origin A B h u) = p
  abel

lemma chart_range (h : ℝ) (u : Side A B) :
    Set.range (chart A B h u) = {p | sideRow A B h u.val p = 0} := by
  ext p
  constructor
  · rintro ⟨x,rfl⟩
    have hx : sideLinear A B h u.val x.val = 0 := x.property
    change supportValue B u.val-sideLinear A B h u.val (origin A B h u+x.val) = 0
    rw [map_add,origin_linear,hx]
    ring
  · intro hp
    exact ⟨pull A B h u p hp,chart_pull A B h u p hp⟩

lemma sideLinear_surjective (h : ℝ) (u : Side A B) :
    Function.Surjective (sideLinear A B h u.val) := by
  intro c
  refine ⟨pack (lowerLift (c • u.val)),?_⟩
  have hu : inner ℝ u.val u.val = 1 := by
    rw [real_inner_self_eq_norm_sq,side_unit A B u]
    norm_num
  change inner ℝ u.val (c • u.val) - (supportValue A u.val-supportValue B u.val)*(h⁻¹*0) = c
  rw [inner_smul_right,hu]
  ring

/-- The chart's source has the inherited Euclidean norm and dimension TWO. -/
theorem faceSpace_finrank (h : ℝ) (u : Side A B) :
    Module.finrank ℝ (FaceSpace A B h u) = 2 := by
  have hdim := (sideLinear A B h u.val).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (sideLinear_surjective A B h u),finrank_top] at hdim
  have hR : Module.finrank ℝ ℝ = 1 := by simp
  have hP : Module.finrank ℝ PhysicalAmbient = 3 := by simp [PhysicalAmbient]
  rw [hR,hP] at hdim
  change Module.finrank ℝ (LinearMap.ker (sideLinear A B h u.val)) = 2
  omega

/-- Enumerate finite ORIGINAL tight samples. Repeated geometric samples are
allowed by the existing certificate contract; no new interior seed is input. -/
def sampleEquiv (u : Side A B) : Sample A B u ≃
    Fin ((Fintype.card (Sample A B u)-1)+1) :=
  Fintype.equivFinOfCardEq (by have := Fintype.card_pos (α := Sample A B u); omega)

def certificate {h : ℝ} (hh : 0 < h) (u : Side A B) :
    FacetCertificate (halfspaces A B h) (FaceSpace A B h u) where
  row := Sum.inr u
  chart := chart A B h u
  chart_range := chart_range A B h u
  sampleCount := Fintype.card (Sample A B u)-1
  samples t :=
    let s := (sampleEquiv A B u).symm t
    pull A B h u (rawPoint A B h s.val) ((rawPoint_tight_iff A B hh u.val s.val).mpr s.property)
  feasible := by
    intro t
    simp only [chart_pull]
    exact rawPoint_mem A B hh _
  strict_sample := by
    intro k hk
    obtain ⟨s,hs⟩ := samples_strict A B hh u k hk
    refine ⟨sampleEquiv A B u s,?_⟩
    simpa only [Equiv.symm_apply_apply,chart_pull] using hs

/-- Direct bijection to exactly the non-cap rows; no cyclic order is assumed. -/
def rowsEquiv : Side A B ≃
    {k : Row A B // k ≠ Sum.inl 0 ∧ k ≠ Sum.inl 1} :=
  Equiv.ofBijective (fun u => ⟨Sum.inr u,by simp⟩) (by
    constructor
    · intro u v huv
      exact Sum.inr.inj (congrArg Subtype.val huv)
    · rintro ⟨k,hk⟩
      cases k with
      | inl i =>
          fin_cases i
          · exact (hk.1 rfl).elim
          · exact (hk.2 rfl).elim
      | inr u => exact ⟨u,rfl⟩)

/-- Every constructed face has a derived nonempty two-dimensional interior. -/
theorem constructed_face_interior {h : ℝ} (hh : 0 < h) (u : Side A B) :
    Module.finrank ℝ (FaceSpace A B h u) = 2 ∧
    (interior (certificate A B hh u).domain).Nonempty := by
  exact ⟨faceSpace_finrank A B h u,
    ⟨(certificate A B hh u).center,(certificate A B hh u).center_interior⟩⟩

/-- All original lateral material is covered by CONSTRUCTED certificates. -/
theorem constructed_lateral_coverage {h : ℝ} (hh : 0 < h) :
    (⋃ u : Side A B, (certificate A B hh u).chart '' (certificate A B hh u).domain) =
      lateralBoundary (halfspaces A B h) := by
  apply material_band_eq (halfspaces A B h) (certificate A B hh) (rowsEquiv A B)
  intro u
  rfl

/-- WHOLE CERTIFICATE ENDPOINT. The finite table, whole Euclidean charts,
original samples, dimension and complete non-cap coverage are all outputs of
these definitions/theorems, not caller-supplied certificates. -/
theorem original_facet_table {h : ℝ} (hh : 0 < h) :
    (halfspaces A B h).body = physicalPrismatoid A B h ∧
    (∀ u : Side A B, Module.finrank ℝ (FaceSpace A B h u) = 2 ∧
      (interior (certificate A B hh u).domain).Nonempty) ∧
    (⋃ u : Side A B, (certificate A B hh u).chart '' (certificate A B hh u).domain) =
      lateralBoundary (halfspaces A B h) := by
  exact ⟨halfspaces_body A B hh,constructed_face_interior A B hh,
    constructed_lateral_coverage A B hh⟩

/-! ## A shared interior-height point constructs both original edge endpoints. -/

def materialFace {h : ℝ} (hh : 0 < h) (u : Side A B) : Set PhysicalAmbient :=
  (certificate A B hh u).chart '' (certificate A B hh u).domain

lemma mem_materialFace {h : ℝ} (hh : 0 < h) (u : Side A B) (p : PhysicalAmbient) :
    p ∈ materialFace A B hh u ↔
    p ∈ (halfspaces A B h).body ∧ sideRow A B h u.val p = 0 := by
  rw [materialFace,(certificate A B hh u).material_facet]
  rfl

/-- At strictly intermediate height, zero mixed slack forces zero slack on
BOTH original rims. At a cap height this implication would be false. -/
lemma tight_mixture {h : ℝ} (hh : 0 < h) (u : Plane) (p : PhysicalAmbient)
    (b a : Plane) (hb : b ∈ B.body) (ha : a ∈ A.body)
    (ht : (unpack p).2/h ∈ Ioo (0 : ℝ) 1)
    (hm : mixLinear ((unpack p).2/h) (b,a) = (unpack p).1)
    (hz : sideRow A B h u p = 0) :
    sideRow A B h u (pack (lowerLift b)) = 0 ∧
    sideRow A B h u (pack (upperLift h a)) = 0 := by
  let t := (unpack p).2/h
  let lb := supportValue B u-inner ℝ u b
  let la := supportValue A u-inner ℝ u a
  have hlb : 0 ≤ lb := sub_nonneg.mpr (supportIndex_max B u b hb)
  have hla : 0 ≤ la := sub_nonneg.mpr (supportIndex_max A u a ha)
  have he : (1-t)*lb+t*la = 0 := by
    rw [sideRow_apply,←hm] at hz
    change rowBound A B t u-inner ℝ u ((1-t) • b+t • a) = 0 at hz
    simp only [inner_add_right,inner_smul_right,rowBound] at hz
    dsimp [lb,la]
    nlinarith
  have h1 : 0 < 1-t := by dsimp [t]; linarith [ht.2]
  have h2 : 0 < t := ht.1
  have hp1 := mul_nonneg h1.le hlb
  have hp2 := mul_nonneg h2.le hla
  have lb0 : lb = 0 := by nlinarith
  have la0 : la = 0 := by nlinarith
  rw [sideRow_lower,sideRow_upper A B hh]
  exact ⟨lb0,la0⟩

/-- No endpoint or OriginalEdge certificate is supplied: a genuine shared
interior-height point supplies a convex decomposition, and its rim points
are proved common before pulling them into the constructed charts. -/
theorem originalEdge_of_shared_interior {h : ℝ} (hh : 0 < h)
    (u v : Side A B) (huv : u ≠ v) (p : PhysicalAmbient)
    (hpu : p ∈ materialFace A B hh u) (hpv : p ∈ materialFace A B hh v)
    (ht : (unpack p).2/h ∈ Ioo (0 : ℝ) 1) :
    Nonempty (OriginalEdge (certificate A B hh u) (certificate A B hh v)) := by
  obtain ⟨hbody,huz⟩ := (mem_materialFace A B hh u p).mp hpu
  obtain ⟨_,hvz⟩ := (mem_materialFace A B hh v p).mp hpv
  have hphys : p ∈ physicalPrismatoid A B h := by
    rwa [halfspaces_body A B hh] at hbody
  rw [←pack_prismatoid A B h] at hphys
  obtain ⟨q,hq,hqp⟩ := hphys
  have hqval : q = unpack p := by
    have he := congrArg unpack hqp
    exact (coordinateEquiv.symm_apply_apply q).symm.trans he
  rw [hqval,mem_prismatoid_iff A B hh] at hq
  obtain ⟨⟨b,a⟩,⟨hb,ha⟩,hm⟩ := hq.2
  have hzu := tight_mixture A B hh u.val p b a hb ha ht hm huz
  have hzv := tight_mixture A B hh v.val p b a hb ha ht hm hvz
  have lower_body : pack (lowerLift b) ∈ (halfspaces A B h).body := by
    rw [halfspaces_body A B hh,←pack_prismatoid A B h]
    exact ⟨_,lower_mem_prismatoid A B h hb,rfl⟩
  have upper_body : pack (upperLift h a) ∈ (halfspaces A B h).body := by
    rw [halfspaces_body A B hh,←pack_prismatoid A B h]
    exact ⟨_,upper_mem_prismatoid A B h ha,rfl⟩
  refine ⟨{
    aL := pull A B h u (pack (lowerLift b)) hzu.1
    bL := pull A B h u (pack (upperLift h a)) hzu.2
    aR := pull A B h v (pack (lowerLift b)) hzv.1
    bR := pull A B h v (pack (upperLift h a)) hzv.2
    aL_mem := ?_
    bL_mem := ?_
    aR_mem := ?_
    bR_mem := ?_
    a_height := ?_
    b_height := ?_
    match_a := ?_
    match_b := ?_
    distinct_rows := ?_ }⟩
  · change chart A B h u (pull A B h u _ hzu.1) ∈ (halfspaces A B h).body
    simpa only [chart_pull] using lower_body
  · change chart A B h u (pull A B h u _ hzu.2) ∈ (halfspaces A B h).body
    simpa only [chart_pull] using upper_body
  · change chart A B h v (pull A B h v _ hzv.1) ∈ (halfspaces A B h).body
    simpa only [chart_pull] using lower_body
  · change chart A B h v (pull A B h v _ hzv.2) ∈ (halfspaces A B h).body
    simpa only [chart_pull] using upper_body
  · change heightLinear h (chart A B h u (pull A B h u _ hzu.1)) = 0
    rw [chart_pull,height_apply]
    simp [pack,unpack,lowerLift]
  · change heightLinear h (chart A B h u (pull A B h u _ hzu.2)) = 1
    rw [chart_pull,height_apply]
    simp [pack,unpack,upperLift,hh.ne']
  · change chart A B h u (pull A B h u _ hzu.1) = chart A B h v (pull A B h v _ hzv.1)
    simp only [chart_pull]
  · change chart A B h u (pull A B h u _ hzu.2) = chart A B h v (pull A B h v _ hzv.2)
    simp only [chart_pull]
  · exact fun he => huv (Sum.inr.inj he)

/-- Exact full-height supporting-edge identity, derived from a shared point.
The uncut/cut labels and their global circular order are NOT asserted here. -/
theorem shared_faces_are_fullHeight_edge {h : ℝ} (hh : 0 < h)
    (u v : Side A B) (huv : u ≠ v) (p : PhysicalAmbient)
    (hpu : p ∈ materialFace A B hh u) (hpv : p ∈ materialFace A B hh v)
    (ht : (unpack p).2/h ∈ Ioo (0 : ℝ) 1) :
    ∃ lo hi : PhysicalAmbient, lo ≠ hi ∧
      heightLinear h lo = 0 ∧ heightLinear h hi = 1 ∧
      materialFace A B hh u ∩ materialFace A B hh v =
        AffineMap.lineMap lo hi '' Icc (0 : ℝ) 1 := by
  obtain ⟨ed⟩ := originalEdge_of_shared_interior A B hh u v huv p hpu hpv ht
  let C := certificate A B hh u
  refine ⟨C.chart ed.aL,C.chart ed.bL,?_,ed.a_height,ed.b_height,?_⟩
  · intro he
    have hh' := congrArg (heightLinear h) he
    have ha := ed.a_height
    have hb := ed.b_height
    change heightLinear h (C.chart ed.aL) = 0 at ha
    change heightLinear h (C.chart ed.bL) = 1 at hb
    rw [ha,hb] at hh'
    norm_num at hh'
  · exact ed.common_material_edge (faceSpace_finrank A B h u)


end Pair
end
end OriginalFacetCertificates

#print axioms OriginalFacetCertificates.positive_ray_of_edge_maxima
#print axioms OriginalFacetCertificates.samples_strict
#print axioms OriginalFacetCertificates.halfspaces_body
#print axioms OriginalFacetCertificates.chart_range
#print axioms OriginalFacetCertificates.faceSpace_finrank
#print axioms OriginalFacetCertificates.certificate
#print axioms OriginalFacetCertificates.original_facet_table
#check @OriginalFacetCertificates.certificate
#check @OriginalFacetCertificates.original_facet_table

#print axioms OriginalFacetCertificates.originalEdge_of_shared_interior
#print axioms OriginalFacetCertificates.shared_faces_are_fullHeight_edge
#check @OriginalFacetCertificates.shared_faces_are_fullHeight_edge
