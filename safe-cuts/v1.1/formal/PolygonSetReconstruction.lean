import CutSurfaceQuotient
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Topology
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Finite hull reconstruction

The input is an arbitrary finite real planar point set with nonempty hull
interior. Minimal generators, inward separators, strict clockwise successors,
and a simple periodic supporting cycle are all derived. The old reverse
halfspace theorem then identifies the unchanged raw polygon with the original
hull, without assuming that the cycle exhausts the generators.

For two ordinary polygon sets, the final theorem retains their exact body
identities and physical Euclidean height. Its sole external argument is the
existing ordinary nested-band result, universally quantified over presentations
of those same sets; it does not assume that any presentation exists.
-/

set_option autoImplicit false

open Set
open MergedNormalPrismatoid

namespace PolygonSetReconstruction

/-- Removing a hull-redundant generator preserves the original hull. -/
theorem hull_erase_eq {S : Finset Plane} {p : Plane}
    (hp : p ∈ convexHull ℝ (↑(S.erase p) : Set Plane)) :
    convexHull ℝ (↑(S.erase p) : Set Plane) = convexHull ℝ (↑S : Set Plane) := by
  classical
  apply Subset.antisymm
  · exact convexHull_mono (by simpa using S.erase_subset p)
  · apply convexHull_min _ (convex_convexHull ℝ _)
    intro q hq
    by_cases hqp : q = p
    · simpa [hqp] using hp
    · exact subset_convexHull ℝ _ (Finset.mem_erase.mpr ⟨hqp, hq⟩)

/-- Every finite cloud has a minimum-cardinality generating subset, and every
retained generator is outside the hull of the others. No interior assumption
or boundary order is needed for this stage. -/
theorem exists_minimal_generators (S : Finset Plane) :
    ∃ T : Finset Plane, T ⊆ S ∧
      convexHull ℝ (↑T : Set Plane) = convexHull ℝ (↑S : Set Plane) ∧
      (∀ U : Finset Plane, U ⊆ S →
        convexHull ℝ (↑U : Set Plane) = convexHull ℝ (↑S : Set Plane) →
        T.card ≤ U.card) ∧
      ∀ p ∈ T, p ∉ convexHull ℝ (↑(T.erase p) : Set Plane) := by
  classical
  let Q : ℕ → Prop := fun n => ∃ T : Finset Plane, T ⊆ S ∧
    convexHull ℝ (↑T : Set Plane) = convexHull ℝ (↑S : Set Plane) ∧ T.card = n
  have hex : ∃ n, Q n := ⟨S.card, S, Finset.Subset.refl _, rfl, rfl⟩
  obtain ⟨T, hTS, hHull, hcard⟩ := Nat.find_spec hex
  have hmin : ∀ U : Finset Plane, U ⊆ S →
      convexHull ℝ (↑U : Set Plane) = convexHull ℝ (↑S : Set Plane) →
      T.card ≤ U.card := by
    intro U hUS hU
    rw [hcard]
    exact Nat.find_min' hex ⟨U, hUS, hU, rfl⟩
  refine ⟨T, hTS, hHull, hmin, ?_⟩
  intro p hp hred
  have hsmall := hmin (T.erase p) ((T.erase_subset p).trans hTS)
    ((hull_erase_eq hred).trans hHull)
  have hlt := Finset.card_erase_lt_of_mem hp
  omega

/-- Strict separation at each retained generator, derived from pruning. -/
theorem exists_strict_separator {T : Finset Plane}
    (hirr : ∀ p ∈ T, p ∉ convexHull ℝ (↑(T.erase p) : Set Plane))
    {p : Plane} (hp : p ∈ T) :
    ∃ f : Plane →L[ℝ] ℝ, ∀ q ∈ T, q ≠ p → 0 < f (q - p) := by
  classical
  obtain ⟨f, c, hpc, hc⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ (↑(T.erase p) : Set Plane))
    ((T.erase p).finite_toSet.isClosed_convexHull ℝ) (hirr p hp)
  refine ⟨f, ?_⟩
  intro q hq hqp
  have hqc := hc q (subset_convexHull ℝ _ (Finset.mem_erase.mpr ⟨hqp, hq⟩))
  rw [map_sub]
  linarith

/-- Combined unconditional pruning and local separation for the original cloud. -/
theorem exists_separated_generators (S : Finset Plane) :
    ∃ T : Finset Plane, T ⊆ S ∧
      convexHull ℝ (↑T : Set Plane) = convexHull ℝ (↑S : Set Plane) ∧
      (∀ p ∈ T, p ∉ convexHull ℝ (↑(T.erase p) : Set Plane)) ∧
      ∀ p ∈ T, ∃ f : Plane →L[ℝ] ℝ,
        ∀ q ∈ T, q ≠ p → 0 < f (q - p) := by
  obtain ⟨T, hTS, hHull, _, hirr⟩ := exists_minimal_generators S
  exact ⟨T, hTS, hHull, hirr, fun _ hp => exists_strict_separator hirr hp⟩

open PolygonSupportCompleteness

/-- The ratio comparison identity in the existing determinant convention. -/
lemma ratio_identity (w d z : Plane) :
    inner ℝ w d * det w z - det w d * inner ℝ w z =
      inner ℝ w w * det d z := by
  simp [inner, Fin.sum_univ_two, det]
  ring

/-- An inward separator gives a clockwise weak supporting edge by maximizing
its transverse-to-longitudinal ratio. -/
theorem exists_support_maximizer {T : Finset Plane} {p : Plane}
    (hne : (T.erase p).Nonempty) (w : Plane)
    (hw : ∀ q ∈ T, q ≠ p → 0 < inner ℝ w (q - p)) :
    ∃ q ∈ T, q ≠ p ∧ ∀ r ∈ T, det (q - p) (r - p) ≤ 0 := by
  classical
  obtain ⟨q, hq, hmax⟩ := (T.erase p).exists_max_image
    (fun r => det w (r - p) / inner ℝ w (r - p)) hne
  obtain ⟨hqp, hqT⟩ := Finset.mem_erase.mp hq
  have hqpos := hw q hqT hqp
  have hwnz : w ≠ 0 := by
    intro hz
    simp [hz] at hqpos
  have hww : 0 < inner ℝ w w := real_inner_self_pos.mpr hwnz
  refine ⟨q, hqT, hqp, ?_⟩
  intro r hr
  by_cases hrp : r = p
  · simp [hrp, det]
  have hrpos := hw r hr hrp
  have hratio := (div_le_div_iff₀ hrpos hqpos).mp
    (hmax r (Finset.mem_erase.mpr ⟨hrp, hr⟩))
  have hid := ratio_identity w (q - p) (r - p)
  nlinarith

/-- Equal transverse ratios with positive longitudinal coordinates place the
nearer point in the segment from the origin point to the farther point. -/
lemma mem_segment_of_det_zero (p q r w : Plane)
    (hq : 0 < inner ℝ w (q - p)) (hr : 0 < inner ℝ w (r - p))
    (hle : inner ℝ w (q - p) ≤ inner ℝ w (r - p))
    (hd : det (q - p) (r - p) = 0) : q ∈ segment ℝ p r := by
  let a := inner ℝ w (q - p)
  let b := inner ℝ w (r - p)
  have hb : b ≠ 0 := ne_of_gt hr
  have heq : b • (q - p) = a • (r - p) := by
    ext i
    fin_cases i
    · change inner ℝ w (r - p) * (q 0 - p 0) =
        inner ℝ w (q - p) * (r 0 - p 0)
      simp [inner, Fin.sum_univ_two, det] at hd ⊢
      linear_combination (w 1) * hd
    · change inner ℝ w (r - p) * (q 1 - p 1) =
        inner ℝ w (q - p) * (r 1 - p 1)
      simp [inner, Fin.sum_univ_two, det] at hd ⊢
      linear_combination -(w 0) * hd
  have hrepr : q = (1 - a / b) • p + (a / b) • r := by
    have hh : q - p = (a / b) • (r - p) := by
      calc
        q - p = b⁻¹ • (b • (q - p)) := by simp [smul_smul, hb]
        _ = b⁻¹ • (a • (r - p)) := by rw [heq]
        _ = (a / b) • (r - p) := by rw [smul_smul]; congr 1; ring
    rw [smul_sub] at hh
    rw [sub_smul, one_smul]
    calc
      q = (q - p) + p := by abel
      _ = (a / b) • r - (a / b) • p + p := by rw [hh]
      _ = p - (a / b) • p + (a / b) • r := by abel
  rw [segment_eq_image]
  exact ⟨a / b, ⟨(div_nonneg hq.le hr.le), (div_le_one hr).mpr hle⟩, hrepr.symm⟩

/-- Irredundance makes every other generator lie strictly on the supported side.
This is local geometric strictness, not an assumed boundary ordering. -/
theorem strict_of_support {T : Finset Plane}
    (hirr : ∀ p ∈ T, p ∉ convexHull ℝ (↑(T.erase p) : Set Plane))
    {p q : Plane} (hp : p ∈ T) (hq : q ∈ T) (hqp : q ≠ p)
    (w : Plane) (hw : ∀ r ∈ T, r ≠ p → 0 < inner ℝ w (r - p))
    (hs : ∀ r ∈ T, det (q - p) (r - p) ≤ 0) :
    ∀ r ∈ T, r ≠ p → r ≠ q → det (q - p) (r - p) < 0 := by
  classical
  intro r hr hrp hrq
  apply lt_of_le_of_ne (hs r hr)
  intro hd
  have hqpos := hw q hq hqp
  have hrpos := hw r hr hrp
  rcases le_total (inner ℝ w (q - p)) (inner ℝ w (r - p)) with hle | hle
  · apply hirr q hq
    exact (convex_convexHull ℝ (↑(T.erase q) : Set Plane)).segment_subset
      (subset_convexHull ℝ _ (Finset.mem_erase.mpr ⟨hqp.symm, hp⟩))
      (subset_convexHull ℝ _ (Finset.mem_erase.mpr ⟨hrq, hr⟩))
      (mem_segment_of_det_zero p q r w hqpos hrpos hle hd)
  · apply hirr r hr
    have hd' : det (r - p) (q - p) = 0 := by rw [det_swap, hd]; ring
    exact (convex_convexHull ℝ (↑(T.erase r) : Set Plane)).segment_subset
      (subset_convexHull ℝ _ (Finset.mem_erase.mpr ⟨hrp.symm, hp⟩))
      (subset_convexHull ℝ _ (Finset.mem_erase.mpr ⟨hrq.symm, hq⟩))
      (mem_segment_of_det_zero p r q w hrpos hqpos hle hd')

/-- Strict clockwise support successor at a retained point. -/
theorem exists_strict_support_successor {T : Finset Plane}
    (hirr : ∀ p ∈ T, p ∉ convexHull ℝ (↑(T.erase p) : Set Plane))
    {p : Plane} (hp : p ∈ T) (hne : (T.erase p).Nonempty) :
    ∃ q ∈ T, q ≠ p ∧
      (∀ r ∈ T, det (q - p) (r - p) ≤ 0) ∧
      ∀ r ∈ T, r ≠ p → r ≠ q → det (q - p) (r - p) < 0 := by
  obtain ⟨f, hf⟩ := exists_strict_separator hirr hp
  let w := (InnerProductSpace.toDual ℝ Plane).symm f
  have hw : ∀ r ∈ T, r ≠ p → 0 < inner ℝ w (r - p) := by
    intro r hr hrp
    simpa [w, InnerProductSpace.toDual_symm_apply] using hf r hr hrp
  obtain ⟨q, hq, hqp, hs⟩ := exists_support_maximizer hne w hw
  exact ⟨q, hq, hqp, hs, strict_of_support hirr hp hq hqp w hw hs⟩

/-- Full planar interior rules out zero, one and two generators. -/
theorem three_le_card_of_interior {S : Finset Plane}
    (hS : (interior (convexHull ℝ (↑S : Set Plane))).Nonempty) : 3 ≤ S.card := by
  classical
  have hspan := affineSpan_eq_top_of_nonempty_interior hS
  by_contra hn
  have hcard : S.card ≤ 2 := by omega
  have hdim : Module.finrank ℝ Plane = 2 := by simp [Plane]
  have he : (↑S : Set Plane).encard ≤ Module.finrank ℝ Plane := by
    rw [hdim, Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast hcard
  have hnot := affineSpan_image_ne_top_of_encard_le_finrank ℝ S.finite_toSet he
    (id : Plane → Plane)
  apply hnot
  simpa using hspan

/-- A finite self-map has a periodic point without any injectivity assumption. -/
theorem exists_periodic_point {α : Type*} [Finite α] [Nonempty α] (N : α → α) :
    ∃ x, x ∈ Function.periodicPts N := by
  classical
  let a : α := Classical.arbitrary α
  obtain ⟨m, n, heq, hne⟩ : ∃ m n, N^[m] a = N^[n] a ∧ m ≠ n := by
    simpa [Function.Injective] using not_injective_infinite_finite (N^[·] a)
  have aux : ∀ m n : ℕ, m < n → N^[m] a = N^[n] a →
      ∃ x, x ∈ Function.periodicPts N := by
    intro m n hmn heq
    refine ⟨N^[m] a, Function.mk_mem_periodicPts (by omega : 0 < n - m) ?_⟩
    change N^[n - m] (N^[m] a) = N^[m] a
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hmn.le]
    exact heq.symm
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact aux m n hlt heq
  · exact aux n m hlt heq.symm

/-- Extract a simple cyclic orbit, excluding periods one and two locally. -/
theorem exists_simple_cycle {α : Type*} [Finite α] [Nonempty α] (N : α → α)
    (hfix : ∀ x, N x ≠ x) (htwo : ∀ x, N (N x) ≠ x) :
    ∃ k : ℕ, ∃ hk : NeZero k, ∃ v : Fin k → α,
      3 ≤ k ∧ Function.Injective v ∧ ∀ i, v (next i) = N (v i) := by
  obtain ⟨x, hx⟩ := exists_periodic_point N
  let k := Function.minimalPeriod N x
  have hkpos : 0 < k := Function.minimalPeriod_pos_of_mem_periodicPts hx
  have hperiod : N^[k] x = x := Function.iterate_minimalPeriod
  have hk1 : k ≠ 1 := by
    intro hk
    apply hfix x
    simpa [hk] using hperiod
  have hk2 : k ≠ 2 := by
    intro hk
    apply htwo x
    simpa [hk, Function.iterate_succ_apply'] using hperiod
  letI : NeZero k := ⟨by omega⟩
  refine ⟨k, inferInstance, (fun i => N^[i.val] x), (by omega), ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    exact Function.iterate_injOn_Iio_minimalPeriod i.isLt j.isLt hij
  · intro i
    change N^[(i.val + 1) % k] x = N (N^[i.val] x)
    rw [Function.iterate_mod_minimalPeriod_eq, Function.iterate_succ_apply']

/-- Internally obtain a simple supporting cycle from a pruned cloud. It is not
assumed to visit all generators; halfspace completeness will supply hull equality. -/
theorem exists_supporting_cycle {T : Finset Plane} (hcard : 3 ≤ T.card)
    (hirr : ∀ p ∈ T, p ∉ convexHull ℝ (↑(T.erase p) : Set Plane)) :
    ∃ k : ℕ, ∃ hk : NeZero k, ∃ v : Fin k → Plane,
      3 ≤ k ∧ Function.Injective v ∧ (∀ i, v i ∈ T) ∧
      (∀ i r, r ∈ T → det (v (next i) - v i) (r - v i) ≤ 0) ∧
      ∀ i r, r ∈ T → r ≠ v i → r ≠ v (next i) →
        det (v (next i) - v i) (r - v i) < 0 := by
  classical
  have hex : ∀ p : T, ∃ q : T, q ≠ p ∧
      (∀ r ∈ T, det (q.val - p.val) (r - p.val) ≤ 0) ∧
      ∀ r ∈ T, r ≠ p.val → r ≠ q.val → det (q.val - p.val) (r - p.val) < 0 := by
    intro p
    have hne : (T.erase p.val).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem p.property]
      omega
    obtain ⟨q, hq, hqp, hs, hstrict⟩ := exists_strict_support_successor hirr p.property hne
    exact ⟨⟨q, hq⟩, (fun h => hqp (congrArg Subtype.val h)), hs, hstrict⟩
  choose N hN using hex
  have htwo : ∀ p, N (N p) ≠ p := by
    intro p htwo
    have hq : (N p).val ∈ T.erase p.val :=
      Finset.mem_erase.mpr ⟨(fun h => (hN p).1 (Subtype.ext h)), (N p).property⟩
    have hrne : ((T.erase p.val).erase (N p).val).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem hq, Finset.card_erase_of_mem p.property]
      omega
    obtain ⟨r, hr⟩ := hrne
    obtain ⟨hrq, hr⟩ := Finset.mem_erase.mp hr
    obtain ⟨hrp, hr⟩ := Finset.mem_erase.mp hr
    have h1 := (hN p).2.2 r hr hrp hrq
    have h2 := (hN (N p)).2.2 r hr hrq (by simpa [htwo] using hrp)
    rw [htwo] at h2
    have hid : det (p.val - (N p).val) (r - (N p).val) =
        -det ((N p).val - p.val) (r - p.val) := by
      simp [det]; ring
    rw [hid] at h2
    linarith
  have hnonempty : T.Nonempty := Finset.card_pos.mp (by omega)
  letI : Nonempty T := ⟨⟨hnonempty.choose, hnonempty.choose_spec⟩⟩
  obtain ⟨k, hk, v, hk3, hvinj, hnext⟩ := exists_simple_cycle N (fun p => (hN p).1) htwo
  letI : NeZero k := hk
  refine ⟨k, hk, (fun i => (v i).val), hk3,
    (fun i j hij => hvinj (Subtype.ext hij)), (fun i => (v i).property), ?_, ?_⟩
  · intro i r hr
    dsimp only
    rw [hnext]
    exact (hN (v i)).2.1 r hr
  · intro i r hr hrp hrq
    dsimp only at hrq ⊢
    rw [hnext] at hrq ⊢
    exact (hN (v i)).2.2 r hr hrp hrq

/-- Unordered arbitrary finite real generators with nonempty hull interior
produce the unchanged raw polygon, with exact equality to the original hull. -/
theorem exists_reduced_polygon_of_finite_hull (S : Finset Plane)
    (hS : (interior (convexHull ℝ (↑S : Set Plane))).Nonempty) :
    ∃ k : ℕ, ∃ hk : NeZero k, ∃ P : ReducedConvexPolygon k,
      P.body = convexHull ℝ (↑S : Set Plane) ∧ range P.vertex ⊆ (↑S : Set Plane) := by
  classical
  obtain ⟨T, hTS, hHull, _, hirr⟩ := exists_minimal_generators S
  have hT : (interior (convexHull ℝ (↑T : Set Plane))).Nonempty := by rwa [hHull]
  obtain ⟨k, hk, v, hk3, hinj, hvT, hs, hstrict⟩ :=
    exists_supporting_cycle (three_le_card_of_interior hT) hirr
  letI : NeZero k := hk
  have hnextne : ∀ i : Fin k, next i ≠ i := next_ne (by omega)
  let P : ReducedConvexPolygon k := {
    vertex := v
    three_le := hk3
    edge_ne := fun i h => hnextne i (hinj h)
    supports := by
      intro i j
      change inner ℝ (rotateCW (v (next i) - v i)) (v j - v i) ≤ 0
      rw [inner_rotate]
      exact hs i (v j) (hvT j)
    support_eq_vertices := by
      intro i j heq
      by_contra hn
      have hji : j ≠ i := fun h => hn (Or.inl h)
      have hjn : j ≠ next i := fun h => hn (Or.inr h)
      have hlt := hstrict i (v j) (hvT j) (fun h => hji (hinj h))
        (fun h => hjn (hinj h))
      change inner ℝ (rotateCW (v (next i) - v i)) (v j - v i) = 0 at heq
      rw [inner_rotate] at heq
      linarith }
  have hvsub : range P.vertex ⊆ (↑T : Set Plane) := by
    rintro _ ⟨i, rfl⟩
    exact hvT i
  have heq : P.body = convexHull ℝ (↑T : Set Plane) := by
    apply Subset.antisymm (convexHull_mono hvsub)
    intro x hx
    apply PolygonSupportCompleteness.ReducedConvexPolygon.mem_body_of_edgeRows P
    intro i
    have hsub : (↑T : Set Plane) ⊆
        {y | P.edgeLinear i y ≤ P.edgeLinear i (P.vertex i)} := by
      intro r hr
      have hh := hs i r hr
      change det (P.vertex (next i) - P.vertex i) (r - P.vertex i) ≤ 0 at hh
      rw [← inner_rotate] at hh
      simpa [ReducedConvexPolygon.edgeLinear, outwardNormal, edgeVector,
        inner_sub_right] using hh
    have hh := convexHull_min hsub
      (convex_halfSpace_le (P.edgeLinear i).toLinearMap.isLinear _) hx
    change P.edgeLinear i x - P.edgeLinear i (P.vertex i) ≤ 0
    exact sub_nonpos.mpr hh
  exact ⟨k, hk, P, heq.trans hHull, hvsub.trans hTS⟩

/-- A raw presentation is an output package, never an ordinary-set input. -/
structure RawPresentation (K : Set Plane) where
  size : ℕ
  size_nezero : NeZero size
  polygon : @ReducedConvexPolygon size size_nezero
  body_eq : polygon.body = K

attribute [instance] RawPresentation.size_nezero

/-- Set-level reconstruction from a finite generating set and nonempty interior. -/
theorem exists_reduced_polygon_of_polygon_set (K : Set Plane)
    (hfin : ∃ S : Finset Plane, convexHull ℝ (↑S : Set Plane) = K)
    (hint : (interior K).Nonempty) : Nonempty (RawPresentation K) := by
  obtain ⟨S, hS⟩ := hfin
  obtain ⟨k, hk, P, hP, _⟩ := exists_reduced_polygon_of_finite_hull S (by rwa [hS])
  exact ⟨⟨k, hk, P, hP.trans hS⟩⟩

open EuclideanPrismatoidCoordinates CommonSupportMerge NestedBandExternalApplication CyclicCutOrders

/-- Independent physical convex hull of the original sets, in the existing
Euclidean coordinates at physical heights zero and h. -/
def physicalBodyOfSets (KA KB : Set Plane) (h : ℝ) : Set PhysicalAmbient :=
  convexHull ℝ ((fun x => pack (lowerLift x)) '' KB ∪
    (fun x => pack (upperLift h x)) '' KA)

/-- Exact body equality, with no rescaling or metric replacement. -/
theorem physicalBodyOfSets_eq {KA KB : Set Plane}
    (PA : RawPresentation KA) (PB : RawPresentation KB) (h : ℝ) :
    physicalBodyOfSets KA KB h = physicalPrismatoid PA.polygon PB.polygon h := by
  simp only [physicalBodyOfSets, physicalPrismatoid, PA.body_eq, PB.body_eq]

/-- The one external ordinary nested-band premise, universally quantified only
over presentations of these same original sets. It asserts no presentation exists. -/
def ExternalNestedBandForSets (KA KB : Set Plane) {h : ℝ} (hh : 0 < h) : Prop :=
  ∀ (PA : RawPresentation KA) (PB : RawPresentation KB),
    ExternalNestedBandTheorem PA.polygon PB.polygon hh Plane

/-- Ordinary finite-hull sets reach the existing continuous cut-surface package.
Boundary order, pruning, successor, cycle, and raw polygons are all constructed
internally. The single ordinary external nested-band theorem remains explicit. -/
theorem exists_cut_surface_for_polygon_sets (KA KB : Set Plane)
    (hfinA : ∃ S : Finset Plane, convexHull ℝ (↑S : Set Plane) = KA)
    (hfinB : ∃ S : Finset Plane, convexHull ℝ (↑S : Set Plane) = KB)
    (hintA : (interior KA).Nonempty) (hintB : (interior KB).Nonempty)
    (hNest : KA ⊆ interior KB) {h : ℝ} (hh : 0 < h)
    (hExternal : ExternalNestedBandForSets KA KB hh) :
    ∃ (PA : RawPresentation KA) (PB : RawPresentation KB),
      PA.polygon.body = KA ∧ PB.polygon.body = KB ∧
      physicalBodyOfSets KA KB h = physicalPrismatoid PA.polygon PB.polygon h ∧
      ∃ e : Fin (sideCount PA.polygon PB.polygon),
        Nonempty (CutSurfaceQuotient.CutSurfaceDevelopment PA.polygon PB.polygon hh Plane e) := by
  obtain ⟨PA⟩ := exists_reduced_polygon_of_polygon_set KA hfinA hintA
  obtain ⟨PB⟩ := exists_reduced_polygon_of_polygon_set KB hfinB hintB
  refine ⟨PA, PB, PA.body_eq, PB.body_eq, physicalBodyOfSets_eq PA PB h, ?_⟩
  exact CutSurfaceQuotient.exists_continuous_cut_surface_unfolding_from_external_nested_band
    PA.polygon PB.polygon hh Plane (by simpa only [PA.body_eq, PB.body_eq] using hNest)
    (hExternal PA PB) (by simp [Plane])

end PolygonSetReconstruction

#check @PolygonSetReconstruction.exists_strict_support_successor
#print axioms PolygonSetReconstruction.exists_strict_support_successor
#check @PolygonSetReconstruction.exists_minimal_generators
#print axioms PolygonSetReconstruction.exists_minimal_generators
#check @PolygonSetReconstruction.exists_separated_generators
#print axioms PolygonSetReconstruction.exists_separated_generators
#check @PolygonSetReconstruction.three_le_card_of_interior
#print axioms PolygonSetReconstruction.three_le_card_of_interior
#check @PolygonSetReconstruction.exists_simple_cycle
#print axioms PolygonSetReconstruction.exists_simple_cycle
#check @PolygonSetReconstruction.exists_supporting_cycle
#print axioms PolygonSetReconstruction.exists_supporting_cycle
#check @PolygonSetReconstruction.exists_reduced_polygon_of_finite_hull
#print axioms PolygonSetReconstruction.exists_reduced_polygon_of_finite_hull
#check @PolygonSetReconstruction.exists_reduced_polygon_of_polygon_set
#print axioms PolygonSetReconstruction.exists_reduced_polygon_of_polygon_set
#check @PolygonSetReconstruction.physicalBodyOfSets_eq
#print axioms PolygonSetReconstruction.physicalBodyOfSets_eq
#print PolygonSetReconstruction.ExternalNestedBandForSets
#print NestedBandExternalApplication.ExternalNestedBandTheorem
#check @PolygonSetReconstruction.exists_cut_surface_for_polygon_sets
#print axioms PolygonSetReconstruction.exists_cut_surface_for_polygon_sets
