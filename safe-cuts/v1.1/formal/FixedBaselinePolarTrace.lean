import FixedBaselinePolarRayGeometry
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open Set
open scoped BigOperators Classical NNReal
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CommonSupportMerge OriginalFacetCertificates NormalFanSplice MaximalSupportCells
open CyclicCutOrders EuclideanPrismatoidCoordinates PolyhedralInputBridge
open TrimmedFacetWitnesses BandGeometryAssembly FiniteWitnessClosure SingleCutRecovery
open CutSurfaceQuotient MixedTurnSafeCut PolygonSetReconstruction ConvexPolygonTurning

namespace FixedBaselinePolarTrace
noncomputable section
set_option maxHeartbeats 8000000

abbrev Plane := MixedTurnSafeCut.Plane

/-- The two literal half-plane branches used by the principal polar argument.
Unlike a heading label, a branch is selected from the coordinates of the
material point itself. -/
inductive HalfPlaneBranch
  | upper
  | lower
  deriving DecidableEq

/-- The explicit branch test.  The boundary belongs to the lower branch, so
there is no omitted radial or branch-cut case. -/
def InHalfPlane (b : HalfPlaneBranch) (z : Plane) : Prop :=
  match b with
  | .upper => 0 < z 1
  | .lower => z 1 ≤ 0

/-- Coordinate identification used only to invoke the genuine complex
principal argument. -/
def planeComplex (z : Plane) : ℂ := ⟨z 0, z 1⟩

/-- Principal polar radius of an actual developed point. -/
def polarRadius (O x : Plane) : ℝ := ‖planeComplex (x - O)‖

/-- The complex-coordinate radius is the ordinary Euclidean radius. -/
@[simp] theorem polarRadius_eq_norm (O x : Plane) :
    polarRadius O x = ‖x - O‖ := by
  simp only [polarRadius, planeComplex, Complex.norm_def, Complex.normSq_apply,
    EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  congr 1
  ring

/-- Principal polar argument of an actual developed point. -/
def polarAngle (O x : Plane) : ℝ := Complex.arg (planeComplex (x - O))

/-- The half-plane branch is computed from the actual point, not supplied by a
caller. -/
def halfPlaneBranch (O x : Plane) : HalfPlaneBranch :=
  if 0 < (x - O) 1 then .upper else .lower

lemma halfPlaneBranch_spec (O x : Plane) :
    InHalfPlane (halfPlaneBranch O x) (x - O) := by
  unfold halfPlaneBranch
  split_ifs with h
  · exact h
  · exact le_of_not_gt h

lemma planeComplex_ne_zero {z : Plane} (hz : z ≠ 0) : planeComplex z ≠ 0 := by
  intro h
  apply hz
  ext i
  fin_cases i
  · exact congrArg Complex.re h
  · exact congrArg Complex.im h

/-- Every non-pole point has a genuine positive-radius polar representation.
The angle is `Complex.arg` of the point itself. -/
theorem polar_decomposition {O x : Plane} (hx : x ≠ O) :
    0 < polarRadius O x ∧
      x - O = polarRadius O x • MixedTurnSafeCut.direction (polarAngle O x) := by
  have hz : planeComplex (x - O) ≠ 0 := by
    apply planeComplex_ne_zero
    exact sub_ne_zero.mpr hx
  constructor
  · exact norm_pos_iff.mpr hz
  · ext i
    fin_cases i
    · simpa [polarRadius, polarAngle, planeComplex, MixedTurnSafeCut.direction]
        using (Complex.norm_mul_cos_arg (planeComplex (x - O))).symm
    · simpa [polarRadius, polarAngle, planeComplex, MixedTurnSafeCut.direction]
        using (Complex.norm_mul_sin_arg (planeComplex (x - O))).symm

section Strip

variable {n : ℕ} (S : RadialExtremalSafety.TriangularRadialStrip n) (O : Plane)

/-- Genuine polar trace of every material point of every RF-supported panel.
It contains the computed half-plane branch, positive norm radius, principal
argument, and exact ray equation. -/
theorem material_point_polar
    (hR : S.RadialSupport O) {i : ℕ} (hi : i ≤ n)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    InHalfPlane (halfPlaneBranch O (S.point i s t)) (S.point i s t - O) ∧
      0 < polarRadius O (S.point i s t) ∧
      S.point i s t - O =
        polarRadius O (S.point i s t) •
          MixedTurnSafeCut.direction (polarAngle O (S.point i s t)) := by
  refine ⟨halfPlaneBranch_spec O _, ?_⟩
  exact polar_decomposition
    (RadialExtremalSafety.TriangularRadialStrip.point_ne_pole hR hi hs ht)

/-- Pointwise compatibility at every retained hinge of the abstract strip.
This identity does not divide by either rim coefficient and therefore includes
zero-length rim runs. -/
theorem point_exit_eq_next_entry {i : ℕ} (hi : i < n) (t : ℝ) :
    S.point i 1 t = S.point (i + 1) 0 t := by
  rw [RadialExtremalSafety.TriangularRadialStrip.point,
    RadialExtremalSafety.TriangularRadialStrip.point,
    S.lower_step i hi, S.hinge_step i hi]
  module

/-- Consequently radius, principal angle, and explicit branch agree at a
retained hinge. -/
theorem polar_compatible_at_hinge {i : ℕ} (hi : i < n) (t : ℝ) :
    polarRadius O (S.point i 1 t) = polarRadius O (S.point (i + 1) 0 t) ∧
      polarAngle O (S.point i 1 t) = polarAngle O (S.point (i + 1) 0 t) ∧
      halfPlaneBranch O (S.point i 1 t) =
        halfPlaneBranch O (S.point (i + 1) 0 t) := by
  rw [point_exit_eq_next_entry S hi t]
  exact ⟨rfl, rfl, rfl⟩

/-- Physical orientation makes the upper endpoint determinant strictly larger
than the lower endpoint determinant. -/
lemma endpoint_det_lt {i : ℕ} (hi : i ≤ n) :
    MixedTurnSafeCut.det (S.B i - O) (S.v i) <
      MixedTurnSafeCut.det (S.B i + S.d i - O) (S.v i) := by
  have ho := S.orientation_neg i hi
  have he : MixedTurnSafeCut.det (S.B i + S.d i - O) (S.v i) =
      MixedTurnSafeCut.det (S.B i - O) (S.v i) -
        MixedTurnSafeCut.det (S.v i) (S.d i) := by
    simp [MixedTurnSafeCut.det]
    ring
  rw [he]
  linarith

/-- Along every eligible fixed ray, height is strictly radially inward.  This
is the orientation-correct counterpart of the outward ordering lemma in the
prerequisite module. -/
theorem ray_radius_strictAnti
    (hR : S.RadialSupport O) {α : ℝ} {i : ℕ} (hi : i ≤ n)
    {s₁ s₂ t₁ t₂ r₁ r₂ : ℝ} (ht : t₁ < t₂)
    (h₁ : FixedBaselinePolarRayGeometry.RayHit S O α i s₁ t₁ r₁)
    (h₂ : FixedBaselinePolarRayGeometry.RayHit S O α i s₂ t₂ r₂) :
    r₂ < r₁ := by
  let d := MixedTurnSafeCut.det (MixedTurnSafeCut.direction α) (S.v i)
  let a := MixedTurnSafeCut.det (S.B i - O) (S.v i)
  let b := MixedTurnSafeCut.det (S.B i + S.d i - O) (S.v i)
  have hd : d < 0 := FixedBaselinePolarRayGeometry.ray_denominator_neg S O hR hi h₁
  have hab : a < b := endpoint_det_lt S O hi
  have hn : (1 - t₁) * a + t₁ * b < (1 - t₂) * a + t₂ * b := by
    nlinarith
  have he₁ := FixedBaselinePolarRayGeometry.ray_radius_affine S O h₁
  have he₂ := FixedBaselinePolarRayGeometry.ray_radius_affine S O h₂
  by_contra hnot
  have hle : r₁ ≤ r₂ := le_of_not_gt hnot
  have hp : 0 ≤ (r₁ - r₂) * d :=
    mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hle) hd.le
  dsimp [d, a, b] at he₁ he₂ hp hn
  nlinarith

/-- Complete finite same-sheet fixed-ray ordering.  For every physical panel it
simultaneously records: strict inward order for two eligible heights, unique
radius at a singleton height (including zero horizontal coefficients), and
ineligibility of a parallel ray. -/
theorem finite_sameSheet_fixedRay_order
    (hR : S.RadialSupport O) (α : ℝ) :
    (∀ i : Fin (n + 1), ∀ {s₁ s₂ t₁ t₂ r₁ r₂ : ℝ}, t₁ < t₂ →
      FixedBaselinePolarRayGeometry.RayHit S O α i s₁ t₁ r₁ →
      FixedBaselinePolarRayGeometry.RayHit S O α i s₂ t₂ r₂ → r₂ < r₁) ∧
    (∀ i : Fin (n + 1), ∀ {s₁ s₂ t r₁ r₂ : ℝ},
      FixedBaselinePolarRayGeometry.RayHit S O α i s₁ t r₁ →
      FixedBaselinePolarRayGeometry.RayHit S O α i s₂ t r₂ → r₁ = r₂) ∧
    (∀ i : Fin (n + 1),
      MixedTurnSafeCut.det (MixedTurnSafeCut.direction α) (S.v i) = 0 →
      FixedBaselinePolarRayGeometry.eligibleHeights S O α i = ∅) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i s₁ s₂ t₁ t₂ r₁ r₂ ht h₁ h₂
    exact ray_radius_strictAnti S O hR (by omega) ht h₁ h₂
  · intro i s₁ s₂ t r₁ r₂ h₁ h₂
    exact FixedBaselinePolarRayGeometry.ray_radius_unique S O hR
      (by omega) h₁ h₂
  · intro i hp
    exact FixedBaselinePolarRayGeometry.ineligible_of_parallel S O hR
      (by omega) hp

/-- The transition clause supplementing finite panelwise order: radial hinge
hits from either adjacent panel name the same point and therefore the same
radius.  It applies unchanged to singleton hits and vanishing rim coefficients. -/
theorem fixedRay_transition_radius
    (hR : S.RadialSupport O) {α : ℝ} {i : ℕ} (hi : i < n)
    {t r₁ r₂ : ℝ}
    (h₁ : FixedBaselinePolarRayGeometry.RayHit S O α i 1 t r₁)
    (h₂ : FixedBaselinePolarRayGeometry.RayHit S O α (i + 1) 0 t r₂) :
    r₁ = r₂ := by
  have hp : S.point i 1 t = S.point (i + 1) 0 t := point_exit_eq_next_entry S hi t
  have hleft := h₁.2.2.2
  have hright := h₂.2.2.2
  have he : r₁ • MixedTurnSafeCut.direction α =
      r₂ • MixedTurnSafeCut.direction α := by
    rw [← hleft, ← hright, hp]
  have hd : MixedTurnSafeCut.direction α ≠ 0 := by
    intro hz
    have h0 := congrArg (fun z : Plane => z 0) hz
    have h1 := congrArg (fun z : Plane => z 1) hz
    simp [MixedTurnSafeCut.direction] at h0 h1
    nlinarith [Real.sin_sq_add_cos_sq α]
  exact smul_left_injective ℝ hd he

/-- One global finite trace statement: every indexed panel has strict inward
fixed-ray order, singleton-height uniqueness and the parallel/ineligible case,
while every one of the finitely many transitions identifies radial hinge hits.
No positivity of either rim coefficient is assumed. -/
theorem global_finite_sameSheet_fixedRay_trace
    (hR : S.RadialSupport O) (α : ℝ) :
    ((∀ i : Fin (n + 1), ∀ {s₁ s₂ t₁ t₂ r₁ r₂ : ℝ}, t₁ < t₂ →
        FixedBaselinePolarRayGeometry.RayHit S O α i s₁ t₁ r₁ →
        FixedBaselinePolarRayGeometry.RayHit S O α i s₂ t₂ r₂ → r₂ < r₁) ∧
      (∀ i : Fin (n + 1), ∀ {s₁ s₂ t r₁ r₂ : ℝ},
        FixedBaselinePolarRayGeometry.RayHit S O α i s₁ t r₁ →
        FixedBaselinePolarRayGeometry.RayHit S O α i s₂ t r₂ → r₁ = r₂) ∧
      (∀ i : Fin (n + 1),
        MixedTurnSafeCut.det (MixedTurnSafeCut.direction α) (S.v i) = 0 →
        FixedBaselinePolarRayGeometry.eligibleHeights S O α i = ∅)) ∧
    (∀ i < n, ∀ {t r₁ r₂ : ℝ},
      FixedBaselinePolarRayGeometry.RayHit S O α i 1 t r₁ →
      FixedBaselinePolarRayGeometry.RayHit S O α (i + 1) 0 t r₂ → r₁ = r₂) := by
  refine ⟨finite_sameSheet_fixedRay_order S O hR α, ?_⟩
  intro i hi t r₁ r₂ h₁ h₂
  exact fixedRay_transition_radius S O hR hi h₁ h₂

/-- A panel contributes one height piece to the fixed-lift trace exactly when its
closed eligible-height set is nonempty.  The predicate deliberately does not
choose an endpoint or a witness hit. -/
def HasEligiblePiece (α : ℝ) (i : Fin (n + 1)) : Prop :=
  (FixedBaselinePolarRayGeometry.eligibleHeights S O α i).Nonempty

/-- The canonical finite ordered list of all eligible panel-height pieces.  It
is obtained by filtering `Fin` order, so no caller supplies a trace or a
validity certificate. -/
noncomputable def orderedEligiblePieces (α : ℝ) : List (Fin (n + 1)) :=
  (List.finRange (n + 1)).filter (HasEligiblePiece S O α)

@[simp] theorem mem_orderedEligiblePieces_iff (α : ℝ) (i : Fin (n + 1)) :
    i ∈ orderedEligiblePieces S O α ↔
      (FixedBaselinePolarRayGeometry.eligibleHeights S O α i).Nonempty := by
  rw [orderedEligiblePieces, List.mem_filter]
  constructor
  · rintro ⟨_, h⟩
    exact of_decide_eq_true h
  · intro h
    exact ⟨List.mem_finRange i, decide_eq_true h⟩

/-- Exact omission criterion for the canonical list. -/
theorem not_mem_orderedEligiblePieces_iff (α : ℝ) (i : Fin (n + 1)) :
    i ∉ orderedEligiblePieces S O α ↔
      FixedBaselinePolarRayGeometry.eligibleHeights S O α i = ∅ := by
  rw [mem_orderedEligiblePieces_iff]
  constructor
  · intro h
    apply Set.not_nonempty_iff_eq_empty.mp
    exact h
  · intro h hn
    rw [h] at hn
    exact Set.not_nonempty_empty hn

/-- Every omission is classified without a generic-position assumption: the
panel direction is parallel to the lifted ray, or it is nonparallel and the
closed panel simply misses that positive ray. -/
theorem orderedEligiblePieces_omission_classification
    (hR : S.RadialSupport O) (α : ℝ) (i : Fin (n + 1)) :
    i ∉ orderedEligiblePieces S O α ↔
      MixedTurnSafeCut.det (MixedTurnSafeCut.direction α) (S.v i) = 0 ∨
      (MixedTurnSafeCut.det (MixedTurnSafeCut.direction α) (S.v i) ≠ 0 ∧
        FixedBaselinePolarRayGeometry.eligibleHeights S O α i = ∅) := by
  constructor
  · intro homit
    have hempty := (not_mem_orderedEligiblePieces_iff S O α i).mp homit
    by_cases hp : MixedTurnSafeCut.det (MixedTurnSafeCut.direction α) (S.v i) = 0
    · exact Or.inl hp
    · exact Or.inr ⟨hp, hempty⟩
  · rintro (hp | ⟨_, hempty⟩)
    · apply (not_mem_orderedEligiblePieces_iff S O α i).2
      exact FixedBaselinePolarRayGeometry.ineligible_of_parallel S O hR
        (by omega) hp
    · exact (not_mem_orderedEligiblePieces_iff S O α i).2 hempty

/-- A singleton eligible interval is retained rather than discarded. -/
theorem singleton_piece_mem (α : ℝ) (i : Fin (n + 1)) {t : ℝ}
    (hsingle : FixedBaselinePolarRayGeometry.eligibleHeights S O α i = {t}) :
    i ∈ orderedEligiblePieces S O α := by
  rw [mem_orderedEligiblePieces_iff, hsingle]
  exact ⟨t, Set.mem_singleton t⟩

/-- Any actual hit retains its panel, independently of zero lower or upper run
coefficients. -/
theorem hit_piece_mem (α : ℝ) (i : Fin (n + 1)) {s t r : ℝ}
    (hit : FixedBaselinePolarRayGeometry.RayHit S O α i s t r) :
    i ∈ orderedEligiblePieces S O α := by
  rw [mem_orderedEligiblePieces_iff]
  exact ⟨t, s, r, hit⟩

/-- A radial retained hinge puts both adjacent pieces in the canonical list and
identifies their actual hinge point and radius.  This is the adjacency link;
no division by either horizontal coefficient occurs. -/
theorem radialHinge_connects_adjacent_pieces
    (hR : S.RadialSupport O) {α : ℝ} {i : ℕ} (hi : i < n)
    {t r₁ r₂ : ℝ}
    (h₁ : FixedBaselinePolarRayGeometry.RayHit S O α i 1 t r₁)
    (h₂ : FixedBaselinePolarRayGeometry.RayHit S O α (i + 1) 0 t r₂) :
    (⟨i, by omega⟩ : Fin (n + 1)) ∈ orderedEligiblePieces S O α ∧
      (⟨i + 1, by omega⟩ : Fin (n + 1)) ∈ orderedEligiblePieces S O α ∧
      S.point i 1 t = S.point (i + 1) 0 t ∧ r₁ = r₂ := by
  refine ⟨hit_piece_mem S O α ⟨i, by omega⟩ h₁,
    hit_piece_mem S O α ⟨i + 1, by omega⟩ h₂,
    point_exit_eq_next_entry S hi t, ?_⟩
  exact fixedRay_transition_radius S O hR hi h₁ h₂

end Strip

section ConnectedFiniteTrace

/-- Radius cannot increase while crossing a finite connected list of closed
height pieces.  Consecutive pieces meet at the literal cut height `c (i+1)`;
singletons (`c i = c (i+1)`) are allowed. -/
theorem finite_connected_piece_radius_anti
    (m : ℕ) (c : ℕ → ℝ) (R : ℕ → ℝ → ℝ)
    (hc : Monotone c)
    (hanti : ∀ i ≤ m, StrictAntiOn (R i) (Icc (c i) (c (i + 1))))
    (hglue : ∀ i < m, R i (c (i + 1)) = R (i + 1) (c (i + 1)))
    {i j : ℕ} (hi : i ≤ m) (hj : j ≤ m) (hij : i ≤ j)
    {t u : ℝ} (ht : t ∈ Icc (c i) (c (i + 1)))
    (hu : u ∈ Icc (c j) (c (j + 1))) (htu : t ≤ u) :
    R j u ≤ R i t := by
  induction j, hij using Nat.le_induction generalizing u with
  | base =>
      exact (hanti i hi).antitoneOn ht hu htu
  | @succ j hij ih =>
      have hjm : j ≤ m := by omega
      have hjlt : j < m := by omega
      have hleft : c j ≤ c (j + 1) := hc (by omega)
      have hright : c (j + 1) ≤ c (j + 2) := hc (by omega)
      have hbLeft : c (j + 1) ∈ Icc (c j) (c (j + 1)) := ⟨hleft, le_rfl⟩
      have hbRight : c (j + 1) ∈ Icc (c (j + 1)) (c (j + 2)) :=
        ⟨le_rfl, hright⟩
      have hitBoundary : t ≤ c (j + 1) :=
        ht.2.trans (hc (by omega : i + 1 ≤ j + 1))
      have hp : R j (c (j + 1)) ≤ R i t :=
        ih hjm hbLeft hitBoundary
      have hn : R (j + 1) u ≤ R (j + 1) (c (j + 1)) :=
        (hanti (j + 1) (by omega)).antitoneOn hbRight hu hu.1
      calc
        R (j + 1) u ≤ R (j + 1) (c (j + 1)) := hn
        _ = R j (c (j + 1)) := (hglue j hjlt).symm
        _ ≤ R i t := hp

/-- Strict radius order survives every finite transition in a connected piece
list.  At least one local inequality is strict whenever the two global heights
are unequal, even if intervening pieces are singletons. -/
theorem finite_connected_piece_radius_strict
    (m : ℕ) (c : ℕ → ℝ) (R : ℕ → ℝ → ℝ)
    (hc : Monotone c)
    (hanti : ∀ i ≤ m, StrictAntiOn (R i) (Icc (c i) (c (i + 1))))
    (hglue : ∀ i < m, R i (c (i + 1)) = R (i + 1) (c (i + 1)))
    {i j : ℕ} (hi : i ≤ m) (hj : j ≤ m) (hij : i ≤ j)
    {t u : ℝ} (ht : t ∈ Icc (c i) (c (i + 1)))
    (hu : u ∈ Icc (c j) (c (j + 1))) (htu : t < u) :
    R j u < R i t := by
  induction j, hij using Nat.le_induction generalizing u with
  | base => exact hanti i hi ht hu htu
  | @succ j hij ih =>
      have hjm : j ≤ m := by omega
      have hjlt : j < m := by omega
      have hbLeft : c (j + 1) ∈ Icc (c j) (c (j + 1)) :=
        ⟨hc (by omega), le_rfl⟩
      have hbRight : c (j + 1) ∈ Icc (c (j + 1)) (c (j + 2)) :=
        ⟨le_rfl, hc (by omega)⟩
      have hitBoundary : t ≤ c (j + 1) :=
        ht.2.trans (hc (by omega : i + 1 ≤ j + 1))
      rcases lt_or_eq_of_le hitBoundary with htb | htb
      · have hp : R j (c (j + 1)) < R i t := ih hjm hbLeft htb
        have hn : R (j + 1) u ≤ R (j + 1) (c (j + 1)) :=
          (hanti (j + 1) (by omega)).antitoneOn hbRight hu hu.1
        calc
          R (j + 1) u ≤ R (j + 1) (c (j + 1)) := hn
          _ = R j (c (j + 1)) := (hglue j hjlt).symm
          _ < R i t := hp
      · have hbu : c (j + 1) < u := by linarith
        have hn : R (j + 1) u < R (j + 1) (c (j + 1)) :=
          hanti (j + 1) (by omega) hbRight hu hbu
        have hp : R j (c (j + 1)) ≤ R i t :=
          finite_connected_piece_radius_anti m c R hc hanti hglue hi hjm hij
            ht hbLeft (by simpa [htb])
        calc
          R (j + 1) u < R (j + 1) (c (j + 1)) := hn
          _ = R j (c (j + 1)) := (hglue j hjlt).symm
          _ ≤ R i t := hp

/-- The Euclidean direction used by a lifted ray is never zero. -/
lemma direction_ne_zero (α : ℝ) : MixedTurnSafeCut.direction α ≠ 0 := by
  intro hz
  have h0 := congrArg (fun z : Plane => z 0) hz
  have h1 := congrArg (fun z : Plane => z 1) hz
  simp [MixedTurnSafeCut.direction] at h0 h1
  nlinarith [Real.sin_sq_add_cos_sq α]

/-- Global all-pairs nonoverlap on one lifted ray for the complete connected
finite piece list.  This is the form consumed by a later planar-interior
`Safe` proof: points from arbitrary pieces at unequal heights cannot coincide. -/
theorem finite_connected_piece_fixedRay_allPairs_ne
    (m : ℕ) (c : ℕ → ℝ) (R : ℕ → ℝ → ℝ)
    (hc : Monotone c)
    (hanti : ∀ i ≤ m, StrictAntiOn (R i) (Icc (c i) (c (i + 1))))
    (hglue : ∀ i < m, R i (c (i + 1)) = R (i + 1) (c (i + 1)))
    (O : Plane) (α : ℝ)
    {i j : ℕ} (hi : i ≤ m) (hj : j ≤ m) (hij : i ≤ j)
    {t u : ℝ} (ht : t ∈ Icc (c i) (c (i + 1)))
    (hu : u ∈ Icc (c j) (c (j + 1))) (htu : t < u) :
    O + R i t • MixedTurnSafeCut.direction α ≠
      O + R j u • MixedTurnSafeCut.direction α := by
  have hr := finite_connected_piece_radius_strict m c R hc hanti hglue
    hi hj hij ht hu htu
  intro he
  have hs : R i t • MixedTurnSafeCut.direction α =
      R j u • MixedTurnSafeCut.direction α := add_left_cancel he
  have hre : R i t = R j u :=
    smul_left_injective ℝ (direction_ne_zero α) hs
  linarith

/-- The sound bridge across two genuinely disconnected trace components.  No
hinge adjacency is asserted across the gap: componentwise antitonicity is
combined only with the strict inequality between the two facing endpoints. -/
theorem twoComponent_radius_strict
    (Rleft Rright : ℝ → ℝ) {a b c d : ℝ}
    (hleft : StrictAntiOn Rleft (Icc a b))
    (hright : StrictAntiOn Rright (Icc c d))
    (hab : a ≤ b) (hcd : c ≤ d)
    (hgap : Rright c < Rleft b)
    {t u : ℝ} (ht : t ∈ Icc a b) (hu : u ∈ Icc c d) :
    Rright u < Rleft t := by
  have hl : Rleft b ≤ Rleft t :=
    hleft.antitoneOn ht ⟨hab, le_rfl⟩ ht.2
  have hr : Rright u ≤ Rright c :=
    hright.antitoneOn ⟨le_rfl, hcd⟩ hu hu.1
  exact lt_of_le_of_lt hr (lt_of_lt_of_le hgap hl)

/-- Radius separation of disconnected components implies point separation,
without identifying their panel indices or inventing a hinge between them. -/
theorem twoComponent_fixedRay_allPairs_ne
    (Rleft Rright : ℝ → ℝ) {a b c d : ℝ}
    (hleft : StrictAntiOn Rleft (Icc a b))
    (hright : StrictAntiOn Rright (Icc c d))
    (hab : a ≤ b) (hcd : c ≤ d)
    (hgap : Rright c < Rleft b)
    (hleftpos : ∀ t ∈ Icc a b, 0 < Rleft t)
    (hrightpos : ∀ u ∈ Icc c d, 0 < Rright u)
    (O : Plane) (αleft αright : ℝ)
    {t u : ℝ} (ht : t ∈ Icc a b) (hu : u ∈ Icc c d) :
    O + Rleft t • MixedTurnSafeCut.direction αleft ≠
      O + Rright u • MixedTurnSafeCut.direction αright := by
  have hr := twoComponent_radius_strict Rleft Rright hleft hright hab hcd hgap ht hu
  intro he
  have hn := congrArg (fun x : Plane => ‖x - O‖) he
  have hdl : ‖MixedTurnSafeCut.direction αleft‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [MixedTurnSafeCut.direction, Fin.sum_univ_two]
  have hdr : ‖MixedTurnSafeCut.direction αright‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [MixedTurnSafeCut.direction, Fin.sum_univ_two]
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hdl, hdr, mul_one] at hn
  have hlpos : 0 ≤ Rleft t := (hleftpos t ht).le
  have hrpos : 0 ≤ Rright u := (hrightpos u hu).le
  rw [abs_of_nonneg hlpos, abs_of_nonneg hrpos] at hn
  linarith

end ConnectedFiniteTrace

section Seam

/-- Height component associated to one chosen real representative `φ` of a
physical ray when the longitudinal lifted sweep has width `L`.  This is the
paper's `I_j`; different representatives are kept separate. -/
def liftWindowHeights (α : ℝ → ℝ) (L φ : ℝ) : Set ℝ :=
  {t | t ∈ Icc (0 : ℝ) 1 ∧ φ ≤ α t ∧ α t ≤ φ + L}

/-- A monotone seam argument makes each fixed-lift height set order-convex,
including singleton and endpoint-clipped components. -/
theorem liftWindowHeights_orderConvex_of_monotone
    {α : ℝ → ℝ} (hα : MonotoneOn α (Icc (0 : ℝ) 1)) (L φ : ℝ)
    {s t u : ℝ} (hs : s ∈ liftWindowHeights α L φ)
    (hu : u ∈ liftWindowHeights α L φ) (hst : s ≤ t) (htu : t ≤ u) :
    t ∈ liftWindowHeights α L φ := by
  refine ⟨⟨hs.1.1.trans hst, htu.trans hu.1.2⟩, ?_, ?_⟩
  · exact hs.2.1.trans (hα hs.1 ⟨hs.1.1.trans hst, htu.trans hu.1.2⟩ hst)
  · exact (hα ⟨hs.1.1.trans hst, htu.trans hu.1.2⟩ hu.1 htu).trans hu.2.2

/-- The same interval conclusion for the opposite angular order. -/
theorem liftWindowHeights_orderConvex_of_antitone
    {α : ℝ → ℝ} (hα : AntitoneOn α (Icc (0 : ℝ) 1)) (L φ : ℝ)
    {s t u : ℝ} (hs : s ∈ liftWindowHeights α L φ)
    (hu : u ∈ liftWindowHeights α L φ) (hst : s ≤ t) (htu : t ≤ u) :
    t ∈ liftWindowHeights α L φ := by
  refine ⟨⟨hs.1.1.trans hst, htu.trans hu.1.2⟩, ?_, ?_⟩
  · exact hu.2.1.trans (hα ⟨hs.1.1.trans hst, htu.trans hu.1.2⟩ hu.1 htu)
  · exact (hα hs.1 ⟨hs.1.1.trans hst, htu.trans hu.1.2⟩ hst).trans hs.2.2

/-- A seam moves radially inward when its norm-radius is strictly decreasing
with physical height. -/
def RadiallyInward (O : Plane) (γ : ℝ → Plane) : Prop :=
  StrictAntiOn (polarRadius O ∘ γ) (Icc (0 : ℝ) 1)

/-- Heights of an affine seam lying in one of the two literal principal
argument half-planes. -/
def seamBranchHeights (P D O : Plane) (b : HalfPlaneBranch) : Set ℝ :=
  {t | t ∈ Icc (0 : ℝ) 1 ∧ InHalfPlane b (P + t • D - O)}

/-- An affine seam cannot leave and re-enter the upper half-plane.  This is the
explicit branch-component fact behind the two-branch decomposition. -/
theorem affineSeam_upper_branch_interval (P D O : Plane)
    {t₁ t t₂ : ℝ} (h₁ : 0 < (P + t₁ • D - O) 1)
    (h₂ : 0 < (P + t₂ • D - O) 1)
    (ht₁ : t₁ ≤ t) (htt₂ : t ≤ t₂) :
    0 < (P + t • D - O) 1 := by
  by_cases he : t₁ = t₂
  · subst t₂
    have : t = t₁ := le_antisymm htt₂ ht₁
    simpa [this] using h₁
  · let u := (t - t₁) / (t₂ - t₁)
    have hden : 0 < t₂ - t₁ := sub_pos.mpr (lt_of_le_of_ne (le_trans ht₁ htt₂) he)
    have hu0 : 0 ≤ u := div_nonneg (sub_nonneg.mpr ht₁) hden.le
    have hu1 : u ≤ 1 := (div_le_one hden).2 (by linarith)
    have hid : (P + t • D - O) 1 =
        (1 - u) * (P + t₁ • D - O) 1 + u * (P + t₂ • D - O) 1 := by
      dsimp [u]
      field_simp [ne_of_gt hden]
      ring
    rw [hid]
    by_cases hu : u = 0
    · rw [hu]
      norm_num
      simpa using h₁
    · have hupos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
      have hleft : 0 ≤ (1 - u) * (P + t₁ • D - O) 1 :=
        mul_nonneg (sub_nonneg.mpr hu1) h₁.le
      have hright : 0 < u * (P + t₂ • D - O) 1 := mul_pos hupos h₂
      linarith

/-- The closed lower branch is likewise height-convex.  Equality includes a
radial seam lying on the branch cut. -/
theorem affineSeam_lower_branch_interval (P D O : Plane)
    {t₁ t t₂ : ℝ} (h₁ : (P + t₁ • D - O) 1 ≤ 0)
    (h₂ : (P + t₂ • D - O) 1 ≤ 0)
    (ht₁ : t₁ ≤ t) (htt₂ : t ≤ t₂) :
    (P + t • D - O) 1 ≤ 0 := by
  by_cases he : t₁ = t₂
  · subst t₂
    have : t = t₁ := le_antisymm htt₂ ht₁
    simpa [this] using h₁
  · let u := (t - t₁) / (t₂ - t₁)
    have hden : 0 < t₂ - t₁ := sub_pos.mpr (lt_of_le_of_ne (le_trans ht₁ htt₂) he)
    have hu0 : 0 ≤ u := div_nonneg (sub_nonneg.mpr ht₁) hden.le
    have hu1 : u ≤ 1 := (div_le_one hden).2 (by linarith)
    have hid : (P + t • D - O) 1 =
        (1 - u) * (P + t₁ • D - O) 1 + u * (P + t₂ • D - O) 1 := by
      dsimp [u]
      field_simp [ne_of_gt hden]
      ring
    rw [hid]
    have hl : (1 - u) * (P + t₁ • D - O) 1 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hu1) h₁
    have hr : u * (P + t₂ • D - O) 1 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hu0 h₂
    linarith

/-- A radially inward affine seam has at most two height components: its
principal polar trace is the union of the explicit upper and lower branch
sets, and each branch set is an interval in height. -/
theorem radiallyInward_atMostTwoHeightComponents (P D O : Plane)
    (_hin : RadiallyInward O (fun t => P + t • D)) :
    (∀ ⦃t₁ t₂⦄, t₁ ∈ seamBranchHeights P D O .upper →
      t₂ ∈ seamBranchHeights P D O .upper → ∀ ⦃t⦄, t₁ ≤ t → t ≤ t₂ →
        t ∈ seamBranchHeights P D O .upper) ∧
    (∀ ⦃t₁ t₂⦄, t₁ ∈ seamBranchHeights P D O .lower →
      t₂ ∈ seamBranchHeights P D O .lower → ∀ ⦃t⦄, t₁ ≤ t → t ≤ t₂ →
        t ∈ seamBranchHeights P D O .lower) := by
  constructor
  · rintro t₁ t₂ ⟨ht₁, h₁⟩ ⟨ht₂, h₂⟩ t hle hge
    refine ⟨⟨le_trans ht₁.1 hle, le_trans hge ht₂.2⟩, ?_⟩
    exact affineSeam_upper_branch_interval P D O h₁ h₂ hle hge
  · rintro t₁ t₂ ⟨ht₁, h₁⟩ ⟨ht₂, h₂⟩ t hle hge
    refine ⟨⟨le_trans ht₁.1 hle, le_trans hge ht₂.2⟩, ?_⟩
    exact affineSeam_lower_branch_interval P D O h₁ h₂ hle hge

/-- Complete two-component cut statement.  The two explicit branch sets cover
all seam heights, are disjoint, are each order-convex, and inherit strict
radius decrease.  Thus singleton components and a seam lying on the branch cut
are represented literally rather than removed as degenerate cases. -/
theorem radiallyInward_twoComponent_cut (P D O : Plane)
    (hin : RadiallyInward O (fun t => P + t • D)) :
    seamBranchHeights P D O .upper ∪ seamBranchHeights P D O .lower =
        Icc (0 : ℝ) 1 ∧
      Disjoint (seamBranchHeights P D O .upper)
        (seamBranchHeights P D O .lower) ∧
      (∀ b, ∀ ⦃t₁ t₂⦄, t₁ ∈ seamBranchHeights P D O b →
        t₂ ∈ seamBranchHeights P D O b → ∀ ⦃t⦄, t₁ ≤ t → t ≤ t₂ →
          t ∈ seamBranchHeights P D O b) ∧
      (∀ b, StrictAntiOn (polarRadius O ∘ fun t => P + t • D)
        (seamBranchHeights P D O b)) := by
  have hconv := radiallyInward_atMostTwoHeightComponents P D O hin
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext t
    constructor
    · rintro (⟨ht, _⟩ | ⟨ht, _⟩) <;> exact ht
    · intro ht
      by_cases hy : 0 < (P + t • D - O) 1
      · exact Or.inl ⟨ht, hy⟩
      · exact Or.inr ⟨ht, le_of_not_gt hy⟩
  · apply Set.disjoint_left.2
    rintro t ⟨_, hu⟩ ⟨_, hl⟩
    exact (not_lt_of_ge hl) hu
  · intro b
    cases b with
    | upper => exact hconv.1
    | lower => exact hconv.2
  · intro b s hs t ht hst
    exact hin hs.1 ht.1 hst

end Seam

section Physical

variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

/-- Source-level version with no caller-supplied support record: negative RF
constructs the fixed baseline pole and gives a genuine polar decomposition of
every material point in every physical panel. -/
theorem baseline_material_point_polar
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    {i : ℕ} (hi : i ≤ PhysicalMixedTurnSource.MechanismN A B)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    InHalfPlane
        (halfPlaneBranch
          (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
          ((FixedBaselinePolarRayGeometry.baselineStrip A B hh).point i s t))
        ((FixedBaselinePolarRayGeometry.baselineStrip A B hh).point i s t -
          PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)) ∧
      0 < polarRadius
        (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
        ((FixedBaselinePolarRayGeometry.baselineStrip A B hh).point i s t) ∧
      (FixedBaselinePolarRayGeometry.baselineStrip A B hh).point i s t -
          PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ) =
        polarRadius
            (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
            ((FixedBaselinePolarRayGeometry.baselineStrip A B hh).point i s t) •
          MixedTurnSafeCut.direction
            (polarAngle
              (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
              ((FixedBaselinePolarRayGeometry.baselineStrip A B hh).point i s t)) := by
  exact material_point_polar _ _
    (FixedBaselinePolarRayGeometry.baselineStrip_radialSupport A B hh hΔ)
    hi hs ht

/-- Compatibility also includes the virtual final hinge of the physical
baseline, not only transitions stored in the finite strip record. -/
theorem physical_hinge_compatibility (j : ℕ) (t : ℝ) :
    FixedBaselinePolarRayGeometry.retainedHinge A B hh j t =
      PhysicalMixedTurnSource.directDevelopedMap A B hh 0 (j + 1)
        (PhysicalMixedTurnSource.faceEntryAt A B hh t
          (PhysicalMixedTurnSource.familySource A B 0 (j + 1))) :=
  FixedBaselinePolarRayGeometry.retainedHinge_eq_next_entry A B hh j t

/-- The root seam really begins at the root lower endpoint of the baseline
strip. -/
theorem rootSeam_zero_eq :
    FixedBaselinePolarRayGeometry.rootSeam A B hh 0 =
      (FixedBaselinePolarRayGeometry.baselineStrip A B hh).B 0 := by
  simp only [FixedBaselinePolarRayGeometry.rootSeam,
    FixedBaselinePolarRayGeometry.baselineStrip,
    PhysicalMixedTurnSource.developedLower,
    PhysicalMixedTurnSource.faceEntryAt]
  congr 1
  exact AffineMap.lineMap_apply_zero _ _

/-- The root seam really ends at the root upper endpoint. -/
theorem rootSeam_one_eq :
    FixedBaselinePolarRayGeometry.rootSeam A B hh 1 =
      (FixedBaselinePolarRayGeometry.baselineStrip A B hh).B 0 +
        (FixedBaselinePolarRayGeometry.baselineStrip A B hh).d 0 := by
  simp only [FixedBaselinePolarRayGeometry.rootSeam,
    FixedBaselinePolarRayGeometry.baselineStrip,
    PhysicalMixedTurnSource.developedLower,
    PhysicalMixedTurnSource.developedUpper,
    PhysicalMixedTurnSource.faceEntryAt,
    add_sub_cancel]
  congr 1
  exact AffineMap.lineMap_apply_one _ _

/-- The lower facing endpoints are literal root and terminal copies of the
same physical seam. -/
theorem facing_lower_endpoints_literal :
    FixedBaselinePolarRayGeometry.terminalSeam A B hh 0 =
      PhysicalMixedTurnSource.fullCircuit A B hh 0
        (FixedBaselinePolarRayGeometry.rootSeam A B hh 0) := rfl

/-- The upper facing endpoints are literal root and terminal copies of the
same physical seam. -/
theorem facing_upper_endpoints_literal :
    FixedBaselinePolarRayGeometry.terminalSeam A B hh 1 =
      PhysicalMixedTurnSource.fullCircuit A B hh 0
        (FixedBaselinePolarRayGeometry.rootSeam A B hh 1) := rfl

/-- The lower terminal endpoint is the actual virtual terminal-strip endpoint,
not merely a point with a congruent heading. -/
theorem terminalSeam_zero_eq :
    FixedBaselinePolarRayGeometry.terminalSeam A B hh 0 =
      (FixedBaselinePolarRayGeometry.baselineStrip A B hh).B
        (PhysicalMixedTurnSource.MechanismN A B + 1) := by
  rw [facing_lower_endpoints_literal A B hh, rootSeam_zero_eq A B hh,
    ← FixedBaselinePolarRayGeometry.terminal_lower_is_fullCircuit A B hh]

/-- The upper terminal endpoint is the actual virtual terminal-strip endpoint. -/
theorem terminalSeam_one_eq :
    FixedBaselinePolarRayGeometry.terminalSeam A B hh 1 =
      (FixedBaselinePolarRayGeometry.baselineStrip A B hh).B
          (PhysicalMixedTurnSource.MechanismN A B + 1) +
        (FixedBaselinePolarRayGeometry.baselineStrip A B hh).d
          (PhysicalMixedTurnSource.MechanismN A B + 1) := by
  rw [facing_upper_endpoints_literal A B hh, rootSeam_one_eq A B hh,
    ← FixedBaselinePolarRayGeometry.terminal_upper_is_fullCircuit A B hh]

/-- Exact radius identity for corresponding points of the two facing copies. -/
theorem terminalSeam_radius_eq
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) ≠ 0)
    (t : ℝ) :
    ‖FixedBaselinePolarRayGeometry.terminalSeam A B hh t -
        PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ‖ =
      ‖FixedBaselinePolarRayGeometry.rootSeam A B hh t -
        PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ‖ := by
  rw [FixedBaselinePolarRayGeometry.terminalSeam_eq_fullCircuit,
    FixedBaselinePolarRayGeometry.fullCircuit_sub_pole A B hh hΔ,
    (PhysicalMixedTurnSource.planeRotation _).norm_map]

/-- First cross-gap direction: root-to-terminal comparison reduces exactly to
one same-seam radius comparison. -/
theorem root_lt_terminal_iff
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) ≠ 0)
    (s t : ℝ) :
    ‖FixedBaselinePolarRayGeometry.rootSeam A B hh s -
        PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ‖ <
      ‖FixedBaselinePolarRayGeometry.terminalSeam A B hh t -
        PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ‖ ↔
    ‖FixedBaselinePolarRayGeometry.rootSeam A B hh s -
        PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ‖ <
      ‖FixedBaselinePolarRayGeometry.rootSeam A B hh t -
        PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ‖ := by
  rw [terminalSeam_radius_eq A B hh hΔ t]

/-- Reverse cross-gap direction: terminal-to-root comparison reduces exactly to
one same-seam radius comparison. -/
theorem terminal_lt_root_iff
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) ≠ 0)
    (s t : ℝ) :
    ‖FixedBaselinePolarRayGeometry.terminalSeam A B hh s -
        PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ‖ <
      ‖FixedBaselinePolarRayGeometry.rootSeam A B hh t -
        PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ‖ ↔
    ‖FixedBaselinePolarRayGeometry.rootSeam A B hh s -
        PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ‖ <
      ‖FixedBaselinePolarRayGeometry.rootSeam A B hh t -
        PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ‖ := by
  rw [terminalSeam_radius_eq A B hh hΔ s]

/-- The two orientations in which the cut-open angular trace can face its root
and terminal seam copies. -/
inductive FacingDirection
  | rootToTerminal
  | terminalToRoot
  deriving DecidableEq

/-- Ordered facing copies in either angular direction. -/
noncomputable def facingSeamPair (dir : FacingDirection) (t : ℝ) : Plane × Plane :=
  match dir with
  | .rootToTerminal =>
      (FixedBaselinePolarRayGeometry.rootSeam A B hh t,
        FixedBaselinePolarRayGeometry.terminalSeam A B hh t)
  | .terminalToRoot =>
      (FixedBaselinePolarRayGeometry.terminalSeam A B hh t,
        FixedBaselinePolarRayGeometry.rootSeam A B hh t)

/-- In both angular directions the facing endpoint is literally the translated
`fullCircuit` copy of the root seam, not a modularly relabelled panel. -/
theorem facingSeamPair_literal (dir : FacingDirection) (t : ℝ) :
    facingSeamPair A B hh dir t =
      match dir with
      | .rootToTerminal =>
          (FixedBaselinePolarRayGeometry.rootSeam A B hh t,
            PhysicalMixedTurnSource.fullCircuit A B hh 0
              (FixedBaselinePolarRayGeometry.rootSeam A B hh t))
      | .terminalToRoot =>
          (PhysicalMixedTurnSource.fullCircuit A B hh 0
              (FixedBaselinePolarRayGeometry.rootSeam A B hh t),
            FixedBaselinePolarRayGeometry.rootSeam A B hh t) := by
  cases dir <;> rfl

/-- Literal full-circuit copies preserve the genuine polar radius. -/
theorem terminalSeam_polarRadius_eq
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) ≠ 0)
    (t : ℝ) :
    polarRadius (PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ)
        (FixedBaselinePolarRayGeometry.terminalSeam A B hh t) =
      polarRadius (PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ)
        (FixedBaselinePolarRayGeometry.rootSeam A B hh t) := by
  simpa only [polarRadius_eq_norm] using terminalSeam_radius_eq A B hh hΔ t

/-- Actual cross-gap inequalities in both height orders.  They combine strict
inwardness with the translated full-circuit radius identity, and are therefore
strict for every unequal pair of heights. -/
theorem fullCircuit_crossGap_strict
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) ≠ 0)
    (hin : RadiallyInward
      (PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ)
      (FixedBaselinePolarRayGeometry.rootSeam A B hh))
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    (s < t →
      polarRadius (PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ)
          (FixedBaselinePolarRayGeometry.terminalSeam A B hh t) <
        polarRadius (PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ)
          (FixedBaselinePolarRayGeometry.rootSeam A B hh s)) ∧
    (t < s →
      polarRadius (PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ)
          (FixedBaselinePolarRayGeometry.rootSeam A B hh s) <
        polarRadius (PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ)
          (FixedBaselinePolarRayGeometry.terminalSeam A B hh t)) := by
  constructor
  · intro hst
    rw [terminalSeam_polarRadius_eq A B hh hΔ t]
    exact hin hs ht hst
  · intro hts
    rw [terminalSeam_polarRadius_eq A B hh hΔ t]
    exact hin ht hs hts

/-- The accepted-paper gap step for two same-sheet trace components.  Each
component is ordered internally, while the only comparison across the missing
panels is the actual root/terminal `fullCircuit` endpoint inequality.  Both
angular orders are handled explicitly; no fictitious hinge adjacency is used. -/
theorem fullCircuit_orders_two_trace_components
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) ≠ 0)
    (hin : RadiallyInward
      (PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ)
      (FixedBaselinePolarRayGeometry.rootSeam A B hh))
    (dir : FacingDirection)
    (Rleft Rright : ℝ → ℝ) {a b c d : ℝ}
    (hleft : StrictAntiOn Rleft (Icc a b))
    (hright : StrictAntiOn Rright (Icc c d))
    (hab : a ≤ b) (hcd : c ≤ d)
    (hb : b ∈ Icc (0 : ℝ) 1) (hc : c ∈ Icc (0 : ℝ) 1) (hbc : b < c)
    (hleftEnd : Rleft b = polarRadius
      (PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ)
      (facingSeamPair A B hh dir b).1)
    (hrightEnd : Rright c = polarRadius
      (PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ)
      (facingSeamPair A B hh dir c).2) :
    ∀ {t u : ℝ}, t ∈ Icc a b → u ∈ Icc c d → Rright u < Rleft t := by
  have hgap : Rright c < Rleft b := by
    rw [hleftEnd, hrightEnd]
    cases dir with
    | rootToTerminal =>
        simp only [facingSeamPair]
        exact (fullCircuit_crossGap_strict A B hh hΔ hin hb hc).1 hbc
    | terminalToRoot =>
        simp only [facingSeamPair]
        rw [terminalSeam_polarRadius_eq A B hh hΔ b]
        exact hin hb hc hbc
  intro t u ht hu
  exact twoComponent_radius_strict Rleft Rright hleft hright hab hcd hgap ht hu

/-- Consequently unequal seam heights cannot name the same point across the
cut gap.  This is the all-pairs (rather than corresponding-point) consequence
of the two strict cross-gap inequalities. -/
theorem fullCircuit_crossGap_allPairs_ne
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) ≠ 0)
    (hin : RadiallyInward
      (PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ)
      (FixedBaselinePolarRayGeometry.rootSeam A B hh))
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hst : s ≠ t) :
    FixedBaselinePolarRayGeometry.rootSeam A B hh s ≠
      FixedBaselinePolarRayGeometry.terminalSeam A B hh t := by
  intro heq
  obtain hlt | hgt := lt_or_gt_of_ne hst
  · have hstrict := (fullCircuit_crossGap_strict A B hh hΔ hin hs ht).1 hlt
    rw [heq] at hstrict
    exact (lt_irrefl _ hstrict)
  · have hstrict := (fullCircuit_crossGap_strict A B hh hΔ hin hs ht).2 hgt
    rw [heq] at hstrict
    exact (lt_irrefl _ hstrict)

end Physical

end
end FixedBaselinePolarTrace

#print axioms FixedBaselinePolarTrace.material_point_polar
#print axioms FixedBaselinePolarTrace.polar_compatible_at_hinge
#print axioms FixedBaselinePolarTrace.finite_sameSheet_fixedRay_order
#print axioms FixedBaselinePolarTrace.fixedRay_transition_radius
#print axioms FixedBaselinePolarTrace.global_finite_sameSheet_fixedRay_trace
#print axioms FixedBaselinePolarTrace.mem_orderedEligiblePieces_iff
#print axioms FixedBaselinePolarTrace.orderedEligiblePieces_omission_classification
#print axioms FixedBaselinePolarTrace.radialHinge_connects_adjacent_pieces
#print axioms FixedBaselinePolarTrace.finite_connected_piece_radius_strict
#print axioms FixedBaselinePolarTrace.finite_connected_piece_fixedRay_allPairs_ne
#print axioms FixedBaselinePolarTrace.twoComponent_radius_strict
#print axioms FixedBaselinePolarTrace.twoComponent_fixedRay_allPairs_ne
#print axioms FixedBaselinePolarTrace.radiallyInward_atMostTwoHeightComponents
#print axioms FixedBaselinePolarTrace.radiallyInward_twoComponent_cut
#print axioms FixedBaselinePolarTrace.baseline_material_point_polar
#print axioms FixedBaselinePolarTrace.physical_hinge_compatibility
#print axioms FixedBaselinePolarTrace.rootSeam_zero_eq
#print axioms FixedBaselinePolarTrace.rootSeam_one_eq
#print axioms FixedBaselinePolarTrace.facing_lower_endpoints_literal
#print axioms FixedBaselinePolarTrace.facing_upper_endpoints_literal
#print axioms FixedBaselinePolarTrace.terminalSeam_zero_eq
#print axioms FixedBaselinePolarTrace.terminalSeam_one_eq
#print axioms FixedBaselinePolarTrace.root_lt_terminal_iff
#print axioms FixedBaselinePolarTrace.terminal_lt_root_iff
#print axioms FixedBaselinePolarTrace.facingSeamPair_literal
#print axioms FixedBaselinePolarTrace.fullCircuit_crossGap_strict
#print axioms FixedBaselinePolarTrace.fullCircuit_orders_two_trace_components
#print axioms FixedBaselinePolarTrace.fullCircuit_crossGap_allPairs_ne
