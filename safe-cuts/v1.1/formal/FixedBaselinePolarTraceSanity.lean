import FixedBaselinePolarTrace

open Set
open scoped Classical
open FixedBaselinePolarTrace FixedBaselinePolarRayGeometry
open RadialExtremalSafety MixedTurnSafeCut PolygonSupportCompleteness

namespace FixedBaselinePolarTraceSanity
noncomputable section
set_option maxHeartbeats 8000000

abbrev Plane := MixedTurnSafeCut.Plane

example {n : ℕ} (S : TriangularRadialStrip n) (O : Plane)
    (hR : S.RadialSupport O) {i : ℕ} (hi : i ≤ n)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ (b : HalfPlaneBranch) (r α : ℝ),
      InHalfPlane b (S.point i s t - O) ∧ 0 < r ∧
      S.point i s t - O = r • direction α := by
  refine ⟨halfPlaneBranch O (S.point i s t),
    polarRadius O (S.point i s t), polarAngle O (S.point i s t), ?_⟩
  exact material_point_polar S O hR hi hs ht

example {n : ℕ} (S : TriangularRadialStrip n) (O : Plane)
    (hR : S.RadialSupport O) (α : ℝ) :
    ∀ i : Fin (n + 1), ∀ {s₁ s₂ t₁ t₂ r₁ r₂ : ℝ}, t₁ < t₂ →
      RayHit S O α i s₁ t₁ r₁ → RayHit S O α i s₂ t₂ r₂ → r₂ < r₁ :=
  (finite_sameSheet_fixedRay_order S O hR α).1

example (P D O : Plane) (hin : RadiallyInward O (fun t => P + t • D)) :
    ∀ ⦃t₁ t₂⦄, t₁ ∈ seamBranchHeights P D O .upper →
      t₂ ∈ seamBranchHeights P D O .upper → ∀ ⦃t⦄, t₁ ≤ t → t ≤ t₂ →
        t ∈ seamBranchHeights P D O .upper :=
  (radiallyInward_atMostTwoHeightComponents P D O hin).1

example {n : ℕ} (S : TriangularRadialStrip n) (O : Plane)
    (α : ℝ) (i : Fin (n + 1)) {s t r : ℝ}
    (hit : RayHit S O α i s t r) :
    i ∈ orderedEligiblePieces S O α :=
  hit_piece_mem S O α i hit

example (P D O : Plane) (hin : RadiallyInward O (fun t => P + t • D)) :
    seamBranchHeights P D O .upper ∪ seamBranchHeights P D O .lower =
      Icc (0 : ℝ) 1 :=
  (radiallyInward_twoComponent_cut P D O hin).1

/-- Exact scalar control for the new disconnected-component bridge. -/
example {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (2 : ℝ) 3) :
    (5 - u : ℝ) < 10 - t := by
  apply twoComponent_radius_strict (fun x : ℝ => 10 - x) (fun x : ℝ => 5 - x)
    (a := 0) (b := 1) (c := 2) (d := 3)
  · intro x hx y hy hxy
    linarith
  · intro x hx y hy hxy
    linarith
  · norm_num
  · norm_num
  · norm_num
  · exact ht
  · exact hu

/-- A genuine physical source, rather than an abstract strip, supplies the
panel-local open polar window directly from its developed headings and RF. -/
example {nA nB : ℕ} [NeZero nA] [NeZero nB]
    (A : MergedNormalPrismatoid.ReducedConvexPolygon nA)
    (B : MergedNormalPrismatoid.ReducedConvexPolygon nB)
    {h : ℝ} (hh : 0 < h)
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    {i : ℕ} (hi : i ≤ PhysicalMixedTurnSource.MechanismN A B)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) : True := by
  have _window := panelPointPolarLift_mem_window A B hh hΔ hi hs ht
  trivial

/-! The proposed no-gap step for `orderedEligiblePieces` is false under the
hypotheses of `FixedBaselinePolarTrace`.  This exact three-panel strip has
radial support, panels zero and two hit the positive horizontal ray, and the
intervening panel is a nonparallel miss. -/

private def gapB : ℕ → Plane
  | 0 => WithLp.toLp 2 ![(3 : ℝ), -1]
  | 1 => WithLp.toLp 2 ![(-12 : ℝ), -13]
  | _ => WithLp.toLp 2 ![(-42 : ℝ), 29]

private def gapV : ℕ → Plane
  | 0 => WithLp.toLp 2 ![(-5 : ℝ), -4]
  | 1 => WithLp.toLp 2 ![(-5 : ℝ), 7]
  | _ => WithLp.toLp 2 ![(7 : ℝ), -4]

private def gapD : ℕ → Plane
  | 0 => WithLp.toLp 2 ![(0 : ℝ), 1]
  | 1 => WithLp.toLp 2 ![(10 : ℝ), 9]
  | _ => WithLp.toLp 2 ![(30 : ℝ), -19]

private def gapLower : ℕ → ℝ
  | 0 => 3
  | 1 => 6
  | _ => 2

private def gapUpper : ℕ → ℝ
  | 0 => 1
  | 1 => 2
  | _ => 3

private def gapStrip : TriangularRadialStrip 2 where
  B := gapB
  v := gapV
  d := gapD
  lowerCoeff := gapLower
  upperCoeff := gapUpper
  v_ne_zero i hi := by
    interval_cases i <;> intro hz
    all_goals have h := congrArg (fun z : Plane => z 0) hz
    all_goals norm_num [gapV] at h
  lowerCoeff_nonneg i hi := by interval_cases i <;> norm_num [gapLower]
  upperCoeff_nonneg i hi := by interval_cases i <;> norm_num [gapUpper]
  lower_step i hi := by
    interval_cases i <;> ext k <;> fin_cases k <;>
      norm_num [gapB, gapV, gapLower]
  hinge_step i hi := by
    interval_cases i <;> ext k <;> fin_cases k <;>
      norm_num [gapD, gapV, gapLower, gapUpper]
  orientation_neg i hi := by
    interval_cases i <;> norm_num [gapV, gapD, MixedTurnSafeCut.det]

private theorem gapStrip_radialSupport : gapStrip.RadialSupport 0 := by
  intro i hi
  interval_cases i <;>
    norm_num [gapStrip, gapB, gapV, gapD, MixedTurnSafeCut.det]

private theorem gapStrip_hit_zero :
    RayHit gapStrip 0 0 0 0 1 3 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  ext k
  fin_cases k <;>
    norm_num [gapStrip, gapB, gapV, gapD, gapLower, gapUpper,
      TriangularRadialStrip.point, direction]

private theorem gapStrip_hit_two :
    RayHit gapStrip 0 0 2 (72 / 73 : ℝ) (23 / 25 : ℝ) (144 / 25 : ℝ) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  ext k
  fin_cases k <;>
    norm_num [gapStrip, gapB, gapV, gapD, gapLower, gapUpper,
      TriangularRadialStrip.point, direction]

private theorem gapStrip_one_empty :
    eligibleHeights gapStrip 0 0 1 = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  rintro ⟨t, ht⟩
  rcases ht with ⟨s, r, hs, ht, hr, heq⟩
  have heq0 := congrArg (fun z : Plane => z 0) heq
  have hc : 0 ≤ (1 - t) * 6 + t * 2 := by nlinarith [ht.1, ht.2]
  have hsprod : 0 ≤ s * ((1 - t) * 6 + t * 2) := mul_nonneg hs.1 hc
  have ht10 : t * 10 ≤ 10 := by nlinarith [ht.2]
  have hterm : -(s * ((1 - t) * 6 + t * 2) * 5) ≤ 0 := by
    nlinarith
  norm_num [gapStrip, gapB, gapV, gapD, gapLower, gapUpper,
    TriangularRadialStrip.point, direction] at heq0
  nlinarith

/-- Concrete counterexample to the requested no-gap/adjacency assertion:
`1` is omitted as a genuinely nonparallel miss between two retained pieces. -/
theorem orderedEligiblePieces_can_skip_nonparallel_panel :
    (⟨0, by omega⟩ : Fin 3) ∈ orderedEligiblePieces gapStrip 0 0 ∧
      (⟨1, by omega⟩ : Fin 3) ∉ orderedEligiblePieces gapStrip 0 0 ∧
      (⟨2, by omega⟩ : Fin 3) ∈ orderedEligiblePieces gapStrip 0 0 ∧
      MixedTurnSafeCut.det (direction 0) (gapStrip.v 1) ≠ 0 := by
  refine ⟨hit_piece_mem gapStrip 0 0 ⟨0, by omega⟩ gapStrip_hit_zero, ?_,
    hit_piece_mem gapStrip 0 0 ⟨2, by omega⟩ gapStrip_hit_two, ?_⟩
  · exact (not_mem_orderedEligiblePieces_iff gapStrip 0 0 ⟨1, by omega⟩).2
      gapStrip_one_empty
  · norm_num [gapStrip, gapV, direction, MixedTurnSafeCut.det]

/-- Existential form of the counterexample, exposing that the retained panels
have no retained index between them even though the omitted panel is
nonparallel. -/
theorem exists_orderedEligiblePieces_nonparallel_gap :
    ∃ (S : TriangularRadialStrip 2) (O : Plane) (α : ℝ),
      S.RadialSupport O ∧
      (⟨0, by omega⟩ : Fin 3) ∈ orderedEligiblePieces S O α ∧
      (⟨2, by omega⟩ : Fin 3) ∈ orderedEligiblePieces S O α ∧
      (∀ k : Fin 3, 0 < k.val → k.val < 2 →
        k ∉ orderedEligiblePieces S O α) ∧
      MixedTurnSafeCut.det (direction α) (S.v 1) ≠ 0 := by
  refine ⟨gapStrip, 0, 0, gapStrip_radialSupport,
    orderedEligiblePieces_can_skip_nonparallel_panel.1,
    orderedEligiblePieces_can_skip_nonparallel_panel.2.2.1, ?_,
    orderedEligiblePieces_can_skip_nonparallel_panel.2.2.2⟩
  intro k hk0 hk2
  fin_cases k
  · norm_num at hk0
  · exact orderedEligiblePieces_can_skip_nonparallel_panel.2.1
  · norm_num at hk2

end
end FixedBaselinePolarTraceSanity

#print axioms FixedBaselinePolarTraceSanity.exists_orderedEligiblePieces_nonparallel_gap
#print axioms FixedBaselinePolarTrace.material_point_polar
#print axioms FixedBaselinePolarTrace.finite_sameSheet_fixedRay_order
#print axioms FixedBaselinePolarTrace.fixedRay_transition_radius
#print axioms FixedBaselinePolarTrace.radiallyInward_atMostTwoHeightComponents
#print axioms FixedBaselinePolarTrace.root_lt_terminal_iff
#print axioms FixedBaselinePolarTrace.terminal_lt_root_iff
