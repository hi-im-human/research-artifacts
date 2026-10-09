import SelectedPositiveMaterialHit

open Set
open scoped BigOperators Classical NNReal
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CommonSupportMerge OriginalFacetCertificates NormalFanSplice MaximalSupportCells
open CyclicCutOrders EuclideanPrismatoidCoordinates PolyhedralInputBridge
open TrimmedFacetWitnesses BandGeometryAssembly FiniteWitnessClosure SingleCutRecovery
open CutSurfaceQuotient MixedTurnSafeCut PolygonSetReconstruction ConvexPolygonTurning
open FixedBaselinePolarRayGeometry SelectedNegativeRootPolar PhysicalMixedTurnSource

namespace SelectedPositiveRootPolarLift
noncomputable section
set_option maxHeartbeats 64000000
attribute [local irreducible] positiveRoot sourceIndexEquiv

variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

private abbrev N := PhysicalMixedTurnSource.MechanismN A B
private abbrev Δ := PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh)

/-- Equal reflected physical points determine real polar lifts differing by a
whole turn; positive radial lengths exclude the antipodal alternative. -/
private theorem positive_interior_lifts_same_ray (hΔ : 0 < Δ A B hh)
    {i j : ℕ} {s t s' u : ℝ}
    (hi : i ≤ N A B) (hj : j ≤ N A B)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hs' : s' ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1)
    (heq : (normalizedStrip A B hh hΔ).point i s t =
      (normalizedStrip A B hh hΔ).point j s' u) :
    ∃ m : ℤ, pointPolarLift A B hh hΔ j s' u =
      pointPolarLift A B hh hΔ i s t + 2 * Real.pi * (m : ℝ) := by
  let O := normalizedPole A B hh hΔ
  let p := (normalizedStrip A B hh hΔ).point i s t
  let φ := pointPolarLift A B hh hΔ i s t
  let ψ := pointPolarLift A B hh hΔ j s' u
  have hd₁ := pointPolarLift_decomposition A B hh hΔ hi hs ht
  have hd₂ := pointPolarLift_decomposition A B hh hΔ hj hs' hu
  have hnorm : ‖p - O‖ ≠ 0 := ne_of_gt hd₁.2
  have hdir : MixedTurnSafeCut.direction ψ = MixedTurnSafeCut.direction φ := by
    apply smul_right_injective Plane hnorm
    change ‖p - O‖ • MixedTurnSafeCut.direction ψ =
      ‖p - O‖ • MixedTurnSafeCut.direction φ
    rw [← hd₁.1]
    have hd₂' : p - O = ‖p - O‖ • MixedTurnSafeCut.direction ψ := by
      simpa only [← heq] using hd₂.1
    exact hd₂'.symm
  obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp
    (FixedBaselinePolarRayGeometry.angle_eq_mod_two_pi_of_direction_eq hdir)
  refine ⟨m, ?_⟩
  change ψ = φ + 2 * Real.pi * (m : ℝ)
  linarith

/-- The actual positive radial-selected source cut is safe on the *full*
original certificate domains, without a mixed-turn or supplied safety premise. -/
theorem selectedPositiveDirectMap_full_safe (hΔ : 0 < Δ A B hh) :
    Safe
      (fun i => (certificate A B hh (order A B
        (prev (sourceIndexEquiv A B (positiveRoot A B hh hΔ))) i)).domain)
      (fun i => GeneralTwoRimUnfolding.arbitraryCutFaceMap A B hh
        (positiveRoot A B hh hΔ) i) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro p hp hq
  obtain ⟨s, t, hs, ht, hp'⟩ :=
    selectedPositiveImageBoundary A B hh hΔ i hp
  obtain ⟨s', u, hs', hu, hq'⟩ :=
    selectedPositiveImageBoundary A B hh hΔ j hq
  have hn₁ := reflected_source_point A B hh hΔ hp'
  have hn₂ := reflected_source_point A B hh hΔ hq'
  have hi : i.val ≤ N A B := Nat.le_of_lt_succ i.isLt
  have hj : j.val ≤ N A B := Nat.le_of_lt_succ j.isLt
  have hit₁ := reflected_source_materialHit A B hh hΔ hi hs ht
  have hit₂ := reflected_source_materialHit A B hh hΔ hj hs' hu
  have heq : (normalizedStrip A B hh hΔ).point i.val s (1 - t) =
      (normalizedStrip A B hh hΔ).point j.val s' (1 - u) :=
    hn₁.symm.trans hn₂
  obtain ⟨m, hm⟩ := positive_interior_lifts_same_ray A B hh hΔ
    hit₁.1 hit₂.1 hit₁.2.1 ⟨hit₁.2.2.1.1.le, hit₁.2.2.1.2.le⟩
    hit₂.2.1 ⟨hit₂.2.2.1.1.le, hit₂.2.2.1.2.le⟩ heq
  have hit₂' : MaterialHit A B hh hΔ
      (pointPolarLift A B hh hΔ i.val s (1 - t)) m j.val s' (1 - u) :=
    ⟨hit₂.1, hit₂.2.1, hit₂.2.2.1, hm⟩
  exact (materialHit_distinct_faceInteriors_ne A B hh hΔ _ hit₁ hit₂'
    (fun h => hij (Fin.ext h)) hs hs') heq

end
end SelectedPositiveRootPolarLift
