import FixedBaselineCyclicConjugacy
import RadialExtremalSafety
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

open Set
open scoped BigOperators Classical NNReal
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CommonSupportMerge OriginalFacetCertificates NormalFanSplice MaximalSupportCells
open CyclicCutOrders EuclideanPrismatoidCoordinates PolyhedralInputBridge
open TrimmedFacetWitnesses BandGeometryAssembly FiniteWitnessClosure SingleCutRecovery
open CutSurfaceQuotient MixedTurnSafeCut PolygonSetReconstruction ConvexPolygonTurning

namespace FixedBaselinePolarRayGeometry
noncomputable section
set_option maxHeartbeats 8000000

abbrev Plane := MixedTurnSafeCut.Plane

/-- A finite chain of closed intervals whose consecutive endpoints agree
fills the entire interval from the last lower endpoint to the first upper
endpoint. -/
lemma exists_mem_Icc_of_chain {N : ℕ} {lo hi : ℕ → ℝ}
    (horder : ∀ i ≤ N, lo i ≤ hi i)
    (hchain : ∀ i < N, hi (i + 1) = lo i)
    {x : ℝ} (hx : x ∈ Icc (lo N) (hi 0)) :
    ∃ i ≤ N, x ∈ Icc (lo i) (hi i) := by
  induction N with
  | zero => exact ⟨0, le_rfl, by simpa using hx⟩
  | succ N ih =>
      by_cases hcut : x ≤ lo N
      · refine ⟨N + 1, le_rfl, hx.1, ?_⟩
        rw [hchain N (by omega)]
        exact hcut
      · have hxN : x ∈ Icc (lo N) (hi 0) :=
          ⟨le_of_not_ge hcut, hx.2⟩
        obtain ⟨i, hiN, hxi⟩ := ih
          (fun i hi => horder i (by omega))
          (fun i hi => hchain i (by omega)) hxN
        exact ⟨i, by omega, hxi⟩

lemma Icc_subset_Icc_of_chain {N : ℕ} {lo hi : ℕ → ℝ}
    (horder : ∀ i ≤ N, lo i ≤ hi i)
    (hchain : ∀ i < N, hi (i + 1) = lo i)
    {i : ℕ} (hiN : i ≤ N) :
    Icc (lo i) (hi i) ⊆ Icc (lo N) (hi 0) := by
  have hlo : lo N ≤ lo i := by
    induction N with
    | zero =>
        have hieq : i = 0 := Nat.eq_zero_of_le_zero hiN
        subst i
        exact le_rfl
    | succ N ih =>
        by_cases hieq : i = N + 1
        · simp [hieq]
        · have hi' : i ≤ N := by omega
          calc
            lo (N + 1) ≤ hi (N + 1) := horder _ le_rfl
            _ = lo N := hchain N (by omega)
            _ ≤ lo i := ih (fun j hj => horder j (by omega))
              (fun j hj => hchain j (by omega)) hi'
  have hhi_aux : ∀ j, j ≤ N → hi j ≤ hi 0 := by
    intro j hj
    induction j with
    | zero => exact le_rfl
    | succ j ih =>
        calc
          hi (j + 1) = lo j := hchain j (by omega)
          _ ≤ hi j := horder j (by omega)
          _ ≤ hi 0 := ih (by omega)
  have hhi : hi i ≤ hi 0 := hhi_aux i hiN
  intro x hx
  exact ⟨hlo.trans hx.1, hx.2.trans hhi⟩

section Raw
variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

/-- The actual root-zero physical panels, with zero rim runs retained.  Every
field is computed from the source development; there is no caller-supplied
correctness certificate. -/
noncomputable def baselineStrip :
    RadialExtremalSafety.TriangularRadialStrip (PhysicalMixedTurnSource.MechanismN A B) where
  B i := PhysicalMixedTurnSource.developedLower A B hh 0 i
  v i := PhysicalMixedTurnSource.developedForward A B hh 0 i
  d i := PhysicalMixedTurnSource.developedUpper A B hh 0 i -
    PhysicalMixedTurnSource.developedLower A B hh 0 i
  lowerCoeff i := PhysicalMixedTurnSource.lowerRunCoeff A B hh
    (PhysicalMixedTurnSource.familySource A B 0 i)
  upperCoeff i := PhysicalMixedTurnSource.upperRunCoeff A B hh
    (PhysicalMixedTurnSource.familySource A B 0 i)
  v_ne_zero i hi := PhysicalMixedTurnSource.developedForward_ne_zero A B hh 0 i
  lowerCoeff_nonneg i hi := PhysicalMixedTurnSource.lowerRunCoeff_nonneg A B hh _
  upperCoeff_nonneg i hi := PhysicalMixedTurnSource.upperRunCoeff_nonneg A B hh _
  lower_step i hi := by
    have hs := PhysicalMixedTurnSource.developedLower_succ_sub A B hh 0 i
    calc
      _ = (PhysicalMixedTurnSource.developedLower A B hh 0 (i + 1) -
            PhysicalMixedTurnSource.developedLower A B hh 0 i) +
          PhysicalMixedTurnSource.developedLower A B hh 0 i := by abel
      _ = _ := by rw [hs]; abel
  hinge_step i hi := by
    have hu := PhysicalMixedTurnSource.developedUpper_succ_sub A B hh 0 i
    have hl := PhysicalMixedTurnSource.developedLower_succ_sub A B hh 0 i
    change PhysicalMixedTurnSource.developedUpper A B hh 0 (i + 1) -
        PhysicalMixedTurnSource.developedLower A B hh 0 (i + 1) = _
    rw [show PhysicalMixedTurnSource.developedUpper A B hh 0 (i + 1) =
        PhysicalMixedTurnSource.developedUpper A B hh 0 i +
          PhysicalMixedTurnSource.upperRunCoeff A B hh
            (PhysicalMixedTurnSource.familySource A B 0 i) •
              PhysicalMixedTurnSource.developedForward A B hh 0 i by
          calc
            _ = (PhysicalMixedTurnSource.developedUpper A B hh 0 (i + 1) -
                  PhysicalMixedTurnSource.developedUpper A B hh 0 i) +
                PhysicalMixedTurnSource.developedUpper A B hh 0 i := by abel
            _ = _ := by rw [hu]; abel,
      show PhysicalMixedTurnSource.developedLower A B hh 0 (i + 1) =
        PhysicalMixedTurnSource.developedLower A B hh 0 i +
          PhysicalMixedTurnSource.lowerRunCoeff A B hh
            (PhysicalMixedTurnSource.familySource A B 0 i) •
              PhysicalMixedTurnSource.developedForward A B hh 0 i by
          calc
            _ = (PhysicalMixedTurnSource.developedLower A B hh 0 (i + 1) -
                  PhysicalMixedTurnSource.developedLower A B hh 0 i) +
                PhysicalMixedTurnSource.developedLower A B hh 0 i := by abel
            _ = _ := by rw [hl]; abel]
    module
  orientation_neg i hi := PhysicalMixedTurnSource.developed_hinge_orientation_neg A B hh 0 i

/-- Compatible real representatives for the physical panel directions. -/
noncomputable def panelAngleLift (j : ℕ) : ℝ :=
  PhysicalMixedTurnSource.familyHeading A B hh 0 j

@[simp] theorem panelAngleLift_zero : panelAngleLift A B hh 0 = 0 :=
  PhysicalMixedTurnSource.familyHeading_zero A B hh 0

/-- Successive representatives differ by the actual physical fold at their
retained hinge.  This also applies at the final physical panel. -/
theorem panelAngleLift_succ (j : ℕ) :
    panelAngleLift A B hh (j + 1) - panelAngleLift A B hh j =
      PhysicalMixedTurnSource.intrinsicQ A B (hh := hh)
        (PhysicalMixedTurnSource.familySource A B 0 (j + 1)) :=
  PhysicalMixedTurnSource.familyHeading_succ A B hh 0 j

/-- The developed physical forward ray has exactly the chosen real lift. -/
theorem developedForward_eq_direction_lift (j : ℕ) :
    PhysicalMixedTurnSource.developedForward A B hh 0 j =
      MixedTurnSafeCut.direction (panelAngleLift A B hh j) := by
  rw [PhysicalMixedTurnSource.developedForward, panelAngleLift,
    PhysicalMixedTurnSource.planeRotation_direction]
  simp

/-- Exact real sweep, including the virtual turn after the last physical
panel.  No quotient-angle or modulo-turn statement is used. -/
theorem panelAngleLift_terminal :
    panelAngleLift A B hh (PhysicalMixedTurnSource.MechanismN A B + 1) =
      PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) :=
  PhysicalMixedTurnSource.familyHeading_full A B hh 0

/-- The actual retained hinge at height `t` in baseline panel `j`. -/
noncomputable def retainedHinge (j : ℕ) (t : ℝ) : Plane :=
  PhysicalMixedTurnSource.directDevelopedMap A B hh 0 j
    (PhysicalMixedTurnSource.faceExitAt A B hh t
      (PhysicalMixedTurnSource.familySource A B 0 j))

/-- Every retained hinge is shared pointwise by consecutive physical panels,
including the virtual terminal panel when `j = PhysicalMixedTurnSource.MechanismN A B`. -/
theorem retainedHinge_eq_next_entry (j : ℕ) (t : ℝ) :
    retainedHinge A B hh j t =
      PhysicalMixedTurnSource.directDevelopedMap A B hh 0 (j + 1)
        (PhysicalMixedTurnSource.faceEntryAt A B hh t
          (PhysicalMixedTurnSource.familySource A B 0 (j + 1))) :=
  PhysicalMixedTurnSource.directDevelopedMap_exitAt_eq_next_entryAt A B hh 0 j t

/-- The terminal lower endpoint is the literal full-affine-circuit copy of the
root lower endpoint. -/
theorem terminal_lower_is_fullCircuit :
    (baselineStrip A B hh).B (PhysicalMixedTurnSource.MechanismN A B + 1) =
      PhysicalMixedTurnSource.fullCircuit A B hh 0 ((baselineStrip A B hh).B 0) := by
  exact PhysicalMixedTurnSource.developedLower_full A B hh 0

/-- The terminal upper endpoint is the literal full-affine-circuit copy of the
root upper endpoint. -/
theorem terminal_upper_is_fullCircuit :
    (baselineStrip A B hh).B (PhysicalMixedTurnSource.MechanismN A B + 1) +
        (baselineStrip A B hh).d (PhysicalMixedTurnSource.MechanismN A B + 1) =
      PhysicalMixedTurnSource.fullCircuit A B hh 0
        ((baselineStrip A B hh).B 0 + (baselineStrip A B hh).d 0) := by
  dsimp [baselineStrip]
  rw [add_sub_cancel]
  simpa only [add_sub_cancel] using PhysicalMixedTurnSource.developedUpper_full A B hh 0

/-- Simultaneous negative RF constructs radial support for every actual
root-zero panel directly from the source. -/
theorem baselineStrip_radialSupport
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0) :
    (baselineStrip A B hh).RadialSupport
      (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)) := by
  intro i hi
  let k : Fin (PhysicalMixedTurnSource.MechanismN A B + 1) := ⟨i, by omega⟩
  have hk := PhysicalMixedTurnSource.baseline_physical_negative_RF A B hh hΔ k
  simpa [baselineStrip, k] using ⟨hk.2, hk.1⟩

/-- The positive RF branch likewise constructs positive radial support before
one global reflection/rim swap. -/
theorem baselineStrip_positiveRadialSupport
    (hΔ : 0 < PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh)) :
    (baselineStrip A B hh).PositiveRadialSupport
      (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ)) := by
  intro i hi
  let k : Fin (PhysicalMixedTurnSource.MechanismN A B + 1) := ⟨i, by omega⟩
  have hk := PhysicalMixedTurnSource.baseline_physical_positive_RF A B hh hΔ k
  simpa [baselineStrip, k] using hk

/-- The normalized positive branch is a genuine radial strip constructed from
source data, not a hypothesis record. -/
theorem reflectedBaselineStrip_radialSupport
    (hΔ : 0 < PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh)) :
    (RadialExtremalSafety.TriangularRadialStrip.reflectSwap
      (baselineStrip A B hh)).RadialSupport
        (RadialExtremalSafety.reflectPlane
          (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_gt hΔ))) :=
  RadialExtremalSafety.TriangularRadialStrip.reflectSwap_radialSupport
    (baselineStrip_positiveRadialSupport A B hh hΔ)

/-- The zero-longitudinal edge of every baseline panel is its developed
physical entry segment, pointwise in height. -/
theorem baselineStrip_point_zero (j : ℕ) (t : ℝ) :
    (baselineStrip A B hh).point j 0 t =
      PhysicalMixedTurnSource.directDevelopedMap A B hh 0 j
        (PhysicalMixedTurnSource.faceEntryAt A B hh t
          (PhysicalMixedTurnSource.familySource A B 0 j)) := by
  let F := PhysicalMixedTurnSource.directDevelopedMap A B hh 0 j
  let a := PhysicalMixedTurnSource.faceEntryLower A B hh
    (PhysicalMixedTurnSource.familySource A B 0 j)
  let b := PhysicalMixedTurnSource.faceEntryUpper A B hh
    (PhysicalMixedTurnSource.familySource A B 0 j)
  have hmap : F ((1 - t) • a + t • b) = F a + t • (F b - F a) := by
    rw [show (1 - t) • a + t • b = t • (b - a) +ᵥ a by
      simp [vadd_eq_add]
      module]
    rw [F.map_vadd, map_smul]
    have hv := F.map_vsub b a
    change F.linearIsometry (b - a) = F b - F a at hv
    rw [hv]
    simp [vadd_eq_add, add_comm]
  simp only [RadialExtremalSafety.TriangularRadialStrip.point, baselineStrip,
    zero_mul, zero_smul, add_zero]
  change PhysicalMixedTurnSource.developedLower A B hh 0 j +
      t • (PhysicalMixedTurnSource.developedUpper A B hh 0 j -
        PhysicalMixedTurnSource.developedLower A B hh 0 j) = _
  rw [PhysicalMixedTurnSource.faceEntryAt, AffineMap.lineMap_apply_module]
  change _ = F ((1 - t) • a + t • b)
  rw [hmap]
  rfl

/-- The one-longitudinal edge of every baseline panel is its developed
physical exit segment, pointwise in height. -/
theorem baselineStrip_point_one (j : ℕ) (t : ℝ) :
    (baselineStrip A B hh).point j 1 t = retainedHinge A B hh j t := by
  simp only [RadialExtremalSafety.TriangularRadialStrip.point, baselineStrip,
    one_mul]
  change PhysicalMixedTurnSource.developedLower A B hh 0 j +
      t • (PhysicalMixedTurnSource.developedUpper A B hh 0 j -
        PhysicalMixedTurnSource.developedLower A B hh 0 j) +
      ((1 - t) * PhysicalMixedTurnSource.lowerRunCoeff A B hh
          (PhysicalMixedTurnSource.familySource A B 0 j) +
        t * PhysicalMixedTurnSource.upperRunCoeff A B hh
          (PhysicalMixedTurnSource.familySource A B 0 j)) •
        PhysicalMixedTurnSource.developedForward A B hh 0 j = _
  unfold retainedHinge
  let F := PhysicalMixedTurnSource.directDevelopedMap A B hh 0 j
  let a := PhysicalMixedTurnSource.faceExitLower A B hh
    (PhysicalMixedTurnSource.familySource A B 0 j)
  let b := PhysicalMixedTurnSource.faceExitUpper A B hh
    (PhysicalMixedTurnSource.familySource A B 0 j)
  have hmap : F ((1 - t) • a + t • b) = F a + t • (F b - F a) := by
    rw [show (1 - t) • a + t • b = t • (b - a) +ᵥ a by
      simp [vadd_eq_add]
      module]
    rw [F.map_vadd, map_smul]
    have hv := F.map_vsub b a
    change F.linearIsometry (b - a) = F b - F a at hv
    rw [hv]
    simp [vadd_eq_add, add_comm]
  rw [PhysicalMixedTurnSource.faceExitAt, AffineMap.lineMap_apply_module]
  change _ = F ((1 - t) • a + t • b)
  rw [hmap]
  have hl := PhysicalMixedTurnSource.developedLower_run A B hh 0 j
  have hu := PhysicalMixedTurnSource.developedUpper_run A B hh 0 j
  change F a - PhysicalMixedTurnSource.developedLower A B hh 0 j = _ at hl
  change F b - PhysicalMixedTurnSource.developedUpper A B hh 0 j = _ at hu
  have hFa : F a = PhysicalMixedTurnSource.developedLower A B hh 0 j +
      PhysicalMixedTurnSource.lowerRunCoeff A B hh
        (PhysicalMixedTurnSource.familySource A B 0 j) •
          PhysicalMixedTurnSource.developedForward A B hh 0 j := by
    calc
      F a = (F a - PhysicalMixedTurnSource.developedLower A B hh 0 j) +
          PhysicalMixedTurnSource.developedLower A B hh 0 j := by abel
      _ = _ := by rw [hl]; abel
  have hFb : F b = PhysicalMixedTurnSource.developedUpper A B hh 0 j +
      PhysicalMixedTurnSource.upperRunCoeff A B hh
        (PhysicalMixedTurnSource.familySource A B 0 j) •
          PhysicalMixedTurnSource.developedForward A B hh 0 j := by
    calc
      F b = (F b - PhysicalMixedTurnSource.developedUpper A B hh 0 j) +
          PhysicalMixedTurnSource.developedUpper A B hh 0 j := by abel
      _ = _ := by rw [hu]; abel
  rw [hFa, hFb]
  module

/-- The terminal edge of the last physical panel is the literal full-circuit
copy of the root entry edge, pointwise in height. -/
theorem terminalPanelPoint_eq_fullCircuit_rootPoint (t : ℝ) :
    (baselineStrip A B hh).point (PhysicalMixedTurnSource.MechanismN A B) 1 t =
      PhysicalMixedTurnSource.fullCircuit A B hh 0
        ((baselineStrip A B hh).point 0 0 t) := by
  let N := PhysicalMixedTurnSource.MechanismN A B
  calc
    (baselineStrip A B hh).point N 1 t = retainedHinge A B hh N t :=
      baselineStrip_point_one A B hh N t
    _ = PhysicalMixedTurnSource.directDevelopedMap A B hh 0 (N + 1)
        (PhysicalMixedTurnSource.faceEntryAt A B hh t
          (PhysicalMixedTurnSource.familySource A B 0 (N + 1))) :=
      retainedHinge_eq_next_entry A B hh N t
    _ = (baselineStrip A B hh).point (N + 1) 0 t :=
      (baselineStrip_point_zero A B hh (N + 1) t).symm
    _ = PhysicalMixedTurnSource.fullCircuit A B hh 0
        ((baselineStrip A B hh).point 0 0 t) := by
      let G := PhysicalMixedTurnSource.fullCircuit A B hh 0
      let L := (baselineStrip A B hh).B 0
      let U := (baselineStrip A B hh).B 0 + (baselineStrip A B hh).d 0
      have hmap : G (L + t • (U - L)) = G L + t • (G U - G L) := by
        rw [show L + t • (U - L) = t • (U - L) +ᵥ L by
          simp [vadd_eq_add, add_comm]]
        rw [G.map_vadd, map_smul]
        have hv := G.map_vsub U L
        change G.linearIsometry (U - L) = G U - G L at hv
        rw [hv]
        simp [vadd_eq_add, add_comm]
      simp only [RadialExtremalSafety.TriangularRadialStrip.point,
        zero_mul, zero_smul, add_zero]
      have hUL : U - L = (baselineStrip A B hh).d 0 := by
        dsimp [U, L]
        abel
      change (baselineStrip A B hh).B (N + 1) +
          t • (baselineStrip A B hh).d (N + 1) =
        G (L + t • (baselineStrip A B hh).d 0)
      rw [← hUL, hmap, show (baselineStrip A B hh).B (N + 1) = G L by
          exact terminal_lower_is_fullCircuit A B hh,
        show (baselineStrip A B hh).d (N + 1) = G U - G L by
          have hu := terminal_upper_is_fullCircuit A B hh
          change (baselineStrip A B hh).B (N + 1) +
              (baselineStrip A B hh).d (N + 1) = G U at hu
          rw [terminal_lower_is_fullCircuit A B hh] at hu
          calc
            (baselineStrip A B hh).d (N + 1) =
                (G L + (baselineStrip A B hh).d (N + 1)) - G L := by abel
            _ = G U - G L := by rw [hu]]

/-- The physical cut seam in the root copy, with its original height
parameter. -/
noncomputable def rootSeam (t : ℝ) : Plane :=
  PhysicalMixedTurnSource.directDevelopedMap A B hh 0 0
    (PhysicalMixedTurnSource.faceEntryAt A B hh t
      (PhysicalMixedTurnSource.familySource A B 0 0))

/-- The facing copy of that same physical seam after one complete translated
affine circuit.  This definition deliberately keeps the actual `H`, rather
than replacing it by a modular source label. -/
noncomputable def terminalSeam (t : ℝ) : Plane :=
  PhysicalMixedTurnSource.fullCircuit A B hh 0 (rootSeam A B hh t)

/-- The two facing parametrizations are root/terminal copies of the SAME seam
under the literal translated affine circuit `H`. -/
theorem terminalSeam_eq_fullCircuit (t : ℝ) :
    terminalSeam A B hh t =
      PhysicalMixedTurnSource.fullCircuit A B hh 0 (rootSeam A B hh t) := rfl

/-- Around the genuine pole the complete affine circuit is exactly rotation by
the real total sweep. -/
theorem fullCircuit_sub_pole
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) ≠ 0)
    (x : Plane) :
    PhysicalMixedTurnSource.fullCircuit A B hh 0 x -
        PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ =
      PhysicalMixedTurnSource.planeRotation
        (PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh))
        (x - PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ) := by
  have hd := PhysicalMixedTurnSource.fullCircuit_sub_eq_rotation_sub
    A B hh 0 hΔ x
  calc
    _ = (PhysicalMixedTurnSource.fullCircuit A B hh 0 x - x) +
        (x - PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ) := by abel
    _ = _ := by rw [hd]; abel

/-- A root ray of lift `α` is carried to the terminal ray of lift `α + Δ`,
with exactly the same radius and with the actual full-circuit translation. -/
theorem fullCircuit_ray_copy
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) ≠ 0)
    {x : Plane} {α r : ℝ}
    (hx : x - PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ =
      r • MixedTurnSafeCut.direction α) :
    PhysicalMixedTurnSource.fullCircuit A B hh 0 x -
        PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ =
      r • MixedTurnSafeCut.direction
        (α + PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh)) := by
  rw [fullCircuit_sub_pole A B hh hΔ, hx, map_smul,
    PhysicalMixedTurnSource.planeRotation_direction]
  congr 2
  ring

/-- Cross-gap radius comparisons are equivalent in both seam-angle directions:
applying the actual `H` copy to both points neither creates nor destroys a
strict radius ordering. -/
theorem fullCircuit_norm_lt_iff
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) ≠ 0)
    (x y : Plane) :
    ‖PhysicalMixedTurnSource.fullCircuit A B hh 0 x -
        PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ‖ <
      ‖PhysicalMixedTurnSource.fullCircuit A B hh 0 y -
        PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ‖ ↔
    ‖x - PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ‖ <
      ‖y - PhysicalMixedTurnSource.circuitPole A B hh 0 hΔ‖ := by
  rw [fullCircuit_sub_pole A B hh hΔ, fullCircuit_sub_pole A B hh hΔ,
    (PhysicalMixedTurnSource.planeRotation _).norm_map,
    (PhysicalMixedTurnSource.planeRotation _).norm_map]

/-- Coordinates of `z` after rotation by `-θ`.  Its imaginary coordinate is
`det (direction θ) z`; this is the panel-local half-plane coordinate used to
choose a real polar lift without any global angular-window assumption. -/
noncomputable def panelRelativeComplex (θ : ℝ) (z : Plane) : ℂ :=
  ⟨Real.cos θ * z 0 + Real.sin θ * z 1,
    -Real.sin θ * z 0 + Real.cos θ * z 1⟩

@[simp] theorem panelRelativeComplex_im (θ : ℝ) (z : Plane) :
    (panelRelativeComplex θ z).im =
      MixedTurnSafeCut.det (MixedTurnSafeCut.direction θ) z := by
  simp [panelRelativeComplex, MixedTurnSafeCut.det, MixedTurnSafeCut.direction]
  ring

/-- The source-computed real polar lift of a material point in panel `i`.  The
principal relative argument is taken only after rotating into that panel's own
strict radial half-plane. -/
noncomputable def panelPointPolarLift
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    (i : ℕ) (s t : ℝ) : ℝ :=
  panelAngleLift A B hh i + Complex.arg
    (panelRelativeComplex (panelAngleLift A B hh i)
      ((baselineStrip A B hh).point i s t -
        PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)))

/-- The panel-relative complex coordinate of every supported material point is
strictly in the upper half-plane. -/
theorem panelRelativeComplex_point_im_pos
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    {i : ℕ} (hi : i ≤ PhysicalMixedTurnSource.MechanismN A B)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < (panelRelativeComplex (panelAngleLift A B hh i)
      ((baselineStrip A B hh).point i s t -
        PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))).im := by
  have hsupport := RadialExtremalSafety.TriangularRadialStrip.support_point
    (baselineStrip_radialSupport A B hh hΔ) hi hs ht
  rw [panelRelativeComplex_im]
  rw [← developedForward_eq_direction_lift A B hh i]
  change MixedTurnSafeCut.det
    ((baselineStrip A B hh).point i s t -
      PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
    (PhysicalMixedTurnSource.developedForward A B hh 0 i) < 0 at hsupport
  have hanti : MixedTurnSafeCut.det
      (PhysicalMixedTurnSource.developedForward A B hh 0 i)
      ((baselineStrip A B hh).point i s t -
        PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)) =
    -MixedTurnSafeCut.det
      ((baselineStrip A B hh).point i s t -
        PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
      (PhysicalMixedTurnSource.developedForward A B hh 0 i) := by
    simp [MixedTurnSafeCut.det]
    ring
  rw [hanti]
  exact neg_pos.mpr hsupport

/-- Physical radial support puts every point of a source panel in its own open
polar window `(heading, heading + π)`.  This source invariant is stronger than
abstract `RadialSupport`: the window is tied to the actual compatible heading
lift, so the Task34 strip counterexample cannot be assigned arbitrary sheet
labels. -/
theorem panelPointPolarLift_mem_window
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    {i : ℕ} (hi : i ≤ PhysicalMixedTurnSource.MechanismN A B)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    panelAngleLift A B hh i < panelPointPolarLift A B hh hΔ i s t ∧
      panelPointPolarLift A B hh hΔ i s t < panelAngleLift A B hh i + Real.pi := by
  let O := PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)
  let z := (baselineStrip A B hh).point i s t - O
  let w := panelRelativeComplex (panelAngleLift A B hh i) z
  have hsupport := RadialExtremalSafety.TriangularRadialStrip.support_point
    (baselineStrip_radialSupport A B hh hΔ) hi hs ht
  have him : 0 < w.im := by
    rw [show w.im = MixedTurnSafeCut.det
      (MixedTurnSafeCut.direction (panelAngleLift A B hh i)) z by
        simp [w, panelRelativeComplex_im]]
    rw [← developedForward_eq_direction_lift A B hh i]
    change MixedTurnSafeCut.det z
      (PhysicalMixedTurnSource.developedForward A B hh 0 i) < 0 at hsupport
    have hanti : MixedTurnSafeCut.det
        (PhysicalMixedTurnSource.developedForward A B hh 0 i) z =
      -MixedTurnSafeCut.det z
        (PhysicalMixedTurnSource.developedForward A B hh 0 i) := by
      simp [MixedTurnSafeCut.det]
      ring
    rw [hanti]
    exact neg_pos.mpr hsupport
  have harg0 : 0 < Complex.arg w := by
    have hnonneg : 0 ≤ Complex.arg w := Complex.arg_nonneg_iff.2 him.le
    exact lt_of_le_of_ne hnonneg (by
      intro he
      have hz := Complex.arg_eq_zero_iff.mp he.symm
      linarith [hz.2])
  have hargpi : Complex.arg w < Real.pi :=
    Complex.arg_lt_pi_iff.2 (Or.inr (ne_of_gt him))
  simpa [panelPointPolarLift, O, z, w] using ⟨harg0, hargpi⟩

/-- The panel-local lift is an actual real polar representative, not merely a
window label.  This algebraic form is used to compare representatives at a
retained hinge. -/
theorem panelPointPolarLift_decomposition
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    {i : ℕ} (hi : i ≤ PhysicalMixedTurnSource.MechanismN A B)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    let z := (baselineStrip A B hh).point i s t -
      PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)
    z = ‖z‖ • MixedTurnSafeCut.direction
      (panelPointPolarLift A B hh hΔ i s t) := by
  let O := PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)
  let z := (baselineStrip A B hh).point i s t - O
  let θ := panelAngleLift A B hh i
  let w := panelRelativeComplex θ z
  have hz : z ≠ 0 := sub_ne_zero.mpr
    (RadialExtremalSafety.TriangularRadialStrip.point_ne_pole
      (baselineStrip_radialSupport A B hh hΔ) hi hs ht)
  have hw : w ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    have him := congrArg Complex.im hzero
    norm_num at hre him
    have hz0 : z 0 = 0 := by
      calc
        z 0 = (Real.cos θ ^ 2 + Real.sin θ ^ 2) * z 0 := by
          rw [add_comm, Real.sin_sq_add_cos_sq]; ring
        _ = Real.cos θ * w.re - Real.sin θ * w.im := by
          dsimp [w, panelRelativeComplex]
          ring
        _ = 0 := by rw [hre, him]; ring
    have hz1 : z 1 = 0 := by
      calc
        z 1 = (Real.cos θ ^ 2 + Real.sin θ ^ 2) * z 1 := by
          rw [add_comm, Real.sin_sq_add_cos_sq]; ring
        _ = Real.sin θ * w.re + Real.cos θ * w.im := by
          dsimp [w, panelRelativeComplex]
          ring
        _ = 0 := by rw [hre, him]; ring
    apply hz
    ext k
    fin_cases k
    · simpa using hz0
    · simpa using hz1
  have hnorm : ‖w‖ = ‖z‖ := by
    simp only [Complex.norm_def, Complex.normSq_apply, w, panelRelativeComplex,
      EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
    congr 1
    calc
      _ = (Real.cos θ ^ 2 + Real.sin θ ^ 2) *
          (z 0 ^ 2 + z 1 ^ 2) := by ring
      _ = _ := by rw [add_comm, Real.sin_sq_add_cos_sq, one_mul]
  have hcos := Complex.norm_mul_cos_arg w
  have hsin := Complex.norm_mul_sin_arg w
  change ‖w‖ * Real.cos (Complex.arg w) = w.re at hcos
  change ‖w‖ * Real.sin (Complex.arg w) = w.im at hsin
  change z = ‖z‖ • MixedTurnSafeCut.direction
    (θ + Complex.arg w)
  rw [← hnorm]
  ext k
  fin_cases k
  · change z 0 = ‖w‖ * Real.cos (θ + Complex.arg w)
    rw [Real.cos_add]
    calc
      z 0 = Real.cos θ * w.re - Real.sin θ * w.im := by
        dsimp [w, panelRelativeComplex]
        symm
        calc
          _ = (Real.cos θ ^ 2 + Real.sin θ ^ 2) * z 0 := by ring
          _ = z 0 := by rw [add_comm, Real.sin_sq_add_cos_sq, one_mul]
      _ = _ := by rw [← hcos, ← hsin]; ring
  · change z 1 = ‖w‖ * Real.sin (θ + Complex.arg w)
    rw [Real.sin_add]
    calc
      z 1 = Real.sin θ * w.re + Real.cos θ * w.im := by
        dsimp [w, panelRelativeComplex]
        symm
        calc
          _ = (Real.cos θ ^ 2 + Real.sin θ ^ 2) * z 1 := by ring
          _ = z 1 := by rw [add_comm, Real.sin_sq_add_cos_sq, one_mul]
      _ = _ := by rw [← hcos, ← hsin]; ring

/-- Equality of unit directions is equality in the real angle quotient. -/
lemma angle_eq_mod_two_pi_of_direction_eq {α β : ℝ}
    (hdir : MixedTurnSafeCut.direction α = MixedTurnSafeCut.direction β) :
    (α : Real.Angle) = (β : Real.Angle) := by
  apply Real.Angle.cos_sin_inj
  · have h := congrArg (fun z : Plane => z 0) hdir
    simpa [MixedTurnSafeCut.direction] using h
  · have h := congrArg (fun z : Plane => z 1) hdir
    simpa [MixedTurnSafeCut.direction] using h

/-- The local source branches agree as REAL representatives at every retained
physical hinge.  The proof uses the source turn bound to rule out a hidden
`2π` jump. -/
theorem panelPointPolarLift_hinge
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    {i : ℕ} (hi : i < PhysicalMixedTurnSource.MechanismN A B)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    panelPointPolarLift A B hh hΔ i 1 t =
      panelPointPolarLift A B hh hΔ (i + 1) 0 t := by
  let S := baselineStrip A B hh
  let O := PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)
  let x := S.point i 1 t
  have hx : x = S.point (i + 1) 0 t := by
    dsimp [x, S]
    rw [RadialExtremalSafety.TriangularRadialStrip.point,
      RadialExtremalSafety.TriangularRadialStrip.point,
      (baselineStrip A B hh).lower_step i hi,
      (baselineStrip A B hh).hinge_step i hi]
    module
  have hdec₁ := panelPointPolarLift_decomposition A B hh hΔ (i := i) (by omega)
    (s := (1 : ℝ)) (t := t) (by norm_num) ht
  have hdec₂ := panelPointPolarLift_decomposition A B hh hΔ (i := i + 1) (by omega)
    (s := (0 : ℝ)) (t := t) (by norm_num) ht
  change x - O = ‖x - O‖ • MixedTurnSafeCut.direction
      (panelPointPolarLift A B hh hΔ i 1 t) at hdec₁
  change S.point (i + 1) 0 t - O = ‖S.point (i + 1) 0 t - O‖ •
      MixedTurnSafeCut.direction
        (panelPointPolarLift A B hh hΔ (i + 1) 0 t) at hdec₂
  rw [← hx] at hdec₂
  have hr : 0 < ‖x - O‖ := norm_pos_iff.mpr (sub_ne_zero.mpr
    (RadialExtremalSafety.TriangularRadialStrip.point_ne_pole
      (baselineStrip_radialSupport A B hh hΔ) (by omega)
      (by norm_num) ht))
  have hdir : MixedTurnSafeCut.direction
        (panelPointPolarLift A B hh hΔ i 1 t) =
      MixedTurnSafeCut.direction
        (panelPointPolarLift A B hh hΔ (i + 1) 0 t) := by
    apply smul_right_injective Plane (ne_of_gt hr)
    change ‖x - O‖ • MixedTurnSafeCut.direction
        (panelPointPolarLift A B hh hΔ i 1 t) =
      ‖x - O‖ • MixedTurnSafeCut.direction
        (panelPointPolarLift A B hh hΔ (i + 1) 0 t)
    exact hdec₁.symm.trans hdec₂
  have hang := angle_eq_mod_two_pi_of_direction_eq hdir
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hang.symm
  have hw₁ := panelPointPolarLift_mem_window A B hh hΔ (i := i) (by omega)
    (s := (1 : ℝ)) (t := t) (by norm_num) ht
  have hw₂ := panelPointPolarLift_mem_window A B hh hΔ (i := i + 1) (by omega)
    (s := (0 : ℝ)) (t := t) (by norm_num) ht
  have hqabs := PhysicalMixedTurnSource.abs_intrinsicQ_lt_middleExteriorTurn
    A B hh (PhysicalMixedTurnSource.familySource A B 0 (i + 1))
  have hqpi := PhysicalMixedTurnSource.middleExteriorTurn_lt_pi A B
    (PhysicalMixedTurnSource.familySource A B 0 (i + 1))
  have hq : |panelAngleLift A B hh (i + 1) - panelAngleLift A B hh i| <
      Real.pi := by
    rw [panelAngleLift_succ A B hh i]
    exact hqabs.trans hqpi
  have hdiff : -2 * Real.pi <
        panelPointPolarLift A B hh hΔ (i + 1) 0 t -
          panelPointPolarLift A B hh hΔ i 1 t ∧
      panelPointPolarLift A B hh hΔ (i + 1) 0 t -
          panelPointPolarLift A B hh hΔ i 1 t < 2 * Real.pi := by
    rw [abs_lt] at hq
    constructor <;> linarith
  have hk0 : k = 0 := by
    by_contra hk0
    rcases lt_or_gt_of_ne hk0 with hkneg | hkpos
    · have hk_le : k ≤ -1 := by omega
      have hk_le' : (k : ℝ) ≤ -1 := by exact_mod_cast hk_le
      nlinarith [Real.pi_pos]
    · have hk_ge : (1 : ℤ) ≤ k := by omega
      have hk_ge' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge
      nlinarith [Real.pi_pos]
  rw [hk0] at hk
  norm_num at hk
  linarith

/-- At every genuine interior physical height, the real panel lift is strictly
clockwise as the longitudinal parameter increases. -/
theorem panelPointPolarLift_strictAnti
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    {i : ℕ} (hi : i ≤ PhysicalMixedTurnSource.MechanismN A B)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    StrictAntiOn (fun s => panelPointPolarLift A B hh hΔ i s t)
      (Icc (0 : ℝ) 1) := by
  intro s₁ hs₁ s₂ hs₂ hslt
  let S := baselineStrip A B hh
  let O := PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)
  let z₁ := S.point i s₁ t - O
  let z₂ := S.point i s₂ t - O
  let φ₁ := panelPointPolarLift A B hh hΔ i s₁ t
  let φ₂ := panelPointPolarLift A B hh hΔ i s₂ t
  have hρ : 0 < (1 - t) * S.lowerCoeff i + t * S.upperCoeff i := by
    change 0 < PhysicalMixedTurnSource.retainedLowerRunCoeff A B hh t
      (PhysicalMixedTurnSource.familySource A B 0 i)
    exact PhysicalMixedTurnSource.retainedLowerRunCoeff_pos_of_mem_Ioo
      A B hh ht _
  have hstep : z₂ = z₁ + ((s₂ - s₁) *
      ((1 - t) * S.lowerCoeff i + t * S.upperCoeff i)) • S.v i := by
    dsimp [z₁, z₂, S]
    simp only [RadialExtremalSafety.TriangularRadialStrip.point]
    module
  have hsupport := RadialExtremalSafety.TriangularRadialStrip.support_point
    (baselineStrip_radialSupport A B hh hΔ) hi hs₁ ⟨ht.1.le, ht.2.le⟩
  have hc : 0 < (s₂ - s₁) *
      ((1 - t) * S.lowerCoeff i + t * S.upperCoeff i) :=
    mul_pos (sub_pos.mpr hslt) hρ
  have hdetneg : MixedTurnSafeCut.det z₁ z₂ < 0 := by
    rw [hstep]
    have he : MixedTurnSafeCut.det z₁
        (z₁ + ((s₂ - s₁) *
          ((1 - t) * S.lowerCoeff i + t * S.upperCoeff i)) • S.v i) =
        ((s₂ - s₁) * ((1 - t) * S.lowerCoeff i + t * S.upperCoeff i)) *
          MixedTurnSafeCut.det z₁ (S.v i) := by
      simp [MixedTurnSafeCut.det]
      ring
    rw [he]
    exact mul_neg_of_pos_of_neg hc hsupport
  have hdec₁ := panelPointPolarLift_decomposition A B hh hΔ (i := i) hi hs₁ ⟨ht.1.le, ht.2.le⟩
  have hdec₂ := panelPointPolarLift_decomposition A B hh hΔ (i := i) hi hs₂ ⟨ht.1.le, ht.2.le⟩
  change z₁ = ‖z₁‖ • MixedTurnSafeCut.direction φ₁ at hdec₁
  change z₂ = ‖z₂‖ • MixedTurnSafeCut.direction φ₂ at hdec₂
  have hr₁ : 0 < ‖z₁‖ := norm_pos_iff.mpr (by
    dsimp [z₁, S, O]
    exact sub_ne_zero.mpr
      (RadialExtremalSafety.TriangularRadialStrip.point_ne_pole
        (baselineStrip_radialSupport A B hh hΔ) hi hs₁ ⟨ht.1.le, ht.2.le⟩))
  have hr₂ : 0 < ‖z₂‖ := norm_pos_iff.mpr (by
    dsimp [z₂, S, O]
    exact sub_ne_zero.mpr
      (RadialExtremalSafety.TriangularRadialStrip.point_ne_pole
        (baselineStrip_radialSupport A B hh hΔ) hi hs₂ ⟨ht.1.le, ht.2.le⟩))
  have hw₁ := panelPointPolarLift_mem_window A B hh hΔ (i := i) hi hs₁ ⟨ht.1.le, ht.2.le⟩
  have hw₂ := panelPointPolarLift_mem_window A B hh hΔ (i := i) hi hs₂ ⟨ht.1.le, ht.2.le⟩
  by_contra hnot
  have hφle : φ₁ ≤ φ₂ := le_of_not_gt hnot
  have hδ0 : 0 ≤ φ₂ - φ₁ := sub_nonneg.mpr hφle
  have hδπ : φ₂ - φ₁ ≤ Real.pi := by
    dsimp [φ₁, φ₂] at *
    linarith
  have hsin : 0 ≤ Real.sin (φ₂ - φ₁) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hδ0 hδπ
  have hdetdir : MixedTurnSafeCut.det
      (MixedTurnSafeCut.direction φ₁) (MixedTurnSafeCut.direction φ₂) =
      Real.sin (φ₂ - φ₁) := by
    simp [MixedTurnSafeCut.det, MixedTurnSafeCut.direction, Real.sin_sub]
    ring
  rw [hdec₁, hdec₂, RadialExtremalSafety.det_smul_left,
    RadialExtremalSafety.det_smul_right, hdetdir] at hdetneg
  have : 0 ≤ ‖z₁‖ * (‖z₂‖ * Real.sin (φ₂ - φ₁)) :=
    mul_nonneg hr₁.le (mul_nonneg hr₂.le hsin)
  linarith

/-- One physical panel realizes exactly the closed interval between its two
compatible endpoint lifts at every interior height. -/
theorem panelPointPolarLift_image_Icc
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    {i : ℕ} (hi : i ≤ PhysicalMixedTurnSource.MechanismN A B)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (fun s => panelPointPolarLift A B hh hΔ i s t) '' Icc (0 : ℝ) 1 =
      Icc (panelPointPolarLift A B hh hΔ i 1 t)
        (panelPointPolarLift A B hh hΔ i 0 t) := by
  let f : ℝ → ℝ := fun s => panelPointPolarLift A B hh hΔ i s t
  have hanti : StrictAntiOn f (Icc (0 : ℝ) 1) :=
    panelPointPolarLift_strictAnti A B hh hΔ hi ht
  let w : ℝ → ℂ := fun s =>
    panelRelativeComplex (panelAngleLift A B hh i)
      ((baselineStrip A B hh).point i s t -
        PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
  have hre : Continuous (fun s => (w s).re) := by
    dsimp [w, panelRelativeComplex,
      RadialExtremalSafety.TriangularRadialStrip.point]
    fun_prop
  have him : Continuous (fun s => (w s).im) := by
    dsimp [w, panelRelativeComplex,
      RadialExtremalSafety.TriangularRadialStrip.point]
    fun_prop
  have hwcont : Continuous w := by
    have hc : Continuous (fun s => ((w s).re : ℂ) + ((w s).im : ℂ) * Complex.I) :=
      (Complex.continuous_ofReal.comp hre).add
        ((Complex.continuous_ofReal.comp him).mul continuous_const)
    convert hc using 1
    funext s
    apply Complex.ext <;> simp
  have hfcont : ContinuousOn f (Icc (0 : ℝ) 1) := by
    intro s hs
    have hslit : w s ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inr
        (ne_of_gt (panelRelativeComplex_point_im_pos A B hh hΔ hi hs
          ⟨ht.1.le, ht.2.le⟩)))
    have harg : ContinuousAt (fun r => (w r).arg) s :=
      (Complex.continuousAt_arg hslit).comp hwcont.continuousAt
    exact (continuousAt_const.add harg).continuousWithinAt
  apply Set.Subset.antisymm
  · rintro φ ⟨s, hs, rfl⟩
    exact ⟨hanti.antitoneOn hs (by norm_num) hs.2,
      hanti.antitoneOn (by norm_num) hs hs.1⟩
  · exact intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num) hfcont

/-- The complete set of compatible real polar lifts realized by the cut-open
strip at physical height `t`. -/
def longitudinalLiftSet
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    (t : ℝ) : Set ℝ :=
  {φ | ∃ i ≤ PhysicalMixedTurnSource.MechanismN A B,
    ∃ s ∈ Icc (0 : ℝ) 1, φ = panelPointPolarLift A B hh hΔ i s t}

/-- The selected seam's compatible real polar lift. -/
def longitudinalAlpha
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    (t : ℝ) : ℝ := panelPointPolarLift A B hh hΔ 0 0 t

/-- The compatible lift of the terminal seam is exactly the selected seam
lift plus the real total defect (not merely equal modulo `2π`). -/
theorem panelPointPolarLift_terminal_eq_alpha_add_delta
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    panelPointPolarLift A B hh hΔ
        (PhysicalMixedTurnSource.MechanismN A B) 1 t =
      longitudinalAlpha A B hh hΔ t +
        PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) := by
  let N := PhysicalMixedTurnSource.MechanismN A B
  let O := PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)
  let x := (baselineStrip A B hh).point 0 0 t
  let y := (baselineStrip A B hh).point N 1 t
  let α := longitudinalAlpha A B hh hΔ t
  let φ := panelPointPolarLift A B hh hΔ N 1 t
  have hroot := panelPointPolarLift_decomposition A B hh hΔ
    (i := 0) (s := (0 : ℝ)) (t := t) (by omega) (by norm_num) ht
  change x - O = ‖x - O‖ • MixedTurnSafeCut.direction α at hroot
  have hcopy := fullCircuit_ray_copy A B hh (ne_of_lt hΔ) hroot
  have hy : y = PhysicalMixedTurnSource.fullCircuit A B hh 0 x := by
    exact terminalPanelPoint_eq_fullCircuit_rootPoint A B hh t
  rw [← hy] at hcopy
  have hterm := panelPointPolarLift_decomposition A B hh hΔ
    (i := N) (s := (1 : ℝ)) (t := t) (by omega) (by norm_num) ht
  change y - O = ‖y - O‖ • MixedTurnSafeCut.direction φ at hterm
  have hnorm : ‖y - O‖ = ‖x - O‖ := by
    rw [hy, fullCircuit_sub_pole A B hh (ne_of_lt hΔ)]
    exact (PhysicalMixedTurnSource.planeRotation _).norm_map _
  have hdir : MixedTurnSafeCut.direction φ =
      MixedTurnSafeCut.direction
        (α + PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh)) := by
    apply smul_right_injective Plane
      (norm_ne_zero_iff.mpr (by
        dsimp [x, O]
        exact sub_ne_zero.mpr
          (RadialExtremalSafety.TriangularRadialStrip.point_ne_pole
            (baselineStrip_radialSupport A B hh hΔ) (i := 0)
              (s := (0 : ℝ)) (t := t) (by omega) (by norm_num) ht)))
    change ‖x - O‖ • MixedTurnSafeCut.direction φ =
      ‖x - O‖ • MixedTurnSafeCut.direction
        (α + PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh))
    calc
      _ = ‖y - O‖ • MixedTurnSafeCut.direction φ := by rw [hnorm]
      _ = y - O := hterm.symm
      _ = ‖x - O‖ • MixedTurnSafeCut.direction
          (α + PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh)) := by
        exact hcopy
  have hang := angle_eq_mod_two_pi_of_direction_eq hdir
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hang.symm
  have hwφ := panelPointPolarLift_mem_window A B hh hΔ
    (i := N) (s := (1 : ℝ)) (t := t) (by omega) (by norm_num) ht
  have hwα := panelPointPolarLift_mem_window A B hh hΔ
    (i := 0) (s := (0 : ℝ)) (t := t) (by omega) (by norm_num) ht
  have hq := PhysicalMixedTurnSource.abs_intrinsicQ_lt_middleExteriorTurn
    A B hh (PhysicalMixedTurnSource.familySource A B 0 (N + 1))
  have hmid := PhysicalMixedTurnSource.middleExteriorTurn_lt_pi A B
    (PhysicalMixedTurnSource.familySource A B 0 (N + 1))
  have hstep := panelAngleLift_succ A B hh N
  have hterminal := panelAngleLift_terminal A B hh
  have hgap : |PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) -
      panelAngleLift A B hh N| < Real.pi := by
    rw [← hterminal]
    rw [show N + 1 = PhysicalMixedTurnSource.MechanismN A B + 1 by rfl]
    rw [hstep]
    exact lt_trans hq hmid
  have hdiff : -2 * Real.pi < φ -
        (α + PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh)) ∧
      φ - (α + PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh)) <
        2 * Real.pi := by
    simp only [panelAngleLift_zero] at hwα
    dsimp [φ, α, longitudinalAlpha, N] at *
    rw [abs_lt] at hgap
    constructor <;> linarith
  have hk0 : k = 0 := by
    by_contra hkne
    rcases lt_or_gt_of_ne hkne with hkneg | hkpos
    · have hk_le : k ≤ -1 := by omega
      have hk_le' : (k : ℝ) ≤ -1 := by exact_mod_cast hk_le
      nlinarith [Real.pi_pos]
    · have hk_ge : (1 : ℤ) ≤ k := by omega
      have hk_ge' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge
      nlinarith [Real.pi_pos]
  rw [hk0] at hk
  norm_num at hk
  linarith

/-- Positive angular length of the cut-open strip in the negative-defect
branch. -/
def longitudinalLength : ℝ :=
  -PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh)

 theorem longitudinalLength_pos
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0) :
    0 < longitudinalLength A B hh := by
  exact neg_pos.mpr hΔ

theorem longitudinalLength_lt_two_pi :
    longitudinalLength A B hh < 2 * Real.pi := by
  have habs := PhysicalMixedTurnSource.abs_intrinsicDelta_lt_two_pi A B hh
  unfold longitudinalLength
  rcases le_total 0 (PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh)) with h | h
  · rw [abs_of_nonneg h] at habs
    linarith
  · rw [abs_of_nonpos h] at habs
    exact habs

/-- The global fixed-height lift set is one closed real interval.  Its lower
endpoint is the terminal seam lift and its upper endpoint is the selected
(root) seam lift. -/
theorem longitudinalLiftSet_eq_endpointInterval
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    longitudinalLiftSet A B hh hΔ t =
      Icc (panelPointPolarLift A B hh hΔ
          (PhysicalMixedTurnSource.MechanismN A B) 1 t)
        (longitudinalAlpha A B hh hΔ t) := by
  let N := PhysicalMixedTurnSource.MechanismN A B
  let lo : ℕ → ℝ := fun i => panelPointPolarLift A B hh hΔ i 1 t
  let hi : ℕ → ℝ := fun i => panelPointPolarLift A B hh hΔ i 0 t
  have horder : ∀ i ≤ N, lo i ≤ hi i := by
    intro i hiN
    exact (panelPointPolarLift_strictAnti A B hh hΔ hiN ht).antitoneOn
      (by norm_num) (by norm_num) (by norm_num)
  have hchain : ∀ i < N, hi (i + 1) = lo i := by
    intro i hiN
    exact (panelPointPolarLift_hinge A B hh hΔ hiN
      ⟨ht.1.le, ht.2.le⟩).symm
  ext φ
  constructor
  · rintro ⟨i, hiN, s, hs, rfl⟩
    have hlocal : panelPointPolarLift A B hh hΔ i s t ∈ Icc (lo i) (hi i) := by
      rw [← panelPointPolarLift_image_Icc A B hh hΔ hiN ht]
      exact ⟨s, hs, rfl⟩
    exact Icc_subset_Icc_of_chain horder hchain hiN hlocal
  · intro hφ
    obtain ⟨i, hiN, hlocal⟩ := exists_mem_Icc_of_chain horder hchain hφ
    rw [← panelPointPolarLift_image_Icc A B hh hΔ hiN ht] at hlocal
    obtain ⟨s, hs, rfl⟩ := hlocal
    exact ⟨i, hiN, s, hs, rfl⟩

/-- Exact paper-form interval: at every interior physical height, the realized
real lifts are precisely `α(t) - L ≤ φ ≤ α(t)`. -/
theorem longitudinalLiftSet_eq_Icc_alpha_sub_length
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    longitudinalLiftSet A B hh hΔ t =
      Icc (longitudinalAlpha A B hh hΔ t - longitudinalLength A B hh)
        (longitudinalAlpha A B hh hΔ t) := by
  rw [longitudinalLiftSet_eq_endpointInterval A B hh hΔ ht,
    panelPointPolarLift_terminal_eq_alpha_add_delta A B hh hΔ
      ⟨ht.1.le, ht.2.le⟩]
  unfold longitudinalLength
  congr 2 <;> ring

/-- Within each physical panel (sheet chart), the global real lift determines
the longitudinal material coordinate uniquely. -/
theorem panelPointPolarLift_injectiveOn
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    {i : ℕ} (hi : i ≤ PhysicalMixedTurnSource.MechanismN A B)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Set.InjOn (fun s => panelPointPolarLift A B hh hΔ i s t)
      (Icc (0 : ℝ) 1) :=
  (panelPointPolarLift_strictAnti A B hh hΔ hi ht).injOn

/-- A physical ray representative lies in the global lift window. -/
def RayRepresentativeAdmissible (α L β : ℝ) (k : ℤ) : Prop :=
  α - L ≤ β + 2 * Real.pi * (k : ℝ) ∧
    β + 2 * Real.pi * (k : ℝ) ≤ α

/-- A window of angular length strictly below `2π` cannot contain three
ordered real representatives of one physical ray.  This is the explicit
at-most-two-sheet classification used by the trace argument. -/
theorem no_three_ray_representatives
    {α L β : ℝ} (hL0 : 0 < L) (hL2 : L < 2 * Real.pi)
    {k₁ k₂ k₃ : ℤ} (h₁₂ : k₁ < k₂) (h₂₃ : k₂ < k₃)
    (hk₁ : RayRepresentativeAdmissible α L β k₁)
    (hk₃ : RayRepresentativeAdmissible α L β k₃) : False := by
  have hgap : k₁ + 2 ≤ k₃ := by omega
  have hgap' : (k₁ : ℝ) + 2 ≤ (k₃ : ℝ) := by exact_mod_cast hgap
  have hpi : 0 < Real.pi := Real.pi_pos
  unfold RayRepresentativeAdmissible at hk₁ hk₃
  nlinarith

/-- Nonempty physical-height component for one real representative of a ray. -/
def RayRepresentativeHeightNonempty
    (α : ℝ → ℝ) (L β : ℝ) (k : ℤ) : Prop :=
  ∃ t ∈ Icc (0 : ℝ) 1, RayRepresentativeAdmissible (α t) L β k

/-- If the selected seam lift stays in one strict `π` window and the
longitudinal sweep has length below `2π`, then at most two real representatives
of any physical ray have nonempty height components. -/
theorem no_three_nonempty_ray_height_components
    {α : ℝ → ℝ} {θ L β : ℝ}
    (hα : ∀ t ∈ Icc (0 : ℝ) 1, θ < α t ∧ α t < θ + Real.pi)
    (hL0 : 0 < L) (hL2 : L < 2 * Real.pi)
    {k₁ k₂ k₃ : ℤ} (h₁₂ : k₁ < k₂) (h₂₃ : k₂ < k₃)
    (hk₁ : RayRepresentativeHeightNonempty α L β k₁)
    (hk₃ : RayRepresentativeHeightNonempty α L β k₃) : False := by
  rcases hk₁ with ⟨t₁, ht₁, hw₁⟩
  rcases hk₃ with ⟨t₃, ht₃, hw₃⟩
  have hgap : k₁ + 2 ≤ k₃ := by omega
  have hgap' : (k₁ : ℝ) + 2 ≤ (k₃ : ℝ) := by exact_mod_cast hgap
  have ha₁ := hα t₁ ht₁
  have ha₃ := hα t₃ ht₃
  have hpi := Real.pi_pos
  unfold RayRepresentativeAdmissible at hw₁ hw₃
  nlinarith

/-- The selected seam argument stays in the root panel's strict `π` window,
including both height endpoints. -/
theorem longitudinalAlpha_mem_seam_window
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    panelAngleLift A B hh 0 < longitudinalAlpha A B hh hΔ t ∧
      longitudinalAlpha A B hh hΔ t < panelAngleLift A B hh 0 + Real.pi := by
  exact panelPointPolarLift_mem_window A B hh hΔ (i := 0) (s := 0) (t := t)
    (by omega) (by simp) ht

/-- Concrete at-most-two-real-sheets theorem for the full baseline strip. -/
theorem no_three_longitudinal_height_components
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    {β : ℝ} {k₁ k₂ k₃ : ℤ} (h₁₂ : k₁ < k₂) (h₂₃ : k₂ < k₃)
    (hk₁ : RayRepresentativeHeightNonempty
      (longitudinalAlpha A B hh hΔ) (longitudinalLength A B hh) β k₁)
    (hk₃ : RayRepresentativeHeightNonempty
      (longitudinalAlpha A B hh hΔ) (longitudinalLength A B hh) β k₃) : False :=
  no_three_nonempty_ray_height_components
    (fun t ht => longitudinalAlpha_mem_seam_window A B hh hΔ ht)
    (longitudinalLength_pos A B hh hΔ)
    (longitudinalLength_lt_two_pi A B hh)
    h₁₂ h₂₃ hk₁ hk₃

end Raw

section Rays

variable {n : ℕ}
  (S : RadialExtremalSafety.TriangularRadialStrip n) (O : Plane)

/-- A positive hit of one physical panel by the ray with real lift `α`. -/
def RayHit (α : ℝ) (i : ℕ) (s t r : ℝ) : Prop :=
  s ∈ Icc (0 : ℝ) 1 ∧ t ∈ Icc (0 : ℝ) 1 ∧ 0 < r ∧
    S.point i s t - O = r • MixedTurnSafeCut.direction α

/-- Eligible heights on a fixed physical ray.  Endpoints and singleton
intervals are retained because both parameter intervals are closed. -/
def eligibleHeights (α : ℝ) (i : ℕ) : Set ℝ :=
  {t | ∃ s r, RayHit S O α i s t r}

lemma eligibleHeight_mem_Icc {α : ℝ} {i : ℕ} {t : ℝ}
    (ht : t ∈ eligibleHeights S O α i) : t ∈ Icc (0 : ℝ) 1 := by
  rcases ht with ⟨s, r, hs, hti, hr, hp⟩
  exact hti

/-- RF rules out a parallel eligible ray, including endpoint and singleton
hits. -/
theorem ray_denominator_neg
    (hR : S.RadialSupport O) {α : ℝ} {i : ℕ} (hi : i ≤ n)
    {s t r : ℝ} (hit : RayHit S O α i s t r) :
    MixedTurnSafeCut.det (MixedTurnSafeCut.direction α) (S.v i) < 0 := by
  have hd := RadialExtremalSafety.TriangularRadialStrip.support_point
    hR hi hit.1 hit.2.1
  rw [hit.2.2.2] at hd
  rw [RadialExtremalSafety.det_smul_left] at hd
  rcases (mul_neg_iff.mp hd) with hgood | hbad
  · exact hgood.2
  · exact (not_lt_of_ge hit.2.2.1.le hbad.1).elim

/-- Exact affine radius equation on every eligible height. -/
theorem ray_radius_affine
    {α : ℝ} {i : ℕ} {s t r : ℝ} (hit : RayHit S O α i s t r) :
    r * MixedTurnSafeCut.det (MixedTurnSafeCut.direction α) (S.v i) =
      (1 - t) * MixedTurnSafeCut.det (S.B i - O) (S.v i) +
        t * MixedTurnSafeCut.det (S.B i + S.d i - O) (S.v i) := by
  calc
    _ = MixedTurnSafeCut.det
        (r • MixedTurnSafeCut.direction α) (S.v i) := by
      rw [RadialExtremalSafety.det_smul_left]
    _ = MixedTurnSafeCut.det (S.point i s t - O) (S.v i) := by
      rw [hit.2.2.2]
    _ = _ := RadialExtremalSafety.TriangularRadialStrip.det_point S O i s t

/-- Division form of the radius formula; RF supplies the nonzero denominator. -/
theorem ray_radius_eq
    (hR : S.RadialSupport O) {α : ℝ} {i : ℕ} (hi : i ≤ n)
    {s t r : ℝ} (hit : RayHit S O α i s t r) :
    r = ((1 - t) * MixedTurnSafeCut.det (S.B i - O) (S.v i) +
          t * MixedTurnSafeCut.det (S.B i + S.d i - O) (S.v i)) /
        MixedTurnSafeCut.det (MixedTurnSafeCut.direction α) (S.v i) := by
  have hd := ray_denominator_neg S O hR hi hit
  apply (eq_div_iff (ne_of_lt hd)).2
  exact ray_radius_affine S O hit

/-- Exact strict radius ordering along an eligible height interval.  The proof
uses only the two endpoint determinants, so it remains valid at radial hinges,
with zero horizontal coefficients, and when neighboring eligible intervals
collapse to singletons. -/
theorem ray_radius_strict_of_endpoint_det
    (hR : S.RadialSupport O) {α : ℝ} {i : ℕ} (hi : i ≤ n)
    (hend : MixedTurnSafeCut.det (S.B i + S.d i - O) (S.v i) <
      MixedTurnSafeCut.det (S.B i - O) (S.v i))
    {s₁ s₂ t₁ t₂ r₁ r₂ : ℝ} (ht : t₁ < t₂)
    (h₁ : RayHit S O α i s₁ t₁ r₁) (h₂ : RayHit S O α i s₂ t₂ r₂) :
    r₁ < r₂ := by
  let d := MixedTurnSafeCut.det (MixedTurnSafeCut.direction α) (S.v i)
  let a := MixedTurnSafeCut.det (S.B i - O) (S.v i)
  let b := MixedTurnSafeCut.det (S.B i + S.d i - O) (S.v i)
  have hd : d < 0 := ray_denominator_neg S O hR hi h₁
  have hn : (1 - t₂) * a + t₂ * b < (1 - t₁) * a + t₁ * b := by
    dsimp [a, b]
    nlinarith
  have he₁ := ray_radius_affine S O h₁
  have he₂ := ray_radius_affine S O h₂
  by_contra hnot
  have hle : r₂ ≤ r₁ := le_of_not_gt hnot
  have hp : 0 ≤ (r₂ - r₁) * d :=
    mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hle) hd.le
  dsimp [d, a, b] at he₁ he₂ hp hn
  nlinarith

/-- Radius on one panel and one ray is uniquely determined by height, even for
zero-length horizontal pieces. -/
theorem ray_radius_unique
    (hR : S.RadialSupport O) {α : ℝ} {i : ℕ} (hi : i ≤ n)
    {s₁ s₂ t r₁ r₂ : ℝ}
    (h₁ : RayHit S O α i s₁ t r₁) (h₂ : RayHit S O α i s₂ t r₂) : r₁ = r₂ := by
  rw [ray_radius_eq S O hR hi h₁, ray_radius_eq S O hR hi h₂]

/-- A supported ray meets a fixed-height physical panel slice in at most one
point.  This covers zero coefficients: then all `s` names denote that same
point. -/
theorem ray_point_unique_at_height
    (hR : S.RadialSupport O) {α : ℝ} {i : ℕ} (hi : i ≤ n)
    {s₁ s₂ t r₁ r₂ : ℝ}
    (h₁ : RayHit S O α i s₁ t r₁) (h₂ : RayHit S O α i s₂ t r₂) :
    S.point i s₁ t = S.point i s₂ t := by
  have hr := ray_radius_unique S O hR hi h₁ h₂
  have hp₁ := sub_eq_iff_eq_add.mp h₁.2.2.2
  have hp₂ := sub_eq_iff_eq_add.mp h₂.2.2.2
  rw [hp₁, hp₂, hr]

/-- No supported positive ray is parallel to an eligible physical panel. -/
theorem ineligible_of_parallel
    (hR : S.RadialSupport O) {α : ℝ} {i : ℕ} (hi : i ≤ n)
    (hparallel : MixedTurnSafeCut.det (MixedTurnSafeCut.direction α) (S.v i) = 0) :
    eligibleHeights S O α i = ∅ := by
  ext t
  constructor
  · intro ht
    rcases ht with ⟨s, r, hit⟩
    have hd := ray_denominator_neg S O hR hi hit
    linarith
  · simp

end Rays

section PhysicalRayClassification

variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

/-- Every actual non-pole baseline ray hit has one explicit real sheet
representative in the exact global lift window. -/
theorem baselineRayHit_realRepresentative
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    {β : ℝ} {i : ℕ} (hi : i ≤ PhysicalMixedTurnSource.MechanismN A B)
    {s t r : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hit : RayHit (baselineStrip A B hh)
      (PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ))
      β i s t r) :
    ∃ k : ℤ,
      panelPointPolarLift A B hh hΔ i s t = β + 2 * Real.pi * (k : ℝ) ∧
      RayRepresentativeAdmissible
        (longitudinalAlpha A B hh hΔ t) (longitudinalLength A B hh) β k := by
  let O := PhysicalMixedTurnSource.circuitPole A B hh 0 (ne_of_lt hΔ)
  let φ := panelPointPolarLift A B hh hΔ i s t
  let z := (baselineStrip A B hh).point i s t - O
  have hdec := panelPointPolarLift_decomposition A B hh hΔ hi hit.1
    ⟨ht.1.le, ht.2.le⟩
  change z = ‖z‖ • MixedTurnSafeCut.direction φ at hdec
  have hhit : z = r • MixedTurnSafeCut.direction β := hit.2.2.2
  have hdirnorm (γ : ℝ) : ‖MixedTurnSafeCut.direction γ‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [MixedTurnSafeCut.direction, Fin.sum_univ_two]
  have hrnorm : ‖z‖ = r := by
    rw [hhit, norm_smul, Real.norm_eq_abs, hdirnorm, mul_one,
      abs_of_pos hit.2.2.1]
  have hzpos : 0 < ‖z‖ := by rw [hrnorm]; exact hit.2.2.1
  have hdir : MixedTurnSafeCut.direction φ = MixedTurnSafeCut.direction β := by
    apply smul_right_injective Plane (ne_of_gt hzpos)
    change ‖z‖ • MixedTurnSafeCut.direction φ =
      ‖z‖ • MixedTurnSafeCut.direction β
    rw [← hdec, hrnorm, ← hhit]
  have hang := angle_eq_mod_two_pi_of_direction_eq hdir
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hang
  have hkreal : φ = β + 2 * Real.pi * (k : ℝ) := by linarith
  refine ⟨k, hkreal, ?_⟩
  have hmem : φ ∈ longitudinalLiftSet A B hh hΔ t :=
    ⟨i, hi, s, hit.1, rfl⟩
  rw [longitudinalLiftSet_eq_Icc_alpha_sub_length A B hh hΔ ht] at hmem
  unfold RayRepresentativeAdmissible
  change β + 2 * Real.pi * (k : ℝ) ∈
    Icc (longitudinalAlpha A B hh hΔ t - longitudinalLength A B hh)
      (longitudinalAlpha A B hh hΔ t)
  simpa only [hkreal] using hmem

end PhysicalRayClassification

end
end FixedBaselinePolarRayGeometry

#print axioms FixedBaselinePolarRayGeometry.baselineStrip
#print axioms FixedBaselinePolarRayGeometry.panelAngleLift_terminal
#print axioms FixedBaselinePolarRayGeometry.retainedHinge_eq_next_entry
#print axioms FixedBaselinePolarRayGeometry.baselineStrip_radialSupport
#print axioms FixedBaselinePolarRayGeometry.reflectedBaselineStrip_radialSupport
#print axioms FixedBaselinePolarRayGeometry.terminalSeam_eq_fullCircuit
#print axioms FixedBaselinePolarRayGeometry.fullCircuit_ray_copy
#print axioms FixedBaselinePolarRayGeometry.fullCircuit_norm_lt_iff
#print axioms FixedBaselinePolarRayGeometry.panelPointPolarLift_mem_window
#print axioms FixedBaselinePolarRayGeometry.ray_radius_eq
#print axioms FixedBaselinePolarRayGeometry.ray_radius_strict_of_endpoint_det
#print axioms FixedBaselinePolarRayGeometry.ray_point_unique_at_height
#print axioms FixedBaselinePolarRayGeometry.ineligible_of_parallel
#print axioms FixedBaselinePolarRayGeometry.longitudinalLiftSet_eq_Icc_alpha_sub_length
#print axioms FixedBaselinePolarRayGeometry.no_three_longitudinal_height_components
#print axioms FixedBaselinePolarRayGeometry.baselineRayHit_realRepresentative
