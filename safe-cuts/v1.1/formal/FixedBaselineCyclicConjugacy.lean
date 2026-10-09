import PhysicalRadialSupport
import PhysicalMixedTurnLayout

open Set
open scoped BigOperators Classical NNReal
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CommonSupportMerge OriginalFacetCertificates NormalFanSplice MaximalSupportCells
open CyclicCutOrders EuclideanPrismatoidCoordinates PolyhedralInputBridge
open TrimmedFacetWitnesses BandGeometryAssembly FiniteWitnessClosure SingleCutRecovery
open CutSurfaceQuotient MixedTurnSafeCut PolygonSetReconstruction ConvexPolygonTurning

namespace PhysicalMixedTurnSource
noncomputable section
set_option maxHeartbeats 8000000

section Raw
variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

/-- The source at relative position `j` in root `k` is the source at absolute
position `k+j` in the root-zero baseline. -/
lemma baseline_familySource (k : Fin (MechanismN A B + 1)) (j : ℕ) :
    familySource A B 0 (k.val + j) = familySource A B k j := by
  induction j with
  | zero =>
      change familySource A B 0 k.val = familySource A B k 0
      rw [familySource_eq_add A B 0 k.val k.isLt]
      simp
  | succ j ih =>
      change familySource A B 0 (k.val + j + 1) =
        familySource A B k (j + 1)
      rw [familySource_succ, familySource_succ, ih]

/-- Real headings add under cyclic re-rooting; this is an equality in `ℝ`, not
an equality modulo a turn. -/
lemma baseline_familyHeading (k : Fin (MechanismN A B + 1)) (j : ℕ) :
    familyHeading A B hh 0 (k.val + j) =
      familyHeading A B hh 0 k.val + familyHeading A B hh k j := by
  induction j with
  | zero => simp [familyHeading_zero]
  | succ j ih =>
      have hbase := familyHeading_succ A B hh 0 (k.val + j)
      have hroot := familyHeading_succ A B hh k j
      change familyHeading A B hh 0 (k.val + j + 1) =
        familyHeading A B hh 0 k.val + familyHeading A B hh k (j + 1)
      have hs : familySource A B 0 (k.val + j + 1) =
          familySource A B k (j + 1) := by
        convert baseline_familySource A B k (j + 1) using 1 <;> omega
      rw [hs] at hbase
      linarith [ih]

/-- Accumulated direct translations obey the same affine cocycle as the
headings. -/
lemma baseline_directTranslation (k : Fin (MechanismN A B + 1)) (j : ℕ) :
    directTranslation A B hh 0 (k.val + j) =
      directTranslation A B hh 0 k.val +
        planeRotation (familyHeading A B hh 0 k.val)
          (directTranslation A B hh k j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      change directTranslation A B hh 0 (k.val + j + 1) =
        directTranslation A B hh 0 k.val +
          planeRotation (familyHeading A B hh 0 k.val)
            (directTranslation A B hh k (j + 1))
      rw [directTranslation_succ, directTranslation_succ, ih,
        baseline_familyHeading A B hh k j, baseline_familySource A B k j,
        map_add, planeRotation_comp]
      abel

/-- Explicit orientation-preserving affine isometry placing root `k` into the
single root-zero baseline development. -/
noncomputable def baselineAlignment (k : Fin (MechanismN A B + 1)) :
    Plane →ᵃⁱ[ℝ] Plane :=
  planarPlacement (familyHeading A B hh 0 k.val) 0
    (directTranslation A B hh 0 k.val)

@[simp] theorem baselineAlignment_apply
    (k : Fin (MechanismN A B + 1)) (x : Plane) :
    baselineAlignment A B hh k x =
      directTranslation A B hh 0 k.val +
        planeRotation (familyHeading A B hh 0 k.val) x := by
  rw [baselineAlignment, planarPlacement_apply]
  simp

/-- The baseline alignment sends every relative developed position to the
corresponding absolute baseline position. -/
theorem baselineAlignment_direct_position
    (k : Fin (MechanismN A B + 1)) (j : ℕ)
    (z : Plane) :
    baselineAlignment A B hh k
        (planeRotation (familyHeading A B hh k j) z +
          directTranslation A B hh k j) =
      planeRotation (familyHeading A B hh 0 (k.val + j)) z +
        directTranslation A B hh 0 (k.val + j) := by
  rw [baselineAlignment_apply, baseline_familyHeading A B hh,
    baseline_directTranslation A B hh, map_add, planeRotation_comp]
  abel

/-- The alignment maps every corresponding heading vector, without pretending
that headings at different roots are definitionally equal. -/
theorem baselineAlignment_heading_sub
    (k : Fin (MechanismN A B + 1)) (x y : Plane) :
    baselineAlignment A B hh k x - baselineAlignment A B hh k y =
      planeRotation (familyHeading A B hh 0 k.val) (x - y) := by
  simp only [baselineAlignment_apply]
  rw [map_sub]
  abel

/-- In particular every developed forward heading is carried to its absolute
baseline heading. -/
theorem baselineAlignment_developedForward
    (k : Fin (MechanismN A B + 1)) (j : ℕ) :
    planeRotation (familyHeading A B hh 0 k.val)
        (developedForward A B hh k j) =
      developedForward A B hh 0 (k.val + j) := by
  rw [developedForward, developedForward, baseline_familyHeading A B hh,
    planeRotation_comp]

/-- Equality of the dependent source faces used for explicit point transport. -/
lemma baseline_cycle_familySource (k : Fin (MechanismN A B + 1)) (j : ℕ) :
    cycle A B (familySource A B k j) =
      cycle A B (familySource A B 0 (k.val + j)) := by
  rw [baseline_familySource A B k j]

/-- Point transport along equality of physical source indices. -/
noncomputable def sourceFacePoint {i i' : SourceIndex A B} (e : i = i')
    (x : FaceSpace A B h (cycle A B i)) :
    FaceSpace A B h (cycle A B i') := by
  subst i'
  exact x

@[simp] lemma intrinsicFaceChart_sourceFacePoint {i i' : SourceIndex A B}
    (e : i = i') (x : FaceSpace A B h (cycle A B i)) :
    intrinsicFaceChart A B hh i' (sourceFacePoint A B e x) =
      intrinsicFaceChart A B hh i x := by
  subst i'
  rfl

/-- A source point transported only along the proved equality of corresponding
physical source indices. -/
noncomputable def baselineFacePoint
    (k : Fin (MechanismN A B + 1)) (j : ℕ)
    (x : FaceSpace A B h (cycle A B (familySource A B k j))) :
    FaceSpace A B h (cycle A B (familySource A B 0 (k.val + j))) :=
  sourceFacePoint A B (baseline_familySource A B k j).symm x

@[simp] lemma intrinsicFaceChart_baselineFacePoint
    (k : Fin (MechanismN A B + 1)) (j : ℕ)
    (x : FaceSpace A B h (cycle A B (familySource A B k j))) :
    intrinsicFaceChart A B hh (familySource A B 0 (k.val + j))
        (baselineFacePoint A B k j x) =
      intrinsicFaceChart A B hh (familySource A B k j) x := by
  exact intrinsicFaceChart_sourceFacePoint A B hh _ x

@[simp] lemma sourceFacePoint_entryLower {i i' : SourceIndex A B}
    (e : i = i') :
    sourceFacePoint A B e (faceEntryLower A B hh i) =
      faceEntryLower A B hh i' := by
  subst i'
  rfl

@[simp] lemma sourceFacePoint_entryUpper {i i' : SourceIndex A B}
    (e : i = i') :
    sourceFacePoint A B e (faceEntryUpper A B hh i) =
      faceEntryUpper A B hh i' := by
  subst i'
  rfl

@[simp] lemma baselineFacePoint_entryLower
    (k : Fin (MechanismN A B + 1)) (j : ℕ) :
    baselineFacePoint A B k j
        (faceEntryLower A B hh (familySource A B k j)) =
      faceEntryLower A B hh (familySource A B 0 (k.val + j)) := by
  exact sourceFacePoint_entryLower A B hh _

@[simp] lemma baselineFacePoint_entryUpper
    (k : Fin (MechanismN A B + 1)) (j : ℕ) :
    baselineFacePoint A B k j
        (faceEntryUpper A B hh (familySource A B k j)) =
      faceEntryUpper A B hh (familySource A B 0 (k.val + j)) := by
  exact sourceFacePoint_entryUpper A B hh _

/-- Pointwise conjugacy for every source point in every panel. -/
theorem baselineAlignment_directDevelopedMap
    (k : Fin (MechanismN A B + 1)) (j : ℕ)
    (x : FaceSpace A B h (cycle A B (familySource A B k j))) :
    baselineAlignment A B hh k (directDevelopedMap A B hh k j x) =
      directDevelopedMap A B hh 0 (k.val + j)
        (baselineFacePoint A B k j x) := by
  rw [directDevelopedMap_apply, directDevelopedMap_apply,
    intrinsicFaceChart_baselineFacePoint]
  exact baselineAlignment_direct_position A B hh k j _

/-- The alignment carries every lower-rim source position into the same
root-zero baseline sequence. -/
theorem baselineAlignment_developedLower
    (k : Fin (MechanismN A B + 1)) (j : ℕ) :
    baselineAlignment A B hh k (developedLower A B hh k j) =
      developedLower A B hh 0 (k.val + j) := by
  rw [developedLower, developedLower,
    baselineAlignment_directDevelopedMap, baselineFacePoint_entryLower]

/-- The alignment carries every upper-rim source position into the same
root-zero baseline sequence. -/
theorem baselineAlignment_developedUpper
    (k : Fin (MechanismN A B + 1)) (j : ℕ) :
    baselineAlignment A B hh k (developedUpper A B hh k j) =
      developedUpper A B hh 0 (k.val + j) := by
  rw [developedUpper, developedUpper,
    baselineAlignment_directDevelopedMap, baselineFacePoint_entryUpper]

/-- Advancing a full source cycle in the baseline returns to the same physical
source index. -/
lemma baseline_familySource_full_add (j : ℕ) :
    familySource A B 0 (MechanismN A B + 1 + j) =
      familySource A B 0 j := by
  induction j with
  | zero => exact familySource_full A B 0
  | succ j ih =>
      change familySource A B 0 (MechanismN A B + 1 + j + 1) =
        familySource A B 0 (j + 1)
      rw [familySource_succ, familySource_succ, ih]

/-- A full baseline cycle adds the real defect to every subsequent heading. -/
lemma baseline_familyHeading_full_add (j : ℕ) :
    familyHeading A B hh 0 (MechanismN A B + 1 + j) =
      intrinsicDelta A B (hh := hh) + familyHeading A B hh 0 j := by
  induction j with
  | zero => simp [familyHeading_full, familyHeading_zero]
  | succ j ih =>
      have hleft := familyHeading_succ A B hh 0 (MechanismN A B + 1 + j)
      have hright := familyHeading_succ A B hh 0 j
      have hs : familySource A B 0 (MechanismN A B + 1 + j + 1) =
          familySource A B 0 (j + 1) := by
        convert baseline_familySource_full_add A B (j + 1) using 1 <;> omega
      change familyHeading A B hh 0 (MechanismN A B + 1 + j + 1) =
        intrinsicDelta A B (hh := hh) + familyHeading A B hh 0 (j + 1)
      rw [hs] at hleft
      linarith [ih]

/-- A full baseline cycle acts on every later translation by the actual affine
circuit, including its nonzero translation. -/
lemma baseline_directTranslation_full_add (j : ℕ) :
    directTranslation A B hh 0 (MechanismN A B + 1 + j) =
      directTranslation A B hh 0 (MechanismN A B + 1) +
        planeRotation (intrinsicDelta A B (hh := hh))
          (directTranslation A B hh 0 j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hleft := directTranslation_succ A B hh 0
        (MechanismN A B + 1 + j)
      have hright := directTranslation_succ A B hh 0 j
      change directTranslation A B hh 0 (MechanismN A B + 1 + j + 1) =
        directTranslation A B hh 0 (MechanismN A B + 1) +
          planeRotation (intrinsicDelta A B (hh := hh))
            (directTranslation A B hh 0 (j + 1))
      rw [hleft, hright, ih, baseline_familyHeading_full_add A B hh j,
        baseline_familySource_full_add A B j, map_add, planeRotation_comp]
      abel

/-- Explicit transport used for the second-sheet copy of a baseline panel. -/
noncomputable def baselineFullCycleFacePoint (j : ℕ)
    (x : FaceSpace A B h (cycle A B (familySource A B 0 j))) :
    FaceSpace A B h
      (cycle A B (familySource A B 0 (MechanismN A B + 1 + j))) :=
  sourceFacePoint A B (baseline_familySource_full_add A B j).symm x

/-- Every wrapped baseline panel is literally the image of its first-sheet
panel under the actual full affine circuit `H`, not merely a modular relabel. -/
theorem baseline_directDevelopedMap_fullCircuit
    (j : ℕ)
    (x : FaceSpace A B h (cycle A B (familySource A B 0 j))) :
    directDevelopedMap A B hh 0 (MechanismN A B + 1 + j)
        (baselineFullCycleFacePoint A B j x) =
      fullCircuit A B hh 0 (directDevelopedMap A B hh 0 j x) := by
  unfold baselineFullCycleFacePoint
  rw [directDevelopedMap_apply, directDevelopedMap_apply,
    fullCircuit_apply, baseline_familyHeading_full_add,
    baseline_directTranslation_full_add,
    intrinsicFaceChart_sourceFacePoint, map_add, planeRotation_comp]
  abel

/-- The lower-rim positions on the wrapped sheet are actual `H` copies. -/
theorem baseline_developedLower_fullCircuit (j : ℕ) :
    developedLower A B hh 0 (MechanismN A B + 1 + j) =
      fullCircuit A B hh 0 (developedLower A B hh 0 j) := by
  unfold developedLower
  calc
    _ = directDevelopedMap A B hh 0 (MechanismN A B + 1 + j)
        (baselineFullCycleFacePoint A B j
          (faceEntryLower A B hh (familySource A B 0 j))) := by
        congr 1
        exact (sourceFacePoint_entryLower A B hh _).symm
    _ = _ := baseline_directDevelopedMap_fullCircuit A B hh j _

/-- The upper-rim positions on the wrapped sheet are actual `H` copies. -/
theorem baseline_developedUpper_fullCircuit (j : ℕ) :
    developedUpper A B hh 0 (MechanismN A B + 1 + j) =
      fullCircuit A B hh 0 (developedUpper A B hh 0 j) := by
  unfold developedUpper
  calc
    _ = directDevelopedMap A B hh 0 (MechanismN A B + 1 + j)
        (baselineFullCycleFacePoint A B j
          (faceEntryUpper A B hh (familySource A B 0 j))) := by
        congr 1
        exact (sourceFacePoint_entryUpper A B hh _).symm
    _ = _ := baseline_directDevelopedMap_fullCircuit A B hh j _

/-- The explicit alignment conjugates the complete affine circuit at root `k`
to the one fixed root-zero circuit on every point. -/
theorem baselineAlignment_fullCircuit
    (k : Fin (MechanismN A B + 1)) (x : Plane) :
    baselineAlignment A B hh k (fullCircuit A B hh k x) =
      fullCircuit A B hh 0 (baselineAlignment A B hh k x) := by
  have hroot := baseline_directTranslation A B hh k (MechanismN A B + 1)
  have hroot' : directTranslation A B hh 0 (MechanismN A B + 1 + k.val) =
      directTranslation A B hh 0 k.val +
        planeRotation (familyHeading A B hh 0 k.val)
          (directTranslation A B hh k (MechanismN A B + 1)) := by
    calc
      _ = directTranslation A B hh 0 (k.val + (MechanismN A B + 1)) := by
        congr 1
        omega
      _ = _ := hroot
  have hperiod := baseline_directTranslation_full_add A B hh k.val
  have ht : directTranslation A B hh 0 k.val +
        planeRotation (familyHeading A B hh 0 k.val)
          (directTranslation A B hh k (MechanismN A B + 1)) =
      directTranslation A B hh 0 (MechanismN A B + 1) +
        planeRotation (intrinsicDelta A B (hh := hh))
          (directTranslation A B hh 0 k.val) := by
    rw [← hroot', hperiod]
  rw [baselineAlignment_apply, baselineAlignment_apply,
    fullCircuit_apply, fullCircuit_apply, map_add, planeRotation_comp]
  rw [show familyHeading A B hh 0 k.val + intrinsicDelta A B (hh := hh) =
      intrinsicDelta A B (hh := hh) + familyHeading A B hh 0 k.val by ring]
  rw [← planeRotation_comp]
  rw [map_add]
  calc
    _ = planeRotation (intrinsicDelta A B (hh := hh))
          (planeRotation (familyHeading A B hh 0 k.val) x) +
        (directTranslation A B hh 0 k.val +
          planeRotation (familyHeading A B hh 0 k.val)
            (directTranslation A B hh k (MechanismN A B + 1))) := by abel
    _ = planeRotation (intrinsicDelta A B (hh := hh))
          (planeRotation (familyHeading A B hh 0 k.val) x) +
        (directTranslation A B hh 0 (MechanismN A B + 1) +
          planeRotation (intrinsicDelta A B (hh := hh))
            (directTranslation A B hh 0 k.val)) := by rw [ht]
    _ = _ := by abel

/-- The unique pole at every re-rooting is carried to the same baseline pole. -/
theorem baselineAlignment_circuitPole
    (k : Fin (MechanismN A B + 1))
    (hΔ : intrinsicDelta A B (hh := hh) ≠ 0) :
    baselineAlignment A B hh k (circuitPole A B hh k hΔ) =
      circuitPole A B hh 0 hΔ := by
  apply circuitPole_unique A B hh 0 hΔ
  rw [← baselineAlignment_fullCircuit A B hh k,
    circuitPole_fixed A B hh k hΔ]

/-- Determinants are unchanged by the orientation-preserving baseline
alignment. -/
lemma baselineAlignment_det
    (k : Fin (MechanismN A B + 1)) (O Y v : Plane) :
    MixedTurnSafeCut.det
        (baselineAlignment A B hh k Y - baselineAlignment A B hh k O)
        (planeRotation (familyHeading A B hh 0 k.val) v) =
      MixedTurnSafeCut.det (Y - O) v := by
  rw [baselineAlignment_heading_sub A B hh,
    planeRotation_det]

/-- Negative RF transported into one fixed development: every inequality uses
the same baseline pole and the corresponding baseline position (which may lie
on the actual wrapped `H` sheet). -/
theorem baseline_physical_negative_RF
    (hΔ : intrinsicDelta A B (hh := hh) < 0) :
    ∀ k : Fin (MechanismN A B + 1),
      MixedTurnSafeCut.det
          (developedUpper A B hh 0 k.val -
            circuitPole A B hh 0 (ne_of_lt hΔ))
          (developedForward A B hh 0 k.val) < 0 ∧
        MixedTurnSafeCut.det
          (developedLower A B hh 0 k.val -
            circuitPole A B hh 0 (ne_of_lt hΔ))
          (developedForward A B hh 0 k.val) < 0 := by
  intro k
  have hk := physical_negative_RF A B hh hΔ k
  have hu := baselineAlignment_det A B hh k
    (circuitPole A B hh k (ne_of_lt hΔ))
    (developedUpper A B hh k 0) (developedForward A B hh k 0)
  have hl := baselineAlignment_det A B hh k
    (circuitPole A B hh k (ne_of_lt hΔ))
    (developedLower A B hh k 0) (developedForward A B hh k 0)
  rw [baselineAlignment_developedUpper A B hh k 0,
    baselineAlignment_circuitPole A B hh k,
    baselineAlignment_developedForward A B hh k 0] at hu
  rw [baselineAlignment_developedLower A B hh k 0,
    baselineAlignment_circuitPole A B hh k,
    baselineAlignment_developedForward A B hh k 0] at hl
  have hu' : MixedTurnSafeCut.det
        (developedUpper A B hh 0 k.val - circuitPole A B hh 0 (ne_of_lt hΔ))
        (developedForward A B hh 0 k.val) =
      MixedTurnSafeCut.det
        (developedUpper A B hh k 0 - circuitPole A B hh k (ne_of_lt hΔ))
        (developedForward A B hh k 0) := by
    simpa only [Nat.add_zero] using hu
  have hl' : MixedTurnSafeCut.det
        (developedLower A B hh 0 k.val - circuitPole A B hh 0 (ne_of_lt hΔ))
        (developedForward A B hh 0 k.val) =
      MixedTurnSafeCut.det
        (developedLower A B hh k 0 - circuitPole A B hh k (ne_of_lt hΔ))
        (developedForward A B hh k 0) := by
    simpa only [Nat.add_zero] using hl
  exact ⟨hu'.symm ▸ hk.1, hl'.symm ▸ hk.2⟩

/-- Positive RF transported into the same fixed development and same baseline
pole. -/
theorem baseline_physical_positive_RF
    (hΔ : 0 < intrinsicDelta A B (hh := hh)) :
    ∀ k : Fin (MechanismN A B + 1),
      0 < MixedTurnSafeCut.det
          (developedLower A B hh 0 k.val -
            circuitPole A B hh 0 (ne_of_gt hΔ))
          (developedForward A B hh 0 k.val) ∧
        0 < MixedTurnSafeCut.det
          (developedUpper A B hh 0 k.val -
            circuitPole A B hh 0 (ne_of_gt hΔ))
          (developedForward A B hh 0 k.val) := by
  intro k
  have hk := physical_positive_RF A B hh hΔ k
  have hl := baselineAlignment_det A B hh k
    (circuitPole A B hh k (ne_of_gt hΔ))
    (developedLower A B hh k 0) (developedForward A B hh k 0)
  have hu := baselineAlignment_det A B hh k
    (circuitPole A B hh k (ne_of_gt hΔ))
    (developedUpper A B hh k 0) (developedForward A B hh k 0)
  rw [baselineAlignment_developedLower A B hh k 0,
    baselineAlignment_circuitPole A B hh k,
    baselineAlignment_developedForward A B hh k 0] at hl
  rw [baselineAlignment_developedUpper A B hh k 0,
    baselineAlignment_circuitPole A B hh k,
    baselineAlignment_developedForward A B hh k 0] at hu
  have hl' : MixedTurnSafeCut.det
        (developedLower A B hh 0 k.val - circuitPole A B hh 0 (ne_of_gt hΔ))
        (developedForward A B hh 0 k.val) =
      MixedTurnSafeCut.det
        (developedLower A B hh k 0 - circuitPole A B hh k (ne_of_gt hΔ))
        (developedForward A B hh k 0) := by
    simpa only [Nat.add_zero] using hl
  have hu' : MixedTurnSafeCut.det
        (developedUpper A B hh 0 k.val - circuitPole A B hh 0 (ne_of_gt hΔ))
        (developedForward A B hh 0 k.val) =
      MixedTurnSafeCut.det
        (developedUpper A B hh k 0 - circuitPole A B hh k (ne_of_gt hΔ))
        (developedForward A B hh k 0) := by
    simpa only [Nat.add_zero] using hu
  exact ⟨hl'.symm ▸ hk.1, hu'.symm ▸ hk.2⟩

end Raw
end
end PhysicalMixedTurnSource

#print axioms PhysicalMixedTurnSource.baselineAlignment_directDevelopedMap
#print axioms PhysicalMixedTurnSource.baseline_directDevelopedMap_fullCircuit
#print axioms PhysicalMixedTurnSource.baselineAlignment_fullCircuit
#print axioms PhysicalMixedTurnSource.baselineAlignment_circuitPole
#print axioms PhysicalMixedTurnSource.baseline_physical_negative_RF
#print axioms PhysicalMixedTurnSource.baseline_physical_positive_RF
