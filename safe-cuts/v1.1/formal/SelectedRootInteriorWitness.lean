import SelectedNegativeRootPolarLift
import ArbitraryCutDirectMap
import FiniteWitnessClosure

open Set
open scoped Classical NNReal Topology
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CommonSupportMerge OriginalFacetCertificates NormalFanSplice MaximalSupportCells
open CyclicCutOrders EuclideanPrismatoidCoordinates PolyhedralInputBridge
open TrimmedFacetWitnesses BandGeometryAssembly FiniteWitnessClosure SingleCutRecovery
open CutSurfaceQuotient MixedTurnSafeCut PolygonSetReconstruction ConvexPolygonTurning
open PhysicalMixedTurnSource

namespace SelectedNegativeRootPolar
noncomputable section
set_option maxHeartbeats 8000000

variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

private lemma source_height_horizontal (u : SourceIndex A B) (t s : ℝ) :
    (certificate A B hh (cycle A B u)).height
      (faceEntryAt A B hh t u + s • faceUnit A B hh u) = t := by
  have hv := (certificate A B hh (cycle A B u)).height.map_vadd
    (faceEntryAt A B hh t u) (s • faceUnit A B hh u)
  rw [map_smul] at hv
  simp only [vadd_eq_add] at hv
  rw [add_comm, hv, faceEntryAt_height]
  have hz : (certificate A B hh (cycle A B u)).height.linear
      (faceUnit A B hh u) = 0 := by
    exact chartLinear_faceUnit_height A B hh u
  change s • (certificate A B hh (cycle A B u)).height.linear
    (faceUnit A B hh u) + t = t
  rw [hz, smul_zero, zero_add]

private lemma source_horizontal_strict (u : SourceIndex A B)
    {x : FaceSpace A B h (cycle A B u)}
    (hx : x ∈ interior (certificate A B hh (cycle A B u)).domain)
    {t s : ℝ}
    (hrep : x = faceEntryAt A B hh t u + s • faceUnit A B hh u) :
    0 < s ∧ s < retainedLowerRunCoeff A B hh t u := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  have hδnorm : ‖δ • faceUnit A B hh u‖ < ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ, faceUnit_norm]
    change ε / 2 * 1 < ε
    linarith
  have hminus : x - δ • faceUnit A B hh u ∈
      (certificate A B hh (cycle A B u)).domain :=
    interior_subset (hball (by simpa [dist_eq_norm] using hδnorm))
  have hplus : x + δ • faceUnit A B hh u ∈
      (certificate A B hh (cycle A B u)).domain :=
    interior_subset (hball (by simpa [dist_eq_norm, norm_neg] using hδnorm))
  have hminusrep : x - δ • faceUnit A B hh u =
      faceEntryAt A B hh t u + (s - δ) • faceUnit A B hh u := by
    rw [hrep]; module
  have hplusrep : x + δ • faceUnit A B hh u =
      faceEntryAt A B hh t u + (s + δ) • faceUnit A B hh u := by
    rw [hrep]; module
  have hmheight : (certificate A B hh (cycle A B u)).height
      (x - δ • faceUnit A B hh u) = t := by
    rw [hminusrep]; exact source_height_horizontal A B hh u t (s - δ)
  have hpheight : (certificate A B hh (cycle A B u)).height
      (x + δ • faceUnit A B hh u) = t := by
    rw [hplusrep]; exact source_height_horizontal A B hh u t (s + δ)
  obtain ⟨sm, hsm, _, hmrep⟩ := face_horizontal_parameter_bounds A B hh u _ hminus hmheight
  obtain ⟨sp, _, hsp, hprep⟩ := face_horizontal_parameter_bounds A B hh u _ hplus hpheight
  have hunit : faceUnit A B hh u ≠ 0 := by
    intro hz
    have := faceUnit_norm A B hh u
    rw [hz, norm_zero] at this
    norm_num at this
  have hsmEq : sm = s - δ := by
    have he : sm • faceUnit A B hh u = (s - δ) • faceUnit A B hh u := by
      have := hmrep.symm.trans hminusrep
      exact add_left_cancel this
    exact (smul_left_injective ℝ hunit) he
  have hspEq : sp = s + δ := by
    have he : sp • faceUnit A B hh u = (s + δ) • faceUnit A B hh u := by
      have := hprep.symm.trans hplusrep
      exact add_left_cancel this
    exact (smul_left_injective ℝ hunit) he
  constructor <;> linarith

/-- A full-face interior point has genuinely interior horizontal and vertical
coordinates in its physical source face. -/
private theorem source_interior_parameters (u : SourceIndex A B)
    {x : FaceSpace A B h (cycle A B u)}
    (hx : x ∈ interior (certificate A B hh (cycle A B u)).domain) :
    ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
      x = faceEntryAt A B hh t u +
        (s * retainedLowerRunCoeff A B hh t u) • faceUnit A B hh u := by
  let t := (certificate A B hh (cycle A B u)).height x
  have ht : 0 < t ∧ t < 1 := by
    apply FiniteWitnessClosure.interior_height_strict
      (F := (certificate A B hh (cycle A B u)).domain)
      (certificate A B hh (cycle A B u)).height
      (certificate A B hh (cycle A B u)).height_continuous
    · apply FiniteWitnessClosure.height_surjective_of_endpoints
        (certificate A B hh (cycle A B u)).height
        (faceEntryAt_height A B hh 0 u) (faceEntryAt_height A B hh 1 u)
    · intro y hy
      exact (certificate A B hh (cycle A B u)).height_bounds hy
    · exact hx
  obtain ⟨r, hr0, hr1, hrep⟩ := face_horizontal_parameter_bounds A B hh u x
    (interior_subset hx) rfl
  obtain ⟨hr0', hr1'⟩ := source_horizontal_strict A B hh u hx hrep
  have hw : 0 < retainedLowerRunCoeff A B hh t u :=
    retainedLowerRunCoeff_pos_of_mem_Ioo A B hh ⟨ht.1, ht.2⟩ u
  refine ⟨r / retainedLowerRunCoeff A B hh t u, t,
    div_pos hr0' hw, (div_lt_one hw).mpr hr1', ht.1, ht.2, ?_⟩
  rw [div_mul_cancel₀ r (ne_of_gt hw)]
  exact hrep

/-- Direct development of a source face agrees exactly with the selected-root
strip, with no quotient-angle or alignment ambiguity. -/
private theorem direct_source_point (k : Fin (N A B + 1)) (i : ℕ)
    (s t : ℝ) :
    directDevelopedMap A B hh k i
      (faceEntryAt A B hh t (familySource A B k i) +
        (s * retainedLowerRunCoeff A B hh t (familySource A B k i)) •
          faceUnit A B hh (familySource A B k i)) =
      (rootStrip A B hh k).point i s t := by
  let u := familySource A B k i
  have hentry : faceEntryAt A B hh t u =
      faceEntryLower A B hh u +
        t • (faceEntryUpper A B hh u - faceEntryLower A B hh u) := by
    simp only [faceEntryAt, AffineMap.lineMap_apply_module]
    module
  have hmap := (directDevelopedMap A B hh k i).map_vadd
    (faceEntryAt A B hh t u)
    ((s * retainedLowerRunCoeff A B hh t u) • faceUnit A B hh u)
  simp only [vadd_eq_add] at hmap
  have hforward : (directDevelopedMap A B hh k i).linearIsometry
      (faceUnit A B hh u) = developedForward A B hh k i := by
    change planeRotation (familyHeading A B hh k i)
      ((intrinsicFaceChart A B hh u).linearIsometryEquiv (faceUnit A B hh u)) = _
    rw [intrinsicFaceChart_linear_faceUnit]
    simp [developedForward, MixedTurnSafeCut.direction]
  have hline := (directDevelopedMap A B hh k i).map_vadd
    (faceEntryLower A B hh u)
    (t • (faceEntryUpper A B hh u - faceEntryLower A B hh u))
  simp only [vadd_eq_add] at hline
  rw [add_comm (t • (faceEntryUpper A B hh u - faceEntryLower A B hh u))
    (faceEntryLower A B hh u), ← hentry] at hline
  rw [hline, map_smul, map_smul, hforward] at hmap
  have hupper : (directDevelopedMap A B hh k i).linearIsometry
      (faceEntryUpper A B hh u - faceEntryLower A B hh u) =
      developedUpper A B hh k i - developedLower A B hh k i := by
    exact (directDevelopedMap A B hh k i).map_vsub _ _
  rw [hupper] at hmap
  change _ = developedLower A B hh k i +
    t • (developedUpper A B hh k i - developedLower A B hh k i) +
    (s * ((1-t) * lowerRunCoeff A B hh u + t * upperRunCoeff A B hh u)) •
      developedForward A B hh k i
  rw [show faceEntryAt A B hh t u +
      (s * retainedLowerRunCoeff A B hh t u) • faceUnit A B hh u =
      (s * retainedLowerRunCoeff A B hh t u) • faceUnit A B hh u +
        faceEntryAt A B hh t u by abel, hmap]
  change (s * retainedLowerRunCoeff A B hh t u) • developedForward A B hh k i +
      (t • (developedUpper A B hh k i - developedLower A B hh k i) +
        developedLower A B hh k i) = _
  simp only [retainedLowerRunCoeff]
  abel

private lemma transported_interior {u v : Side A B} (e : u = v)
    {x : FaceSpace A B h u} (hx : x ∈ interior (certificate A B hh u).domain) :
    transportFacePoint A B e x ∈ interior (certificate A B hh v).domain := by
  cases e
  exact hx

/-- Interior of an actual source face gives strict strip parameters and exact
direct-developed position, before the entry-cut source-order transport. -/
theorem direct_cycle_interior_witness (k : Fin (N A B + 1))
    (i : Fin (N A B + 1))
    (x : FaceSpace A B h (cycle A B (familySource A B k i.val)))
    (hx : x ∈ interior (certificate A B hh
      (cycle A B (familySource A B k i.val))).domain) :
    ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
      directDevelopedMap A B hh k i.val x = (rootStrip A B hh k).point i.val s t := by
  obtain ⟨s, t, hs0, hs1, ht0, ht1, hrep⟩ :=
    source_interior_parameters A B hh (familySource A B k i.val) hx
  refine ⟨s, t, hs0, hs1, ht0, ht1, ?_⟩
  rw [hrep]
  exact direct_source_point A B hh k i.val s t

/-- Identify the dependent entry-cut face with its physical source face. -/
theorem selected_source_order_eq (k : Fin (N A B + 1))
    (i : Fin (N A B + 1)) :
    order A B (prev (sourceIndexEquiv A B k)) i =
      cycle A B (familySource A B k i.val) := by
  exact order_eq_cycle_orderSource A B k i

/-- The selected entry-cut isometry is the direct source-face isometry after
transporting its argument along the source-order equality. -/
theorem selectedNegativeDirectMap_apply_source
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    (i : Fin (N A B + 1))
    (x : FaceSpace A B h (order A B (prev (sourceIndexEquiv A B
      (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ))) i)) :
    GeneralTwoRimUnfolding.selectedNegativeDirectMap A B hh hΔ i x =
      directDevelopedMap A B hh
        (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ) i.val
        (transportFacePoint A B
          (selected_source_order_eq A B
            (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ) i) x) := by
  let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
  let e := selected_source_order_eq A B k i
  have happ := transportFaceMap_apply A B
    (order_eq_cycle_orderSource A B k i)
    (GeneralTwoRimUnfolding.directOrderedMapAt A B hh k i) x
  change GeneralTwoRimUnfolding.selectedNegativeDirectMap A B hh hΔ i x = _
  exact happ

set_option maxHeartbeats 32000000
/-- Source-order transport of a strict original-face interior witness for any
physical root, independent of the sign of the defect. -/
theorem arbitraryCutFaceMap_source_interior_witness
    (k : Fin (N A B + 1)) (i : Fin (N A B + 1))
    (x : FaceSpace A B h (order A B (prev (sourceIndexEquiv A B k)) i))
    (hx : x ∈ interior (certificate A B hh
      (order A B (prev (sourceIndexEquiv A B k)) i)).domain) :
    ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
      GeneralTwoRimUnfolding.arbitraryCutFaceMap A B hh k i x =
        (rootStrip A B hh k).point i.val s t := by
  let e := selected_source_order_eq A B k i
  have hy : transportFacePoint A B e x ∈
      interior (certificate A B hh (cycle A B (familySource A B k i.val))).domain :=
    transported_interior A B hh e hx
  obtain ⟨s, t, hs0, hs1, ht0, ht1, heq⟩ :=
    direct_cycle_interior_witness A B hh k i (transportFacePoint A B e x) hy
  refine ⟨s, t, hs0, hs1, ht0, ht1, ?_⟩
  exact (transportFaceMap_apply A B (order_eq_cycle_orderSource A B k i)
    (GeneralTwoRimUnfolding.directOrderedMapAt A B hh k i) x).trans heq

/-- Strict source parameters of an interior point of any full direct face image. -/
theorem arbitraryCutFaceMap_image_interior_point
    (k : Fin (N A B + 1)) (i : Fin (N A B + 1)) {p : Plane}
    (hp : p ∈ interior (GeneralTwoRimUnfolding.arbitraryCutFaceMap A B hh k i ''
      (certificate A B hh (order A B (prev (sourceIndexEquiv A B k)) i)).domain)) :
    ∃ s t : ℝ, s ∈ Ioo (0 : ℝ) 1 ∧ t ∈ Ioo (0 : ℝ) 1 ∧
      p = (rootStrip A B hh k).point i.val s t := by
  let u := order A B (prev (sourceIndexEquiv A B k)) i
  let f := GeneralTwoRimUnfolding.arbitraryCutFaceMap A B hh k i
  let F := (certificate A B hh u).domain
  have hd : Module.finrank ℝ (FaceSpace A B h u) = Module.finrank ℝ Plane := by
    simpa [Plane, MixedTurnSafeCut.Plane] using faceSpace_finrank A B h u
  have heq : f '' interior F = interior (f '' F) :=
    FiniteWitnessClosure.embedding_image_interior
      (ι := Unit) (E := fun _ : Unit => FaceSpace A B h u) (Q := Plane)
      (i := ()) hd f F
  have hp' : p ∈ f '' interior F := by rw [heq]; exact hp
  obtain ⟨x, hx, hxp⟩ := hp'
  obtain ⟨s, t, hs0, hs1, ht0, ht1, hpoint⟩ :=
    arbitraryCutFaceMap_source_interior_witness A B hh k i x hx
  exact ⟨s, t, ⟨hs0, hs1⟩, ⟨ht0, ht1⟩, hxp.symm.trans hpoint⟩

/-- Pointwise source-order transport of the strict physical interior witness;
no embedding-interior or global safety claim is needed. -/
theorem selectedNegativeDirectMap_source_interior_witness
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    (i : Fin (N A B + 1))
    (x : FaceSpace A B h (order A B (prev (sourceIndexEquiv A B
      (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ))) i))
    (hx : x ∈ interior (certificate A B hh (order A B
      (prev (sourceIndexEquiv A B
        (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ))) i)).domain) :
    ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
      GeneralTwoRimUnfolding.selectedNegativeDirectMap A B hh hΔ i x =
        (rootStrip A B hh
          (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point i.val s t := by
  let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
  let e := selected_source_order_eq A B k i
  have hy : transportFacePoint A B e x ∈
      interior (certificate A B hh (cycle A B (familySource A B k i.val))).domain :=
    transported_interior A B hh e hx
  obtain ⟨s, t, hs0, hs1, ht0, ht1, heq⟩ :=
    direct_cycle_interior_witness A B hh k i (transportFacePoint A B e x) hy
  exact ⟨s, t, hs0, hs1, ht0, ht1,
    (selectedNegativeDirectMap_apply_source A B hh hΔ i x).trans heq⟩

/-- A point strictly inside the developed full face comes from a strictly
interior point of the original certificate domain. -/
theorem selectedNegativeDirectMap_image_interior_preimage
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    (i : Fin (N A B + 1)) {p : Plane}
    (hp : p ∈ interior (GeneralTwoRimUnfolding.selectedNegativeDirectMap
      A B hh hΔ i '' (certificate A B hh (order A B
        (prev (sourceIndexEquiv A B
          (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ))) i)).domain)) :
    ∃ x ∈ interior (certificate A B hh (order A B
      (prev (sourceIndexEquiv A B
        (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ))) i)).domain,
      GeneralTwoRimUnfolding.selectedNegativeDirectMap A B hh hΔ i x = p := by
  let u := order A B (prev (sourceIndexEquiv A B
    (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ))) i
  let f := GeneralTwoRimUnfolding.selectedNegativeDirectMap A B hh hΔ i
  let F := (certificate A B hh u).domain
  have hd : Module.finrank ℝ (FaceSpace A B h u) = Module.finrank ℝ Plane := by
    simpa [Plane, MixedTurnSafeCut.Plane] using faceSpace_finrank A B h u
  have heq : f '' interior F = interior (f '' F) :=
    FiniteWitnessClosure.embedding_image_interior
      (ι := Unit) (E := fun _ : Unit => FaceSpace A B h u) (Q := Plane)
      (i := ()) hd f F
  change p ∈ interior (f '' F) at hp
  have hp' : p ∈ f '' interior F := by rw [heq]; exact hp
  exact hp'

/-- Strict planar-image interior points have strict selected-root strip
coordinates; the point equality is for the actual selected direct map. -/
theorem selectedNegativeDirectMap_image_interior_point
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    (i : Fin (N A B + 1)) {p : Plane}
    (hp : p ∈ interior (GeneralTwoRimUnfolding.selectedNegativeDirectMap
      A B hh hΔ i '' (certificate A B hh (order A B
        (prev (sourceIndexEquiv A B
          (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ))) i)).domain)) :
    ∃ s t : ℝ, s ∈ Ioo (0 : ℝ) 1 ∧ t ∈ Ioo (0 : ℝ) 1 ∧
      p = (rootStrip A B hh
        (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point i.val s t := by
  obtain ⟨x, hx, hxp⟩ :=
    selectedNegativeDirectMap_image_interior_preimage A B hh hΔ i hp
  obtain ⟨s, t, hs0, hs1, ht0, ht1, heq⟩ :=
    selectedNegativeDirectMap_source_interior_witness A B hh hΔ i x hx
  exact ⟨s, t, ⟨hs0, hs1⟩, ⟨ht0, ht1⟩, hxp.symm.trans heq⟩

/-- Every strict developed-face interior point is an actual positive-radius
material hit at a real representative, chosen as the selected polar lift itself. -/
theorem selectedNegativeDirectMap_image_interior_hit
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    (i : Fin (N A B + 1)) {p : Plane}
    (hp : p ∈ interior (GeneralTwoRimUnfolding.selectedNegativeDirectMap
      A B hh hΔ i '' (certificate A B hh (order A B
        (prev (sourceIndexEquiv A B
          (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ))) i)).domain)) :
    ∃ (s t β : ℝ) (m : ℤ), s ∈ Ioo (0 : ℝ) 1 ∧ t ∈ Ioo (0 : ℝ) 1 ∧
      p = (rootStrip A B hh
        (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point i.val s t ∧
      0 < ‖p - PhysicalMixedTurnSource.circuitPole A B hh
        (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ) (ne_of_lt hΔ)‖ ∧
      SelectedMaterialHit A B hh hΔ β m i.val s t := by
  obtain ⟨s, t, hs, ht, heq⟩ :=
    selectedNegativeDirectMap_image_interior_point A B hh hΔ i hp
  let β := selectedPointPolarLift A B hh hΔ i.val s t
  refine ⟨s, t, β, 0, hs, ht, heq, ?_, ?_⟩
  · rw [heq]
    exact (selectedPointPolarLift_decomposition A B hh hΔ
      (by omega : i.val ≤ N A B)
      ⟨hs.1.le, hs.2.le⟩ ⟨ht.1.le, ht.2.le⟩).2
  · exact ⟨by omega, ⟨hs.1.le, hs.2.le⟩, ht, by simp [β]⟩

/-- The two actual selected-root lifts of one non-pole planar point differ by
an integral full turn. Positivity of the physical radii fixes the direction. -/
private theorem selected_interior_lifts_same_ray
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0)
    {i j : ℕ} {s t s' t' : ℝ}
    (hi : i ≤ N A B) (hj : j ≤ N A B)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hs' : s' ∈ Icc (0 : ℝ) 1) (ht' : t' ∈ Icc (0 : ℝ) 1)
    (heq : (rootStrip A B hh
        (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point i s t =
      (rootStrip A B hh
        (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point j s' t') :
    ∃ m : ℤ, selectedPointPolarLift A B hh hΔ j s' t' =
      selectedPointPolarLift A B hh hΔ i s t + 2 * Real.pi * (m : ℝ) := by
  let k := GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ
  let O := PhysicalMixedTurnSource.circuitPole A B hh k (ne_of_lt hΔ)
  let p := (rootStrip A B hh k).point i s t
  let φ := selectedPointPolarLift A B hh hΔ i s t
  let ψ := selectedPointPolarLift A B hh hΔ j s' t'
  have hd₁ := selectedPointPolarLift_decomposition A B hh hΔ hi hs ht
  have hd₂ := selectedPointPolarLift_decomposition A B hh hΔ hj hs' ht'
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

/-- No two distinct full selected negative-root face images have intersecting
interiors. The maps and radial seam are the actual selected direct family. -/
theorem selectedNegativeDirectMap_full_safe
    (hΔ : PhysicalMixedTurnSource.intrinsicDelta A B (hh := hh) < 0) :
    Safe
      (fun i => (certificate A B hh (order A B
        (prev (sourceIndexEquiv A B
          (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ))) i)).domain)
      (fun i => GeneralTwoRimUnfolding.selectedNegativeDirectMap A B hh hΔ i) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro p hp hq
  obtain ⟨s, t, β, m₁, hs, ht, hp', _, hit₁⟩ :=
    selectedNegativeDirectMap_image_interior_hit A B hh hΔ i hp
  obtain ⟨s', t', β', m₂, hs', ht', hq', _, hit₂⟩ :=
    selectedNegativeDirectMap_image_interior_hit A B hh hΔ j hq
  have heq : (rootStrip A B hh
      (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point i.val s t =
    (rootStrip A B hh
      (GeneralTwoRimUnfolding.selectedNegativeCutIndex A B hh hΔ)).point j.val s' t' :=
    hp'.symm.trans hq'
  obtain ⟨m, hm⟩ := selected_interior_lifts_same_ray A B hh hΔ
    hit₁.1 hit₂.1
    ⟨hs.1.le, hs.2.le⟩ ⟨ht.1.le, ht.2.le⟩
    ⟨hs'.1.le, hs'.2.le⟩ ⟨ht'.1.le, ht'.2.le⟩ heq
  have hit₂' : SelectedMaterialHit A B hh hΔ β (m₁ + m) j.val s' t' := by
    refine ⟨hit₂.1, hit₂.2.1, hit₂.2.2.1, ?_⟩
    rw [hit₁.2.2.2] at hm
    convert hm using 1
    push_cast
    ring
  exact (selectedMaterialHit_distinct_faceInteriors_ne A B hh hΔ β hit₁ hit₂'
    (fun h => hij (Fin.ext h)) hs hs') heq

#print selectedNegativeDirectMap_full_safe
#print axioms selectedNegativeDirectMap_full_safe
#print selectedNegativeDirectMap_image_interior_preimage
#print axioms selectedNegativeDirectMap_image_interior_preimage
#print selectedNegativeDirectMap_image_interior_point
#print axioms selectedNegativeDirectMap_image_interior_point
#print selectedNegativeDirectMap_image_interior_hit
#print axioms selectedNegativeDirectMap_image_interior_hit
#print direct_cycle_interior_witness
#print axioms direct_cycle_interior_witness
#print selectedNegativeDirectMap_apply_source
#print axioms selectedNegativeDirectMap_apply_source
#print selectedNegativeDirectMap_source_interior_witness
#print axioms selectedNegativeDirectMap_source_interior_witness
end
end SelectedNegativeRootPolar
