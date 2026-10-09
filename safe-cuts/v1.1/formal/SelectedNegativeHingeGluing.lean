import ArbitraryCutDirectMap

open Set
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CommonSupportMerge OriginalFacetCertificates NormalFanSplice MaximalSupportCells
open CyclicCutOrders EuclideanPrismatoidCoordinates PolyhedralInputBridge
open TrimmedFacetWitnesses BandGeometryAssembly FiniteWitnessClosure SingleCutRecovery
open CutSurfaceQuotient MixedTurnSafeCut PolygonSetReconstruction ConvexPolygonTurning
open PhysicalMixedTurnSource

namespace GeneralTwoRimUnfolding
noncomputable section
set_option maxHeartbeats 2000000

variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

/-- The consecutive order entries have precisely the physical exit and entry
source coordinates; the terminal seam is not a consecutive pair here. -/
private lemma chain_source_coordinates (k : Fin (MechanismN A B + 1))
    (j : Fin (sideCount A B - 1)) :
    orderSource A B k j.castSucc = familySource A B k j.val ∧
    orderSource A B k j.succ = familySource A B k (j.val + 1) ∧
    orderSource A B k j.succ = next (orderSource A B k j.castSucc) := by
  have h₀ : orderSource A B k j.castSucc = familySource A B k j.val :=
    orderSource_eq_familySource A B k j.castSucc
  have h₁ : orderSource A B k j.succ = familySource A B k (j.val + 1) :=
    orderSource_eq_familySource A B k j.succ
  exact ⟨h₀, h₁, by rw [h₀, h₁, familySource_succ]⟩

/-- Transport along the two dependent face-label equalities preserves both
physical material points and the values of the developed isometries. -/
private lemma transported_hinge_points
    {u₀ v₀ u₁ v₁ : Side A B} (h₀ : u₀ = v₀) (h₁ : u₁ = v₁)
    (f₀ : FaceSpace A B h v₀ →ᵃⁱ[ℝ] PhysicalMixedTurnSource.Plane)
    (f₁ : FaceSpace A B h v₁ →ᵃⁱ[ℝ] PhysicalMixedTurnSource.Plane)
    (x : FaceSpace A B h u₀) (y : FaceSpace A B h u₁)
    (hxy : (certificate A B hh u₀).chart x =
      (certificate A B hh u₁).chart y) :
    (certificate A B hh v₀).chart (transportFacePoint A B h₀ x) =
      (certificate A B hh v₁).chart (transportFacePoint A B h₁ y) ∧
    transportFaceMap A B h₀ f₀ x = f₀ (transportFacePoint A B h₀ x) ∧
    transportFaceMap A B h₁ f₁ y = f₁ (transportFacePoint A B h₁ y) := by
  exact ⟨by simpa only [transportFacePoint_chart] using hxy,
    transportFaceMap_apply A B h₀ f₀ x,
    transportFaceMap_apply A B h₁ f₁ y⟩

private lemma transported_domain {u v : Side A B} (huv : u = v)
    {x : FaceSpace A B h u}
    (hx : x ∈ (certificate A B hh u).domain) :
    transportFacePoint A B huv x ∈ (certificate A B hh v).domain := by
  subst v
  exact hx

/-- The direct maps on consecutive source faces coincide on every point of
their actual original common material hinge, including both endpoints. -/
theorem direct_chain_full_hinge (k : Fin (MechanismN A B + 1))
    (j : Fin (sideCount A B - 1))
    (x : FaceSpace A B h (cycle A B (orderSource A B k j.castSucc)))
    (y : FaceSpace A B h (cycle A B (orderSource A B k j.succ)))
    (hx : x ∈ (certificate A B hh (cycle A B
      (orderSource A B k j.castSucc))).domain)
    (hy : y ∈ (certificate A B hh (cycle A B
      (orderSource A B k j.succ))).domain)
    (hxy : (certificate A B hh (cycle A B
      (orderSource A B k j.castSucc))).chart x =
      (certificate A B hh (cycle A B
        (orderSource A B k j.succ))).chart y) :
    directOrderedMapAt A B hh k j.castSucc x =
      directOrderedMapAt A B hh k j.succ y := by
  obtain ⟨hs₀, hs₁, hnext⟩ := chain_source_coordinates A B k j
  let s₀ := orderSource A B k j.castSucc
  let s₁ := orderSource A B k j.succ
  have hn : s₁ = next s₀ := hnext
  let t := (certificate A B hh (cycle A B s₀)).height x
  have hty : (certificate A B hh (cycle A B s₁)).height y = t := by
    change heightLinear h ((certificate A B hh (cycle A B s₁)).chart y) = t
    rw [← hxy]
    rfl
  have hyown := (certificate A B hh (cycle A B s₁)).own_zero y
  change sideRow A B h (cycle A B s₁).val
    ((certificate A B hh (cycle A B s₁)).chart y) = 0 at hyown
  have hxnext : sideRow A B h (cycle A B (next s₀)).val
      ((certificate A B hh (cycle A B s₀)).chart x) = 0 := by
    rw [← hn, hxy]
    exact hyown
  have hxeq := face_eq_exitAt_of_nextRow_zero A B hh s₀ x hx rfl hxnext
  have hxown := (certificate A B hh (cycle A B s₀)).own_zero x
  change sideRow A B h (cycle A B s₀).val
    ((certificate A B hh (cycle A B s₀)).chart x) = 0 at hxown
  have hyprev : sideRow A B h (cycle A B (prev s₁)).val
      ((certificate A B hh (cycle A B s₁)).chart y) = 0 := by
    have hp : prev s₁ = s₀ := by rw [hn, prev_next]
    rw [hp, ← hxy]
    exact hxown
  have hyeq := face_eq_entryAt_of_prevRow_zero A B hh s₁ y hy hty hyprev
  change directDevelopedMap A B hh k j.val x =
    directDevelopedMap A B hh k (j.val + 1) y
  rw [hxeq, hyeq]
  change directDevelopedMap A B hh k j.val (faceExitAt A B hh t s₀) =
    directDevelopedMap A B hh k (j.val + 1) (faceEntryAt A B hh t s₁)
  exact directDevelopedMap_exitAt_eq_next_entryAt A B hh k j.val t

/-- Full original-domain gluing, packaged to keep theorem statements small. -/
private def AdjacentFullGlue (k : Fin (MechanismN A B + 1))
    (j : Fin (sideCount A B - 1))
    (f₀ : FaceSpace A B h
      (order A B (prev (sourceIndexEquiv A B k)) j.castSucc) →ᵃⁱ[ℝ]
        PhysicalMixedTurnSource.Plane)
    (f₁ : FaceSpace A B h
      (order A B (prev (sourceIndexEquiv A B k)) j.succ) →ᵃⁱ[ℝ]
        PhysicalMixedTurnSource.Plane) : Prop :=
  ∀ x ∈ (certificate A B hh
      (order A B (prev (sourceIndexEquiv A B k)) j.castSucc)).domain,
  ∀ y ∈ (certificate A B hh
      (order A B (prev (sourceIndexEquiv A B k)) j.succ)).domain,
    (certificate A B hh
      (order A B (prev (sourceIndexEquiv A B k)) j.castSucc)).chart x =
    (certificate A B hh
      (order A B (prev (sourceIndexEquiv A B k)) j.succ)).chart y →
      f₀ x = f₁ y

/-- The arbitrary entry-cut maps glue on the entire original common hinge
for each consecutive pair, with no terminal-seam claim. -/
theorem arbitraryCutFaceMap_adjacent_full_glue
    (k : Fin (MechanismN A B + 1)) (j : Fin (sideCount A B - 1)) :
    AdjacentFullGlue A B hh k j
      (arbitraryCutFaceMap A B hh k j.castSucc)
      (arbitraryCutFaceMap A B hh k j.succ) := by
  change AdjacentFullGlue A B hh k j
    (transportFaceMap A B (order_eq_cycle_orderSource A B k j.castSucc)
      (directOrderedMapAt A B hh k j.castSucc))
    (transportFaceMap A B (order_eq_cycle_orderSource A B k j.succ)
      (directOrderedMapAt A B hh k j.succ))
  unfold AdjacentFullGlue
  apply transportFaceMap_full_glue A B hh
    (order_eq_cycle_orderSource A B k j.castSucc)
    (order_eq_cycle_orderSource A B k j.succ)
  intro x hx y hy hxy
  exact direct_chain_full_hinge A B hh k j x y hx hy hxy

/-- The selected negative direct maps glue on every consecutive original hinge. -/
theorem selectedNegativeDirectMap_adjacent_full_glue
    (hΔ : intrinsicDelta A B (hh := hh) < 0)
    (j : Fin (sideCount A B - 1)) :
    AdjacentFullGlue A B hh (selectedNegativeCutIndex A B hh hΔ) j
      (selectedNegativeDirectMap A B hh hΔ j.castSucc)
      (selectedNegativeDirectMap A B hh hΔ j.succ) := by
  change AdjacentFullGlue A B hh (selectedNegativeCutIndex A B hh hΔ) j
    (arbitraryCutFaceMap A B hh (selectedNegativeCutIndex A B hh hΔ) j.castSucc)
    (arbitraryCutFaceMap A B hh (selectedNegativeCutIndex A B hh hΔ) j.succ)
  exact arbitraryCutFaceMap_adjacent_full_glue A B hh
    (selectedNegativeCutIndex A B hh hΔ) j

#print direct_chain_full_hinge
#print axioms arbitraryCutFaceMap_adjacent_full_glue
#print axioms selectedNegativeDirectMap_adjacent_full_glue
#print axioms direct_chain_full_hinge

end
end GeneralTwoRimUnfolding
