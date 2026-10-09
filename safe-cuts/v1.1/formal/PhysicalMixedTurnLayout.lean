import PhysicalMixedTurnTransport

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

set_option maxHeartbeats 4000000 in
theorem ordered_fixedCut_safe (hmix : IntrinsicTMixed A B hh)
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2) :
    Safe
      (fun i : Fin (MechanismN A B+1) =>
        heightTrim (certificate A B hh (cycle A B
          (orderSource A B (fixedCutIndex A B hh hmix) i))).domain
          (certificate A B hh (cycle A B
            (orderSource A B (fixedCutIndex A B hh hmix) i))).height d)
      (fun i => orderedDevelopedMap A B hh hmix d i) := by
  intro i j hij
  change Disjoint (interior (orderedDevelopedMap A B hh hmix d i '' _))
    (interior (orderedDevelopedMap A B hh hmix d j '' _))
  rw [orderedDevelopedMap_heightTrim_image A B hh hmix hd0 hd1,
    orderedDevelopedMap_heightTrim_image A B hh hmix hd0 hd1]
  exact fixedCut_nonoverlap A B hh hmix hd0 hd1 i j hij

set_option maxHeartbeats 4000000 in
theorem ordered_fixedCut_developmentOn (hmix : IntrinsicTMixed A B hh)
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2) :
    DevelopmentOn
      (fun i : Fin (MechanismN A B+1) =>
        (certificate A B hh (cycle A B
          (orderSource A B (fixedCutIndex A B hh hmix) i))).chart.toAffineMap)
      (fun i : Fin (sideCount A B-1+1) =>
        heightTrim (certificate A B hh (cycle A B
          (orderSource A B (fixedCutIndex A B hh hmix) i))).domain
          (certificate A B hh (cycle A B
            (orderSource A B (fixedCutIndex A B hh hmix) i))).height d)
      (fun i => orderedDevelopedMap A B hh hmix d i) := by
  constructor
  · intro j x hx y hy hxy
    let k := fixedCutIndex A B hh hmix
    let s0 := orderSource A B k j.castSucc
    let s1 := orderSource A B k j.succ
    have hs0 : s0 = familySource A B k j.val :=
      by simpa [s0] using orderSource_eq_familySource A B k j.castSucc
    have hs1 : s1 = familySource A B k (j.val+1) := by
      simpa [s1] using orderSource_eq_familySource A B k j.succ
    have hnext : s1 = next s0 := by rw [hs0, hs1, familySource_succ]
    change (certificate A B hh (cycle A B
        (orderSource A B (fixedCutIndex A B hh hmix) j.castSucc))).chart x =
      (certificate A B hh (cycle A B
        (orderSource A B (fixedCutIndex A B hh hmix) j.succ))).chart y at hxy
    have hxy' : (certificate A B hh (cycle A B s0)).chart x =
        (certificate A B hh (cycle A B s1)).chart y := by
      simpa [s0, s1, k] using hxy
    let t := (certificate A B hh (cycle A B s0)).height x
    have hty : (certificate A B hh (cycle A B s1)).height y = t := by
      change heightLinear h ((certificate A B hh (cycle A B s1)).chart y) = t
      rw [← hxy']
      rfl
    have hyown := (certificate A B hh (cycle A B s1)).own_zero y
    change sideRow A B h (cycle A B s1).val
      ((certificate A B hh (cycle A B s1)).chart y) = 0 at hyown
    have hxnext : sideRow A B h (cycle A B (next s0)).val
        ((certificate A B hh (cycle A B s0)).chart x) = 0 := by
      rw [← hnext, hxy']
      exact hyown
    have hxeq := face_eq_exitAt_of_nextRow_zero A B hh s0 x hx.1 rfl hxnext
    have hxown := (certificate A B hh (cycle A B s0)).own_zero x
    change sideRow A B h (cycle A B s0).val
      ((certificate A B hh (cycle A B s0)).chart x) = 0 at hxown
    have hyprev : sideRow A B h (cycle A B (prev s1)).val
        ((certificate A B hh (cycle A B s1)).chart y) = 0 := by
      have hp : prev s1 = s0 := by rw [hnext, prev_next]
      rw [hp, ← hxy']
      exact hxown
    have hyeq := face_eq_entryAt_of_prevRow_zero A B hh s1 y hy.1 hty hyprev
    rw [hxeq, hyeq]
    change planarPlacement (familyHeading A B hh k j.val)
        (localB A B hh d s0) (familyB A B hh d k j.val)
        (intrinsicFaceChart A B hh s0 (faceExitAt A B hh t s0)) =
      planarPlacement (familyHeading A B hh k (j.val+1))
        (localB A B hh d s1) (familyB A B hh d k (j.val+1))
        (intrinsicFaceChart A B hh s1 (faceEntryAt A B hh t s1))
    rw [hs0, hs1]
    have hg := developedMap_exitAt_eq_next_entryAt A B hh hd0 hd1
      k j.val (by omega) t
    change planarPlacement (familyHeading A B hh k j.val)
        (localB A B hh d (familySource A B k j.val))
        (familyB A B hh d k j.val)
        (intrinsicFaceChart A B hh (familySource A B k j.val)
          (faceExitAt A B hh t (familySource A B k j.val))) =
      planarPlacement (familyHeading A B hh k (j.val+1))
        (localB A B hh d (familySource A B k (j.val+1)))
        (familyB A B hh d k (j.val+1))
        (intrinsicFaceChart A B hh (familySource A B k (j.val+1))
          (faceEntryAt A B hh t (familySource A B k (j.val+1)))) at hg
    exact hg
  · intro j
    exact ordered_fixedCut_safe A B hh hmix hd0 hd1 j.castSucc j.succ (by
      intro he
      have hv := congrArg Fin.val he
      simp at hv)

noncomputable def transportFaceMap {u v : Side A B} (huv : u = v)
    (f : FaceSpace A B h v →ᵃⁱ[ℝ] Plane) : FaceSpace A B h u →ᵃⁱ[ℝ] Plane := by
  subst v
  exact f

lemma transportFaceMap_image_heightTrim {u v : Side A B} (huv : u = v)
    (f : FaceSpace A B h v →ᵃⁱ[ℝ] Plane) (d : ℝ) :
    transportFaceMap A B huv f ''
        heightTrim (certificate A B hh u).domain (certificate A B hh u).height d =
      f '' heightTrim (certificate A B hh v).domain
        (certificate A B hh v).height d := by
  subst v
  rfl

noncomputable def transportFacePoint {u v : Side A B} (huv : u = v) :
    FaceSpace A B h u → FaceSpace A B h v := by
  subst v
  exact id

@[simp] lemma transportFacePoint_chart {u v : Side A B} (huv : u = v)
    (x : FaceSpace A B h u) :
    (certificate A B hh v).chart (transportFacePoint A B huv x) =
      (certificate A B hh u).chart x := by
  subst v
  rfl

@[simp] lemma transportFacePoint_height {u v : Side A B} (huv : u = v)
    (x : FaceSpace A B h u) :
    (certificate A B hh v).height (transportFacePoint A B huv x) =
      (certificate A B hh u).height x := by
  subst v
  rfl

lemma transportFacePoint_mem_heightTrim {u v : Side A B} (huv : u = v)
    {d : ℝ} {x : FaceSpace A B h u}
    (hx : x ∈ heightTrim (certificate A B hh u).domain
      (certificate A B hh u).height d) :
    transportFacePoint A B huv x ∈
      heightTrim (certificate A B hh v).domain
        (certificate A B hh v).height d := by
  subst v
  exact hx

@[simp] lemma transportFaceMap_apply {u v : Side A B} (huv : u = v)
    (f : FaceSpace A B h v →ᵃⁱ[ℝ] Plane) (x : FaceSpace A B h u) :
    transportFaceMap A B huv f x = f (transportFacePoint A B huv x) := by
  subst v
  rfl

noncomputable def cutOrderedMap (hmix : IntrinsicTMixed A B hh) (d : ℝ)
    (i : Fin (sideCount A B-1+1)) :
    FaceSpace A B h (order A B
      (prev (sourceIndexEquiv A B (fixedCutIndex A B hh hmix))) i) →ᵃⁱ[ℝ] Plane := by
  let huv := order_eq_cycle_orderSource A B (fixedCutIndex A B hh hmix) i
  exact transportFaceMap A B huv (orderedDevelopedMap A B hh hmix d i)

/-- The directly constructed, trim-independent map family in the existing
`order (k-1)` source cut convention. -/
noncomputable def directCutOrderedMap (hmix : IntrinsicTMixed A B hh)
    (i : Fin (sideCount A B-1+1)) :
    FaceSpace A B h (order A B
      (prev (sourceIndexEquiv A B (fixedCutIndex A B hh hmix))) i) →ᵃⁱ[ℝ] Plane := by
  let huv := order_eq_cycle_orderSource A B (fixedCutIndex A B hh hmix) i
  exact transportFaceMap A B huv (orderedDirectMap A B hh hmix i)

/-- Every positive-trim map used in the old layout is the direct map up to the
same global root translation.  This is the precise cancellation statement
needed to transfer the already proved nonoverlap to the direct family. -/
theorem directCutOrderedMap_eq_cutOrderedMap_add_root
    (hmix : IntrinsicTMixed A B hh) (d : ℝ)
    (i : Fin (sideCount A B-1+1))
    (x : FaceSpace A B h (order A B
      (prev (sourceIndexEquiv A B (fixedCutIndex A B hh hmix))) i)) :
    directCutOrderedMap A B hh hmix i x = cutOrderedMap A B hh hmix d i x +
      localB A B hh d
        (familySource A B (fixedCutIndex A B hh hmix) 0) := by
  rw [show directCutOrderedMap A B hh hmix i = transportFaceMap A B
      (order_eq_cycle_orderSource A B (fixedCutIndex A B hh hmix) i)
      (orderedDirectMap A B hh hmix i) by rfl]
  rw [show cutOrderedMap A B hh hmix d i = transportFaceMap A B
      (order_eq_cycle_orderSource A B (fixedCutIndex A B hh hmix) i)
      (orderedDevelopedMap A B hh hmix d i) by rfl]
  rw [transportFaceMap_apply, transportFaceMap_apply]
  exact orderedDirectMap_eq_orderedDevelopedMap_add_root A B hh hmix d i _

lemma cutOrderedMap_heightTrim_image (hmix : IntrinsicTMixed A B hh)
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2)
    (i : Fin (sideCount A B-1+1)) :
    cutOrderedMap A B hh hmix d i ''
        heightTrim (certificate A B hh (order A B
          (prev (sourceIndexEquiv A B (fixedCutIndex A B hh hmix))) i)).domain
          (certificate A B hh (order A B
            (prev (sourceIndexEquiv A B (fixedCutIndex A B hh hmix))) i)).height d =
      (physicalDevelopedFamily A B hh hd0 hd1).face
        (fixedCutIndex A B hh hmix) i := by
  rw [show cutOrderedMap A B hh hmix d i =
      transportFaceMap A B
        (order_eq_cycle_orderSource A B (fixedCutIndex A B hh hmix) i)
        (orderedDevelopedMap A B hh hmix d i) by rfl]
  rw [transportFaceMap_image_heightTrim A B hh]
  exact orderedDevelopedMap_heightTrim_image A B hh hmix hd0 hd1 i

lemma transportFaceMap_trimmed_glue {u₀ v₀ u₁ v₁ : Side A B}
    (h₀ : u₀ = v₀) (h₁ : u₁ = v₁)
    (f₀ : FaceSpace A B h v₀ →ᵃⁱ[ℝ] Plane)
    (f₁ : FaceSpace A B h v₁ →ᵃⁱ[ℝ] Plane) (d : ℝ)
    (hg : ∀ x ∈ heightTrim (certificate A B hh v₀).domain
        (certificate A B hh v₀).height d,
      ∀ y ∈ heightTrim (certificate A B hh v₁).domain
          (certificate A B hh v₁).height d,
        (certificate A B hh v₀).chart x = (certificate A B hh v₁).chart y →
          f₀ x = f₁ y) :
    ∀ x ∈ heightTrim (certificate A B hh u₀).domain
        (certificate A B hh u₀).height d,
      ∀ y ∈ heightTrim (certificate A B hh u₁).domain
          (certificate A B hh u₁).height d,
        (certificate A B hh u₀).chart x = (certificate A B hh u₁).chart y →
          transportFaceMap A B h₀ f₀ x = transportFaceMap A B h₁ f₁ y := by
  intro x hx y hy hxy
  rw [transportFaceMap_apply A B, transportFaceMap_apply A B]
  apply hg (transportFacePoint A B h₀ x)
    (transportFacePoint_mem_heightTrim A B hh h₀ hx)
    (transportFacePoint A B h₁ y)
    (transportFacePoint_mem_heightTrim A B hh h₁ hy)
  simpa using hxy

set_option maxHeartbeats 4000000 in
theorem cutOrderedMap_hinge_glued (hmix : IntrinsicTMixed A B hh)
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2) :
    ∀ (j : Fin (sideCount A B-1)) (t : ℝ), t ∈ Icc d (1-d) →
      cutOrderedMap A B hh hmix d j.castSucc
          (AffineMap.lineMap (hinge A B hh
            (prev (sourceIndexEquiv A B (fixedCutIndex A B hh hmix))) j).aL
            (hinge A B hh
              (prev (sourceIndexEquiv A B (fixedCutIndex A B hh hmix))) j).bL t) =
        cutOrderedMap A B hh hmix d j.succ
          (AffineMap.lineMap (hinge A B hh
            (prev (sourceIndexEquiv A B (fixedCutIndex A B hh hmix))) j).aR
            (hinge A B hh
              (prev (sourceIndexEquiv A B (fixedCutIndex A B hh hmix))) j).bR t) := by
  intro j t ht
  let e := prev (sourceIndexEquiv A B (fixedCutIndex A B hh hmix))
  let ed := hinge A B hh e j
  have hp :
      (certificate A B hh (order A B e j.castSucc)).chart
          (AffineMap.lineMap ed.aL ed.bL t) ∈
        ((certificate A B hh (order A B e j.castSucc)).chart ''
          heightTrim (certificate A B hh (order A B e j.castSucc)).domain
            (certificate A B hh (order A B e j.castSucc)).height d) ∩
        ((certificate A B hh (order A B e j.succ)).chart ''
          heightTrim (certificate A B hh (order A B e j.succ)).domain
            (certificate A B hh (order A B e j.succ)).height d) := by
    rw [(hinge A B hh e j).common_trimmed_edge
      (faceSpace_finrank A B h _) hd0 hd1]
    refine ⟨t, ht, ?_⟩
    exact ((certificate A B hh
      (order A B e j.castSucc)).chart.toAffineMap.apply_lineMap _ _ _).symm
  obtain ⟨⟨x, hx, hxp⟩, ⟨y, hy, hyp⟩⟩ := hp
  have hxline : x = AffineMap.lineMap ed.aL ed.bL t := by
    apply (certificate A B hh (order A B e j.castSucc)).chart.injective
    exact hxp
  have hyline : y = AffineMap.lineMap ed.aR ed.bR t := by
    apply (certificate A B hh (order A B e j.succ)).chart.injective
    calc
      (certificate A B hh (order A B e j.succ)).chart y =
          (certificate A B hh (order A B e j.castSucc)).chart
            (AffineMap.lineMap ed.aL ed.bL t) := hyp
      _ = AffineMap.lineMap
          ((certificate A B hh (order A B e j.castSucc)).chart ed.aL)
          ((certificate A B hh (order A B e j.castSucc)).chart ed.bL) t :=
        (certificate A B hh
          (order A B e j.castSucc)).chart.toAffineMap.apply_lineMap _ _ _
      _ = AffineMap.lineMap
          ((certificate A B hh (order A B e j.succ)).chart ed.aR)
          ((certificate A B hh (order A B e j.succ)).chart ed.bR) t := by
        rw [ed.match_a, ed.match_b]
      _ = (certificate A B hh (order A B e j.succ)).chart
          (AffineMap.lineMap ed.aR ed.bR t) :=
        ((certificate A B hh
          (order A B e j.succ)).chart.toAffineMap.apply_lineMap _ _ _).symm
  rw [← hxline, ← hyline]
  apply transportFaceMap_trimmed_glue A B hh
    (order_eq_cycle_orderSource A B (fixedCutIndex A B hh hmix) j.castSucc)
    (order_eq_cycle_orderSource A B (fixedCutIndex A B hh hmix) j.succ)
    (orderedDevelopedMap A B hh hmix d j.castSucc)
    (orderedDevelopedMap A B hh hmix d j.succ) d
    ((ordered_fixedCut_developmentOn A B hh hmix hd0 hd1).1 j)
    x hx y hy (hxp.trans hyp.symm)

/-- The same whole retained hinge is glued by the direct maps.  The common root
translation cancels, so this is not a fresh per-depth normalization. -/
theorem directCutOrderedMap_hinge_glued (hmix : IntrinsicTMixed A B hh)
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2) :
    ∀ (j : Fin (sideCount A B-1)) (t : ℝ), t ∈ Icc d (1-d) →
      directCutOrderedMap A B hh hmix j.castSucc
          (AffineMap.lineMap (hinge A B hh
            (prev (sourceIndexEquiv A B (fixedCutIndex A B hh hmix))) j).aL
            (hinge A B hh
              (prev (sourceIndexEquiv A B (fixedCutIndex A B hh hmix))) j).bL t) =
        directCutOrderedMap A B hh hmix j.succ
          (AffineMap.lineMap (hinge A B hh
            (prev (sourceIndexEquiv A B (fixedCutIndex A B hh hmix))) j).aR
            (hinge A B hh
              (prev (sourceIndexEquiv A B (fixedCutIndex A B hh hmix))) j).bR t) := by
  intro j t ht
  rw [directCutOrderedMap_eq_cutOrderedMap_add_root A B hh hmix d,
    directCutOrderedMap_eq_cutOrderedMap_add_root A B hh hmix d,
    cutOrderedMap_hinge_glued A B hh hmix hd0 hd1 j t ht]

set_option maxHeartbeats 8000000 in
theorem cutOrdered_safe (hmix : IntrinsicTMixed A B hh)
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2) :
    Safe
      (fun i : Fin (sideCount A B-1+1) =>
        heightTrim (certificate A B hh (order A B
          (prev (sourceIndexEquiv A B (fixedCutIndex A B hh hmix))) i)).domain
          (certificate A B hh (order A B
            (prev (sourceIndexEquiv A B (fixedCutIndex A B hh hmix))) i)).height d)
      (fun i => cutOrderedMap A B hh hmix d i) := by
  intro i j hij
  change Disjoint (interior (cutOrderedMap A B hh hmix d i '' _))
    (interior (cutOrderedMap A B hh hmix d j '' _))
  rw [cutOrderedMap_heightTrim_image A B hh hmix hd0 hd1,
    cutOrderedMap_heightTrim_image A B hh hmix hd0 hd1]
  exact fixedCut_nonoverlap A B hh hmix hd0 hd1 i j hij

/-- Trim safety for the directly constructed maps.  It is transferred through
the proved common-translation equality, never by selecting recovered maps. -/
theorem directCutOrdered_safe (hmix : IntrinsicTMixed A B hh)
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2) :
    Safe
      (fun i : Fin (sideCount A B-1+1) =>
        heightTrim (certificate A B hh (order A B
          (prev (sourceIndexEquiv A B (fixedCutIndex A B hh hmix))) i)).domain
          (certificate A B hh (order A B
            (prev (sourceIndexEquiv A B (fixedCutIndex A B hh hmix))) i)).height d)
      (fun i => directCutOrderedMap A B hh hmix i) := by
  let D := fun i : Fin (sideCount A B-1+1) =>
    heightTrim (certificate A B hh (order A B
      (prev (sourceIndexEquiv A B (fixedCutIndex A B hh hmix))) i)).domain
      (certificate A B hh (order A B
        (prev (sourceIndexEquiv A B (fixedCutIndex A B hh hmix))) i)).height d
  let root := localB A B hh d
    (familySource A B (fixedCutIndex A B hh hmix) 0)
  let C : Plane ≃ᵃⁱ[ℝ] Plane := AffineIsometryEquiv.constVAdd ℝ Plane root
  by_contra hbad
  have hdim : ∀ i : Fin (sideCount A B-1+1),
      Module.finrank ℝ (FaceSpace A B h (order A B
        (prev (sourceIndexEquiv A B (fixedCutIndex A B hh hmix))) i)) =
        Module.finrank ℝ Plane := fun i =>
    (faceSpace_finrank A B h _).trans (by simp [Plane])
  have hw := overlap_of_not_safe hdim (directCutOrderedMap A B hh hmix) hbad
  have hAlign : ∀ i, ∀ x, C (cutOrderedMap A B hh hmix d i x) =
      directCutOrderedMap A B hh hmix i x := by
    intro i x
    rw [directCutOrderedMap_eq_cutOrderedMap_add_root A B hh hmix d]
    simp [C, root]
    abel
  have hwOld := overlap_under_common_alignment C hAlign hw
  exact not_safe_of_overlap hdim (cutOrderedMap A B hh hmix d) hwOld
    (cutOrdered_safe A B hh hmix hd0 hd1)

end Raw
end
end PhysicalMixedTurnSource
