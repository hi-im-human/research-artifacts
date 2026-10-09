import CyclicCutOrders
import ConvexSectionNesting
import SingleCutRecovery

/-!
# Apply an external ordinary nested-band theorem to the checked recovery layer

The borrowed theorem is an ordinary explicit argument.  Its output contains
only rigid face placements, all-pairs safety, and equality on the constructed
retained hinges.  DevelopmentOn and gluing for every possible OriginalEdge are
derived here before the checked SingleCutRecovery endpoint is invoked.
-/

open Set
open scoped Pointwise Classical
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CommonSupportMerge OriginalFacetCertificates MaximalSupportCells CyclicCutOrders
open EuclideanPrismatoidCoordinates PolyhedralInputBridge
open TrimmedFacetWitnesses BandGeometryAssembly FiniteWitnessClosure SingleCutRecovery

namespace NestedBandExternalApplication
noncomputable section
set_option maxHeartbeats 1500000

section Sections
variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)

/-- The independently defined section is exactly the standard Minkowski sum. -/
theorem sectionSet_eq_minkowskiSection (t : ℝ) :
    sectionSet A B t =
      ConvexSectionNesting.minkowskiSection A.body B.body t := by
  ext x
  constructor
  · rintro ⟨⟨b, a⟩, ⟨hb, ha⟩, rfl⟩
    exact ⟨(1-t) • b, ⟨b, hb, rfl⟩, t • a, ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨xb, ⟨b, hb, rfl⟩, xa, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨⟨b, a⟩, ⟨hb, ha⟩, rfl⟩

/-- Every inward trim is strictly nested, derived from the raw body nesting. -/
theorem trimmed_sections_strict_nesting
    (hNest : A.body ⊆ interior B.body) {d : ℝ}
    (hd0 : 0 < d) (hd1 : d < (1 : ℝ)/2) :
    sectionSet A B (1-d) ⊆ interior (sectionSet A B d) := by
  rw [sectionSet_eq_minkowskiSection A B,
    sectionSet_eq_minkowskiSection A B]
  exact ConvexSectionNesting.truncated_section_strict_nesting
    B.body_convex hNest hd0 hd1

end Sections

section ExternalState
variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)
  (Q : Type*) [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]

/-- The layout fields at one already chosen seam.  Separating this dependent
payload keeps the public flat-state record small enough for Lean to elaborate
without changing its mathematical contract. -/
structure TrimmedFlatLayout (d : ℝ) (e : Fin (sideCount A B)) where
  T : (i : Fin (sideCount A B-1+1)) →
    FaceSpace A B h (order A B e i) →ᵃⁱ[ℝ] Q
  safe : Safe
    (fun i => heightTrim (certificate A B hh (order A B e i)).domain
      (certificate A B hh (order A B e i)).height d)
    (fun i => T i)
  hinge_glued : ∀ (j : Fin (sideCount A B-1)) (t : ℝ), t ∈ Icc d (1-d) →
    T j.castSucc (AffineMap.lineMap (hinge A B hh e j).aL
      (hinge A B hh e j).bL t) =
    T j.succ (AffineMap.lineMap (hinge A B hh e j).aR
      (hinge A B hh e j).bR t)

/-- Minimal final flat state supplied by the external ordinary nested-band
theorem: one seam and only the rigid/safe/constructed-hinge layout at it. -/
structure TrimmedFlatState (d : ℝ) where
  seam : Fin (sideCount A B)
  layout : TrimmedFlatLayout A B hh Q d seam

/-- Contract of the borrowed theorem.  Strict section nesting is supplied to
it; DevelopmentOn and arbitrary-edge gluing are deliberately absent. -/
def ExternalNestedBandTheorem : Prop :=
  ∀ (d : ℝ), 0 < d → d < (1 : ℝ)/2 →
    sectionSet A B (1-d) ⊆ interior (sectionSet A B d) →
    Nonempty (TrimmedFlatState A B hh Q d)

variable {A B hh Q}

/-- Retained constructed-hinge equality plus all-pairs safety gives the exact
DevelopmentOn predicate required by recovery. -/
theorem developmentOn_of_flat_state {d : ℝ} (hd0 : 0 < d)
    (hd1 : d < (1 : ℝ)/2) (s : TrimmedFlatState A B hh Q d) :
    DevelopmentOn
      (fun i => (certificate A B hh (order A B s.seam i)).chart.toAffineMap)
      (fun i => heightTrim (certificate A B hh (order A B s.seam i)).domain
        (certificate A B hh (order A B s.seam i)).height d)
      (fun i => s.layout.T i) := by
  constructor
  · intro j x hx y hy hxy
    let ed := hinge A B hh s.seam j
    have hp : (certificate A B hh (order A B s.seam j.castSucc)).chart x ∈
        ((certificate A B hh (order A B s.seam j.castSucc)).chart ''
          heightTrim (certificate A B hh (order A B s.seam j.castSucc)).domain
            (certificate A B hh (order A B s.seam j.castSucc)).height d) ∩
        ((certificate A B hh (order A B s.seam j.succ)).chart ''
          heightTrim (certificate A B hh (order A B s.seam j.succ)).domain
            (certificate A B hh (order A B s.seam j.succ)).height d) :=
      ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy.symm⟩⟩
    rw [(hinge A B hh s.seam j).common_trimmed_edge
      (faceSpace_finrank A B h _ ) hd0 hd1] at hp
    obtain ⟨t, ht, htp⟩ := hp
    have hxline : AffineMap.lineMap ed.aL ed.bL t = x := by
      apply (certificate A B hh (order A B s.seam j.castSucc)).chart.injective
      exact ((certificate A B hh
        (order A B s.seam j.castSucc)).chart.toAffineMap.apply_lineMap _ _ _).trans htp
    have hyline : AffineMap.lineMap ed.aR ed.bR t = y := by
      apply (certificate A B hh (order A B s.seam j.succ)).chart.injective
      calc
        (certificate A B hh (order A B s.seam j.succ)).chart
            (AffineMap.lineMap ed.aR ed.bR t) =
            AffineMap.lineMap
              ((certificate A B hh (order A B s.seam j.succ)).chart ed.aR)
              ((certificate A B hh (order A B s.seam j.succ)).chart ed.bR) t :=
          (certificate A B hh
            (order A B s.seam j.succ)).chart.toAffineMap.apply_lineMap _ _ _
        _ = AffineMap.lineMap
              ((certificate A B hh (order A B s.seam j.castSucc)).chart ed.aL)
              ((certificate A B hh (order A B s.seam j.castSucc)).chart ed.bL) t := by
          rw [← ed.match_a, ← ed.match_b]
        _ = (certificate A B hh (order A B s.seam j.castSucc)).chart x := htp
        _ = (certificate A B hh (order A B s.seam j.succ)).chart y := hxy
    simpa only [ed, hxline, hyline] using s.layout.hinge_glued j t ht
  · intro j
    have hne : j.castSucc ≠ j.succ := by
      intro he
      have hv := congrArg Fin.val he
      change j.val = j.val+1 at hv
      omega
    exact s.layout.safe j.castSucc j.succ hne

/-- A flat state glues every uncut OriginalEdge, not merely the particular
constructed hinge records in the external output. -/
theorem allUncutGlued_of_flat_state {d : ℝ} (hd0 : 0 < d)
    (hd1 : d < (1 : ℝ)/2) (s : TrimmedFlatState A B hh Q d) :
    AllUncutGlued
      (fun i => certificate A B hh (order A B s.seam i)) d
      (fun i => s.layout.T i) := by
  have hDev := developmentOn_of_flat_state hd0 hd1 s
  intro i j hNot ed t ht
  let u := order A B s.seam i
  let v := order A B s.seam j
  have hAdj : MaterialAdjacent A B hh u v :=
    (materialAdjacency_iff_gapEndpoints A B hh u v).mpr
      (arbitraryOriginalEdge_covered A B hh u v ed)
  have hNotPair : ¬ SamePair u v
      (order A B s.seam (Fin.last _)) (order A B s.seam 0) := by
    intro hp
    apply hNot
    rcases hp with ⟨hui, hvj⟩ | ⟨huj, hvi⟩
    · exact Or.inl ⟨(order A B s.seam).injective hui,
        (order A B s.seam).injective hvj⟩
    · exact Or.inr ⟨(order A B s.seam).injective huj,
        (order A B s.seam).injective hvi⟩
  obtain ⟨k, hk⟩ :=
    (uncut_iff_chain A B hh s.seam u v).mp ⟨hAdj, hNotPair⟩
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hx : AffineMap.lineMap ed.aL ed.bL t ∈
      heightTrim (certificate A B hh u).domain
        (certificate A B hh u).height d := by
    constructor
    · exact lineMap_mem_face (certificate A B hh u).domain_convex
        ed.aL_mem ed.bL_mem ht01
    · simpa only [Set.mem_ofPred_eq, mem_Icc,
        height_lineMap (certificate A B hh u).height ed.a_height ed.b_height t] using ht
  have hy : AffineMap.lineMap ed.aR ed.bR t ∈
      heightTrim (certificate A B hh v).domain
        (certificate A B hh v).height d := by
    constructor
    · exact lineMap_mem_face (certificate A B hh v).domain_convex
        ed.aR_mem ed.bR_mem ht01
    · simpa only [Set.mem_ofPred_eq, mem_Icc,
        height_lineMap (certificate A B hh v).height ed.right_height_a ed.right_height_b t]
        using ht
  have hxy : (certificate A B hh u).chart
        (AffineMap.lineMap ed.aL ed.bL t) =
      (certificate A B hh v).chart
        (AffineMap.lineMap ed.aR ed.bR t) := by
    calc
      (certificate A B hh u).chart (AffineMap.lineMap ed.aL ed.bL t) =
          AffineMap.lineMap ((certificate A B hh u).chart ed.aL)
            ((certificate A B hh u).chart ed.bL) t :=
        (certificate A B hh u).chart.toAffineMap.apply_lineMap _ _ _
      _ = AffineMap.lineMap ((certificate A B hh v).chart ed.aR)
            ((certificate A B hh v).chart ed.bR) t := by
        rw [ed.match_a, ed.match_b]
      _ = (certificate A B hh v).chart (AffineMap.lineMap ed.aR ed.bR t) :=
        ((certificate A B hh v).chart.toAffineMap.apply_lineMap _ _ _).symm
  rcases hk with ⟨huk, hvk⟩ | ⟨hvk, huk⟩
  · have hik : i = k.castSucc := (order A B s.seam).injective huk
    have hjk : j = k.succ := (order A B s.seam).injective hvk
    subst i
    subst j
    exact hDev.1 k _ hx _ hy hxy
  · have hik : i = k.succ := (order A B s.seam).injective hvk
    have hjk : j = k.castSucc := (order A B s.seam).injective huk
    subst i
    subst j
    exact (hDev.1 k _ hy _ hx hxy.symm).symm

end ExternalState

section Recovery
variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)
  (Q : Type*) [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
  [FiniteDimensional ℝ Q]

/-- Conditional raw-polygon face-table recovery.  The sole borrowed
mathematical premise is `hExternal`; all recovery inputs stronger than its
ordinary flat-state output are derived in this module. -/
theorem recover_full_face_table_from_external_nested_band
    (hNest : A.body ⊆ interior B.body)
    (hExternal : ExternalNestedBandTheorem A B hh Q)
    (hdQ : Module.finrank ℝ Q = 2) :
    ∃ e : Fin (sideCount A B),
      ∃ U : (i : Fin (sideCount A B-1+1)) →
        FaceSpace A B h (order A B e i) →ᵃⁱ[ℝ] Q,
      DevelopmentOn
          (fun i => (certificate A B hh (order A B e i)).chart.toAffineMap)
          (fun i => (certificate A B hh (order A B e i)).domain)
          (fun i => U i) ∧
      Safe (fun i => (certificate A B hh (order A B e i)).domain)
          (fun i => U i) ∧
      AllUncutGlued (fun i => certificate A B hh (order A B e i)) 0
          (fun i => U i) ∧
      (∀ i j, ¬ CutPair i j →
        ∀ _ed : OriginalEdge
          (certificate A B hh (order A B e i))
          (certificate A B hh (order A B e j)),
        ∀ x ∈ (certificate A B hh (order A B e i)).domain,
        ∀ y ∈ (certificate A B hh (order A B e j)).domain,
          (certificate A B hh (order A B e i)).chart x =
            (certificate A B hh (order A B e j)).chart y →
          U i x = U j y) ∧
      (((certificate A B hh (order A B e (Fin.last _))).chart ''
          (certificate A B hh (order A B e (Fin.last _))).domain) ∩
        ((certificate A B hh (order A B e 0)).chart ''
          (certificate A B hh (order A B e 0)).domain) =
        AffineMap.lineMap
          ((certificate A B hh (order A B e (Fin.last _))).chart
            (cut A B hh e).aL)
          ((certificate A B hh (order A B e (Fin.last _))).chart
            (cut A B hh e).bL) '' Icc (0 : ℝ) 1) ∧
      (⋃ i, (certificate A B hh (order A B e i)).chart ''
        (certificate A B hh (order A B e i)).domain) =
        lateralBoundary (halfspaces A B h) := by
  apply SingleCutRecovery.exists_safe_glued_table_from_trimmed_unfoldings
    (halfspaces A B h) (certificate A B hh) (rowsEquiv A B)
    (fun _ => rfl)
    (by have hs := three_le_sideCount A B; omega)
    (faceSpace_finrank A B h) hdQ
    (order A B) (hinge A B hh) (cut A B hh)
  intro d hd0 hd1
  have hStrict := trimmed_sections_strict_nesting A B hNest hd0 hd1
  obtain ⟨s⟩ := hExternal d hd0 hd1 hStrict
  exact ⟨s.seam, s.layout.T, developmentOn_of_flat_state hd0 hd1 s,
    s.layout.safe, allUncutGlued_of_flat_state hd0 hd1 s⟩

end Recovery

end
end NestedBandExternalApplication

#print axioms NestedBandExternalApplication.sectionSet_eq_minkowskiSection
#print axioms NestedBandExternalApplication.trimmed_sections_strict_nesting
#check @NestedBandExternalApplication.sectionSet_eq_minkowskiSection
#check @NestedBandExternalApplication.trimmed_sections_strict_nesting
#check @NestedBandExternalApplication.TrimmedFlatState
#check @NestedBandExternalApplication.TrimmedFlatLayout
#check @NestedBandExternalApplication.ExternalNestedBandTheorem
#print NestedBandExternalApplication.TrimmedFlatState
#print NestedBandExternalApplication.TrimmedFlatLayout
#print NestedBandExternalApplication.ExternalNestedBandTheorem
#print axioms NestedBandExternalApplication.developmentOn_of_flat_state
#print axioms NestedBandExternalApplication.allUncutGlued_of_flat_state
#print axioms NestedBandExternalApplication.recover_full_face_table_from_external_nested_band
#check @NestedBandExternalApplication.developmentOn_of_flat_state
#check @NestedBandExternalApplication.allUncutGlued_of_flat_state
#check @NestedBandExternalApplication.recover_full_face_table_from_external_nested_band
