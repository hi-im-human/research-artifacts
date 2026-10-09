import PhysicalMixedTurnSource

/-!
Endpoint transport for proof-selected `OriginalEdge` witnesses.

The generic lemmas characterize the lower and upper physical endpoints of an
`OriginalEdge` by membership in its common material segment and normalized
height.  Physical source endpoints can therefore be identified without
unfolding the dependent construction of `CyclicCutOrders.cyclicEdge`.
-/

open Set
open scoped Classical
open TrimmedFacetWitnesses PolyhedralInputBridge

namespace PolyhedralInputBridge.OriginalEdge

variable {K A : Type*} [Fintype K]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  {H : HalfspaceData (K := K) (A := A)}
  {L R : Type*}
  [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  {CL : FacetCertificate H L} {CR : FacetCertificate H R}

/-- A point of the common material edge at normalized height zero is the
physical image of the selected lower endpoint. -/
theorem chart_a_eq_of_mem_common_of_height_zero
    (e : OriginalEdge CL CR) (hdL : Module.finrank ℝ L = 2)
    (p : A) (hp : p ∈ (CL.chart '' CL.domain) ∩ (CR.chart '' CR.domain))
    (hz : H.height p = 0) :
    CL.chart e.aL = p := by
  rw [e.common_material_edge hdL] at hp
  obtain ⟨t, ht, htp⟩ := hp
  have hheight : H.height
      (AffineMap.lineMap (CL.chart e.aL) (CL.chart e.bL) t) = t :=
    height_lineMap H.height e.a_height e.b_height t
  have ht0 : t = 0 := by
    rw [htp, hz] at hheight
    exact hheight.symm
  rw [ht0] at htp
  simpa using htp

/-- A point of the common material edge at normalized height one is the
physical image of the selected upper endpoint. -/
theorem chart_b_eq_of_mem_common_of_height_one
    (e : OriginalEdge CL CR) (hdL : Module.finrank ℝ L = 2)
    (p : A) (hp : p ∈ (CL.chart '' CL.domain) ∩ (CR.chart '' CR.domain))
    (hz : H.height p = 1) :
    CL.chart e.bL = p := by
  rw [e.common_material_edge hdL] at hp
  obtain ⟨t, ht, htp⟩ := hp
  have hheight : H.height
      (AffineMap.lineMap (CL.chart e.aL) (CL.chart e.bL) t) = t :=
    height_lineMap H.height e.a_height e.b_height t
  have ht1 : t = 1 := by
    rw [htp, hz] at hheight
    exact hheight.symm
  rw [ht1] at htp
  simpa using htp

end PolyhedralInputBridge.OriginalEdge

open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CommonSupportMerge OriginalFacetCertificates NormalFanSplice MaximalSupportCells
open CyclicCutOrders EuclideanPrismatoidCoordinates PolyhedralInputBridge
open PhysicalMixedTurnSource

namespace PhysicalMixedTurnSource
noncomputable section

variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

/-- Every `OriginalEdge` witness with the entry-edge dependent type has the
canonical physical endpoints.  In particular this applies directly to
`entryEdge A B hh i` (and hence to its underlying `cyclicEdge`) without
unfolding how that witness was chosen. -/
theorem entryEdge_endpoints_eq (i : SourceIndex A B)
    (ed : OriginalEdge
      (certificate A B hh (cycle A B (prev i)))
      (certificate A B hh
        (cycle A B (finRotate (sideCount A B) (prev i))))) :
    (certificate A B hh (cycle A B (prev i))).chart ed.aL =
        lowerEndpoint A B hh i ∧
      (certificate A B hh (cycle A B (prev i))).chart ed.bL =
        upperEndpoint A B hh i := by
  have hp0 := canonical_hinge_point_mem_both A B hh i 0 (by norm_num)
  rw [← lowerEndpoint_eq_mixedPoint_zero A B hh i] at hp0
  change lowerEndpoint A B hh i ∈
    ((certificate A B hh (cycle A B (prev i))).chart ''
      (certificate A B hh (cycle A B (prev i))).domain) ∩
    ((certificate A B hh
      (cycle A B (finRotate (sideCount A B) (prev i)))).chart ''
      (certificate A B hh
        (cycle A B (finRotate (sideCount A B) (prev i)))).domain) at hp0
  have hp1 := canonical_hinge_point_mem_both A B hh i 1 (by norm_num)
  rw [← upperEndpoint_eq_mixedPoint_one A B hh i] at hp1
  change upperEndpoint A B hh i ∈
    ((certificate A B hh (cycle A B (prev i))).chart ''
      (certificate A B hh (cycle A B (prev i))).domain) ∩
    ((certificate A B hh
      (cycle A B (finRotate (sideCount A B) (prev i)))).chart ''
      (certificate A B hh
        (cycle A B (finRotate (sideCount A B) (prev i)))).domain) at hp1
  exact ⟨
    ed.chart_a_eq_of_mem_common_of_height_zero
      (faceSpace_finrank A B h (cycle A B (prev i)))
      (lowerEndpoint A B hh i) hp0 (lowerEndpoint_height A B hh i),
    ed.chart_b_eq_of_mem_common_of_height_one
      (faceSpace_finrank A B h (cycle A B (prev i)))
      (upperEndpoint A B hh i) hp1 (upperEndpoint_height A B hh i)⟩

/-- Direct specialization to the proof-selected `cyclicEdge`, kept behind an
annotated `let` so elaboration uses its interface rather than reducing its
choice proof. -/
theorem selectedEntryEdge_endpoints_eq (i : SourceIndex A B) :
    let ed : OriginalEdge
      (certificate A B hh (cycle A B (prev i)))
      (certificate A B hh
        (cycle A B (finRotate (sideCount A B) (prev i)))) :=
      entryEdge A B hh i
    (certificate A B hh (cycle A B (prev i))).chart ed.aL =
        lowerEndpoint A B hh i ∧
      (certificate A B hh (cycle A B (prev i))).chart ed.bL =
        upperEndpoint A B hh i := by
  exact entryEdge_endpoints_eq A B hh i (entryEdge A B hh i)

end
end PhysicalMixedTurnSource
