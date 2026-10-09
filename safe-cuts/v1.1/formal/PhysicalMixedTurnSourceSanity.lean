import PhysicalMixedTurnSourceSanityFixtures

/-!
Exact scalar hypothesis guards for the physical source bridge.  These are not
physical counterexamples and do not substitute for source-level applications.
-/

open scoped BigOperators
open PhysicalMixedTurnSource
open MergedNormalPrismatoid CyclicCutOrdersSanity
open TrimmedFacetWitnesses CyclicCutOrders
open OriginalFacetCertificates PolygonSupportCompleteness CommonSupportMerge
open PolygonSupportCompleteness.ReducedConvexPolygon PolyhedralInputBridge
open TrimmedFacetWitnesses CyclicCutOrders NormalFanSplice MaximalSupportCells

namespace PhysicalMixedTurnSourceSanity
noncomputable section
set_option maxHeartbeats 4000000

/-- The requested nonphysical scalar guard `q = (1,1,-1/4)`. -/
def guardQ : Fin 3 → ℝ := ![1, 1, -(1/4 : ℝ)]

example : (∃ i, guardQ i < 0) ∧ (∃ i, 0 < guardQ i) := by
  refine ⟨⟨2, by norm_num [guardQ]⟩, ⟨0, by norm_num [guardQ]⟩⟩

example : (∑ i, guardQ i) = (7/4 : ℝ) := by
  norm_num [guardQ, Fin.sum_univ_succ]

/-- Mixed unshifted signs do not imply the accepted shifted condition. -/
example : ¬ ShiftedMixed guardQ := by
  intro h
  rcases h.2 with ⟨i, hi⟩
  fin_cases i <;> norm_num [guardQ, ShiftedMixed, Fin.sum_univ_succ] at hi

example :
    (∑ i, guardQ i) =
      MixedTurnSafeCut.positiveBudget guardQ - MixedTurnSafeCut.negativeBudget guardQ :=
  sum_eq_positiveBudget_sub_negativeBudget guardQ

def triangleSquareInsertedSide : Side triangle square :=
  ⟨unitRay (outwardNormal square.vertex 1),
    (mem_mergedRays triangle square _).mpr ⟨Sum.inr 1, rfl⟩⟩

lemma square_one_is_triangle_only_insertion :
    ¬ EdgeRay triangle (outwardNormal square.vertex 1) := by
  rintro ⟨k, c, hc, he⟩
  fin_cases k
  · have hx := congrArg (fun x : MergedNormalPrismatoid.Plane => x.ofLp 0) he
    norm_num [triangle, square, triangleVertices, squareVertices, next,
      outwardNormal, edgeVector, rotateCW] at hx
    nlinarith
  · have hx := congrArg (fun x : MergedNormalPrismatoid.Plane => x.ofLp 0) he
    norm_num [triangle, square, triangleVertices, squareVertices, next,
      outwardNormal, edgeVector, rotateCW] at hx
    nlinarith
  · have hx := congrArg (fun x : MergedNormalPrismatoid.Plane => x.ofLp 0) he
    have hy := congrArg (fun x : MergedNormalPrismatoid.Plane => x.ofLp 1) he
    norm_num [triangle, square, triangleVertices, squareVertices, next,
      outwardNormal, edgeVector, rotateCW] at hx hy
    nlinarith

/-- The concrete triangle/square side whose normal is square-only.  This is an
actual source-facet index, not a symbolic triangular panel. -/
noncomputable def collapsedUpperFacet :
    SourceIndex triangle square :=
  (cycle triangle square).symm
    triangleSquareInsertedSide

lemma collapsedUpperFacet_cycle :
    cycle triangle square
        collapsedUpperFacet = triangleSquareInsertedSide :=
  (cycle triangle square).apply_symm_apply _

/-- On the identified physical facet, the original upper-rim run collapses.
The proof uses the two actual neighboring support cells at the square-only ray:
both triangle support vertices lie in the ray's singleton support face. -/
lemma collapsedUpperFacet_upperPlanarRun :
    upperPlanarRun triangle square
      collapsedUpperFacet = 0 := by
  let A := triangle
  let B := square
  let i : SourceIndex A B := collapsedUpperFacet
  let u : Side A B := triangleSquareInsertedSide
  have hcycle : cycle A B i = u := collapsedUpperFacet_cycle
  let g₀ := entryGap A B i
  let g₁ := entryGap A B (next i)
  have hm₀ : Maximizes A u.val g₀.1 := by
    have hs := (side_supports_pair_iff A B g₀ u).2
      (Or.inr ((entryGap_right A B i).trans hcycle).symm)
    exact hs.1
  have hm₁ : Maximizes A u.val g₁.1 := by
    have hleft : gapSide A B g₁ = u := by
      calc
        gapSide A B g₁ = cycle A B (prev (next i)) := by
          simpa only [g₁] using entryGap_left A B (next i)
        _ = cycle A B i := by rw [prev_next]
        _ = u := hcycle
    have hs := (side_supports_pair_iff A B g₁ u).2 (Or.inl hleft.symm)
    exact hs.1
  have hsingle : supportFace A u.val = {A.vertex g₀.1} := by
    obtain ⟨k, hk⟩ := singleton_of_not_edgeRay A u.val (side_ne_zero A B u)
      (by
        dsimp [u, triangleSquareInsertedSide]
        intro hunit
        let w := outwardNormal square.vertex 1
        have hw : 0 < ‖w‖ := norm_pos_iff.mpr (square.outwardNormal_ne_zero 1)
        rcases hunit with ⟨k, c, hc, he⟩
        apply square_one_is_triangle_only_insertion
        refine ⟨k, ‖w‖ * c, mul_pos hw hc, ?_⟩
        calc
          w = ‖w‖ • unitRay w := by simp [unitRay, hw.ne']
          _ = (‖w‖ * c) • outwardNormal triangle.vertex k := by
            rw [he, smul_smul]
        )
    have hmem₀ : A.vertex g₀.1 ∈ supportFace A u.val :=
      ⟨A.vertex_mem_body g₀.1, hm₀⟩
    have : A.vertex g₀.1 = A.vertex k := by simpa [hk] using hmem₀
    simpa [this] using hk
  have hmem₁ : A.vertex g₁.1 ∈ supportFace A u.val :=
    ⟨A.vertex_mem_body g₁.1, hm₁⟩
  have heq : A.vertex g₁.1 = A.vertex g₀.1 := by
    rw [hsingle] at hmem₁
    simpa using hmem₁
  change A.vertex (entryGap A B (next i)).1 - A.vertex (entryGap A B i).1 = 0
  simpa [g₀, g₁] using sub_eq_zero.mpr heq

lemma collapsedUpperFacet_upperRunCoeff :
    upperRunCoeff triangle square
      (h := 2) (by norm_num) collapsedUpperFacet = 0 := by
  let A := triangle
  let B := square
  let hh : (0 : ℝ) < 2 := by norm_num
  let i : SourceIndex A B := collapsedUpperFacet
  have hmap := chartLinear_faceUpperRun A B hh i
  rw [collapsedUpperFacet_upperPlanarRun] at hmap
  have hrun : faceUpperRun A B hh i = 0 := by
    apply (certificate A B hh (cycle A B i)).chart.linearIsometry.injective
    simpa using hmap
  change inner ℝ (faceUnit A B hh i) (faceUpperRun A B hh i) = 0
  rw [hrun]
  simp

/-- Despite the collapsed original upper rim, both retained boundary lengths of
this same actual facet are strictly positive at every positive trim. -/
theorem collapsedUpperFacet_retained_lengths_pos {d : ℝ}
    (hd0 : 0 < d) (hd1 : d < (1 : ℝ) / 2) :
    0 < retainedLowerRunCoeff triangle
        square (h := 2) (by norm_num) d collapsedUpperFacet ∧
      0 < retainedUpperRunCoeff triangle
        square (h := 2) (by norm_num) d collapsedUpperFacet :=
  ⟨retainedLowerRunCoeff_pos _ _ (by norm_num) hd0 hd1 _,
    retainedUpperRunCoeff_pos _ _ (by norm_num) hd0 hd1 _⟩

lemma two_pos : (0 : ℝ) < 2 := by norm_num

noncomputable def collapsedUpperCutIndex : Fin (MechanismN triangle square + 1) :=
  (sourceIndexEquiv triangle square).symm collapsedUpperFacet

lemma collapsedUpperCutIndex_source :
    familySource triangle square collapsedUpperCutIndex 0 = collapsedUpperFacet := by
  rw [familySource_zero]
  exact (sourceIndexEquiv triangle square).apply_symm_apply _

lemma collapsedUpperFacet_side_eq :
    cycle triangle square collapsedUpperFacet =
      cycle triangle square (familySource triangle square collapsedUpperCutIndex
        (0 : Fin (MechanismN triangle square + 1)).val) := by
  exact congrArg (fun i : SourceIndex triangle square => cycle triangle square i)
    (by simpa using collapsedUpperCutIndex_source.symm)

/-- Specialized kernel check for the named triangular source facet: the exact
trimmed material image under the transported developed source map is the
corresponding physical developed-family face.  The statement itself names
`collapsedUpperFacet`; the dependent transport is exposed rather than hidden
behind a generic alias and a separate equality. -/
theorem collapsedUpperFacet_developed_source_image
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ) / 2) :
    transportFaceMap triangle square collapsedUpperFacet_side_eq
        (developedMap triangle square two_pos d collapsedUpperCutIndex
          (0 : Fin (MechanismN triangle square + 1)).val) ''
        heightTrim
          (certificate triangle square two_pos
            (cycle triangle square collapsedUpperFacet)).domain
          (certificate triangle square two_pos
            (cycle triangle square collapsedUpperFacet)).height d =
      (physicalDevelopedFamily triangle square two_pos hd0 hd1).face
        collapsedUpperCutIndex 0 := by
  rw [transportFaceMap_image_heightTrim triangle square two_pos]
  exact developedMap_heightTrim_image triangle square two_pos hd0 hd1
    collapsedUpperCutIndex (0 : Fin (MechanismN triangle square + 1))

/-- Actual triangle/square source: every positive trim of every physical facet
is exactly its canonical finite hull, including inserted-normal facets. -/
example (i : SourceIndex triangle square) :
    heightTrim
      (certificate triangle square (h := 2) (by norm_num) (cycle triangle square i)).domain
      (certificate triangle square (h := 2) (by norm_num) (cycle triangle square i)).height (1/4) =
      retainedFaceHull triangle square (h := 2) (by norm_num) (1/4) i :=
  heightTrim_eq_retainedFaceHull triangle square (by norm_num)
    (by norm_num) (by norm_num) i

/-- Actual aligned triangle-prism source: exact retained-facet hull equality. -/
example (i : SourceIndex triangle triangle) :
    heightTrim
      (certificate triangle triangle (h := 2) (by norm_num) (cycle triangle triangle i)).domain
      (certificate triangle triangle (h := 2) (by norm_num) (cycle triangle triangle i)).height (1/4) =
      retainedFaceHull triangle triangle (h := 2) (by norm_num) (1/4) i :=
  heightTrim_eq_retainedFaceHull triangle triangle (by norm_num)
    (by norm_num) (by norm_num) i

/-- Actual-source holonomy is the intrinsic middle-section turning defect. -/
example :
    (∑ k, mechanismQ triangle square (h := 2) (by norm_num) k) =
      intrinsicDelta triangle square (h := 2) (hh := by norm_num) :=
  mechanismQ_sum_eq_intrinsicDelta triangle square (by norm_num)

/-- Wraparound and the `k ↦ k-1` source-cut convention agree at the first
physical face. -/
example (k : SourceIndex triangle square) :
    order triangle square (prev k) 0 = cycle triangle square k :=
  by
    rw [order_prev_apply]
    congr 1
    apply Fin.ext
    change (k.val + 0) % sideCount triangle square = k.val
    exact Nat.mod_eq_of_lt k.isLt

end
end PhysicalMixedTurnSourceSanity
