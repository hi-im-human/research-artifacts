import CommonSupportMerge

/-! Actual raw data and actual section statements, not a conditional type alias.
System draft, uncompiled. Uses the unchanged clockwise convention. -/
open Set MergedNormalPrismatoid PolygonSupportCompleteness CommonSupportMerge
namespace CommonSupportMergeSanity
noncomputable section

def vertices : Fin 3 → Plane :=
  ![WithLp.toLp 2 ![0,0], WithLp.toLp 2 ![0,1], WithLp.toLp 2 ![1,0]]

def triangle : ReducedConvexPolygon 3 where
  vertex := vertices
  three_le := by norm_num
  edge_ne := by
    intro i
    fin_cases i <;> norm_num [vertices,next]
  supports := by
    intro i j
    fin_cases i <;> fin_cases j
    all_goals norm_num [vertices,next,outwardNormal,edgeVector,rotateCW,inner,Fin.sum_univ_two]
  support_eq_vertices := by
    intro i j hz
    fin_cases i <;> fin_cases j
    all_goals try norm_num [vertices,next,outwardNormal,edgeVector,rotateCW,inner,Fin.sum_univ_two] at hz
    all_goals norm_num [vertices,next]

def p : Plane := WithLp.toLp 2 ![(1:ℝ)/4,(1:ℝ)/4]
def q : Plane := WithLp.toLp 2 ![(2:ℝ),(2:ℝ)]

lemma p_inside : p ∈ triangle.body := by
  apply PolygonSupportCompleteness.ReducedConvexPolygon.mem_body_of_edgeRows
  intro i
  fin_cases i <;> norm_num [ReducedConvexPolygon.edgeRow_apply,triangle,vertices,p,
    next,outwardNormal,edgeVector,rotateCW,inner,Fin.sum_univ_two]

lemma q_outside : q ∉ triangle.body := by
  intro hq
  have h := triangle.body_edge_nonpos (1 : Fin 3) hq
  norm_num [ReducedConvexPolygon.edgeRow_apply,triangle,vertices,q,
    next,outwardNormal,edgeVector,rotateCW,inner,Fin.sum_univ_two] at h

/-- Positive instance of the new merged-row equivalence. -/
theorem p_in_merged_section : p ∈ mergedFeasible triangle triangle ((1:ℝ)/2) := by
  rw [← section_eq_merged_halfspaces triangle triangle (by norm_num : (1:ℝ)/2 ∈ Icc 0 1)]
  refine ⟨(p,p),⟨p_inside,p_inside⟩,?_⟩
  change (1-(1:ℝ)/2) • p + ((1:ℝ)/2) • p = p
  module

/-- A genuinely exterior point cannot pass the newly combined row description. -/
theorem q_not_in_merged_section : q ∉ mergedFeasible triangle triangle ((1:ℝ)/2) := by
  rw [← section_eq_merged_halfspaces triangle triangle (by norm_num : (1:ℝ)/2 ∈ Icc 0 1)]
  rintro ⟨⟨b,a⟩,⟨hb,ha⟩,he⟩
  have hm := triangle.body_convex hb ha
    (by norm_num : 0 ≤ 1-(1:ℝ)/2) (by norm_num : 0 ≤ (1:ℝ)/2) (by norm_num)
  change mixLinear ((1:ℝ)/2) (b,a) ∈ triangle.body at hm
  rw [he] at hm
  exact q_outside hm

#check physicalPrismatoid_eq_merged_halfspaces triangle triangle (by norm_num : (0:ℝ) < 2)
end
end CommonSupportMergeSanity
#print axioms CommonSupportMergeSanity.triangle
#print axioms CommonSupportMergeSanity.p_in_merged_section
#print axioms CommonSupportMergeSanity.q_not_in_merged_section
