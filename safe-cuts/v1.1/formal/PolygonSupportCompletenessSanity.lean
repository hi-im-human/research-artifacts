import PolygonSupportCompleteness
import EuclideanPrismatoidCoordinates

/-! UNCOMPILED concrete raw-input witness. Unlike a specialized conditional
type, this actually inhabits the raw polygon structure used by the new proof.
The clockwise ordering matches the original source's actual sign convention. -/
open MergedNormalPrismatoid PolygonSupportCompleteness
namespace PolygonSupportCompletenessSanity
noncomputable section

def vertices : Fin 3 → Plane :=
  ![WithLp.toLp 2 ![0,0], WithLp.toLp 2 ![0,1], WithLp.toLp 2 ![1,0]]

def triangle : MergedNormalPrismatoid.ReducedConvexPolygon 3 where
  vertex := vertices
  three_le := by norm_num
  edge_ne := by
    intro i
    fin_cases i <;> norm_num [vertices, next]
  supports := by
    intro i j
    fin_cases i <;> fin_cases j
    all_goals
      norm_num [vertices, next, outwardNormal, edgeVector, rotateCW, inner, Fin.sum_univ_two]
  support_eq_vertices := by
    intro i j hz
    fin_cases i <;> fin_cases j
    all_goals try
      norm_num [vertices, next, outwardNormal, edgeVector, rotateCW, inner, Fin.sum_univ_two] at hz
    all_goals
      norm_num [vertices, next]

example : (WithLp.toLp 2 ![(1:ℝ)/4, (1:ℝ)/4]) ∈ triangle.body := by
  apply PolygonSupportCompleteness.ReducedConvexPolygon.mem_body_of_edgeRows triangle
  intro i
  rw [MergedNormalPrismatoid.ReducedConvexPolygon.edgeRow_apply]
  fin_cases i <;>
    norm_num [triangle, vertices, next, outwardNormal, edgeVector, rotateCW, inner, Fin.sum_univ_two]

example : (WithLp.toLp 2 ![(2:ℝ),(2:ℝ)]) ∉ triangle.body := by
  intro h
  have hc := triangle.body_edge_nonpos (1 : Fin 3) h
  rw [MergedNormalPrismatoid.ReducedConvexPolygon.edgeRow_apply] at hc
  norm_num [triangle, vertices, next, outwardNormal, edgeVector, rotateCW, inner, Fin.sum_univ_two] at hc

end
end PolygonSupportCompletenessSanity
#print axioms PolygonSupportCompletenessSanity.triangle
