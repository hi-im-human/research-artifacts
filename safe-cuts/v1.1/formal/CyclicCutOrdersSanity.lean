import CyclicCutOrders

/-! Actual clockwise raw data, followed by genuinely constructed cycles,
OriginalEdges and all-cut families. UNCOMPILED until Forge's direct check. -/
open MergedNormalPrismatoid PolygonSupportCompleteness CommonSupportMerge
open OriginalFacetCertificates NormalFanSplice MaximalSupportCells CyclicCutOrders
namespace CyclicCutOrdersSanity
noncomputable section
open scoped Classical

def triangleVertices : Fin 3 → Plane :=
  ![WithLp.toLp 2 ![0,0],WithLp.toLp 2 ![0,1],WithLp.toLp 2 ![1,0]]

def triangle : ReducedConvexPolygon 3 where
  vertex := triangleVertices
  three_le := by norm_num
  edge_ne := by
    intro i
    fin_cases i <;> norm_num [triangleVertices,next]
  supports := by
    intro i j
    fin_cases i <;> fin_cases j
    all_goals norm_num [triangleVertices,next,outwardNormal,edgeVector,rotateCW,
      inner,Fin.sum_univ_two]
  support_eq_vertices := by
    intro i j hz
    fin_cases i <;> fin_cases j
    all_goals try norm_num [triangleVertices,next,outwardNormal,edgeVector,rotateCW,
      inner,Fin.sum_univ_two] at hz
    all_goals norm_num [triangleVertices,next]

def squareVertices : Fin 4 → Plane :=
  ![WithLp.toLp 2 ![-2,-2],WithLp.toLp 2 ![-2,2],
    WithLp.toLp 2 ![2,2],WithLp.toLp 2 ![2,-2]]

def square : ReducedConvexPolygon 4 where
  vertex := squareVertices
  three_le := by norm_num
  edge_ne := by
    intro i
    fin_cases i <;> norm_num [squareVertices,next]
  supports := by
    intro i j
    fin_cases i <;> fin_cases j
    all_goals norm_num [squareVertices,next,outwardNormal,edgeVector,rotateCW,
      inner,Fin.sum_univ_two]
  support_eq_vertices := by
    intro i j hz
    fin_cases i <;> fin_cases j
    all_goals try norm_num [squareVertices,next,outwardNormal,edgeVector,rotateCW,
      inner,Fin.sum_univ_two] at hz
    all_goals norm_num [squareVertices,next]

def actualInsertedCycle := cycle triangle square
def actualSharedCycle := cycle triangle triangle

def actualInsertedEdge := cyclicEdge triangle square (h := 2) (by norm_num) 0
def actualSharedEdge := cyclicEdge triangle triangle (h := 2) (by norm_num) 0

def actualHinges := hinge triangle square (h := 2) (by norm_num)
def actualCuts := cut triangle square (h := 2) (by norm_num)

theorem actualAdjacency (i j : Fin (sideCount triangle square)) :
    MaterialAdjacent triangle square (h := 2) (by norm_num)
      (cycle triangle square i) (cycle triangle square j) ↔
    j=finRotate _ i ∨ i=finRotate _ j :=
  original_cycle_adjacency triangle square (by norm_num) i j

theorem actualLastFirst :
    MaterialAdjacent triangle square (h := 2) (by norm_num)
      (cycle triangle square ((finRotate _).symm 0))
      (cycle triangle square 0) := by
  apply (actualAdjacency _ _).mpr
  exact Or.inl ((finRotate _).apply_symm_apply 0).symm

#check original_cycle_cut_package triangle square (h := 2) (by norm_num)
#check original_cycle_cut_package triangle triangle (h := 2) (by norm_num)
#check actualHinges
#check actualCuts
end
end CyclicCutOrdersSanity
#print axioms CyclicCutOrdersSanity.triangle
#print axioms CyclicCutOrdersSanity.square
#print axioms CyclicCutOrdersSanity.actualInsertedEdge
#print axioms CyclicCutOrdersSanity.actualSharedEdge
#print axioms CyclicCutOrdersSanity.actualAdjacency
#print axioms CyclicCutOrdersSanity.actualLastFirst
