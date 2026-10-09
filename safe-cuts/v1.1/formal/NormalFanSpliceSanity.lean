import NormalFanSplice

/-! Actual raw-polygon sanity fixtures for the compiled partial splice.
The triangle/square pair contains B-only rays; triangle/triangle has shared
directions. These instantiate the constructed dependent-gap equivalence, not a
proposed display value or a conditional alias. -/
open MergedNormalPrismatoid PolygonSupportCompleteness CommonSupportMerge
open OriginalFacetCertificates NormalFanSplice
namespace NormalFanSpliceSanity
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
    all_goals try
      norm_num [triangleVertices,next,outwardNormal,edgeVector,rotateCW,
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
    all_goals try
      norm_num [squareVertices,next,outwardNormal,edgeVector,rotateCW,
        inner,Fin.sum_univ_two] at hz
    all_goals norm_num [squareVertices,next]

def insertedSide : Side triangle square :=
  ⟨unitRay (outwardNormal square.vertex 1),
    (mem_mergedRays triangle square _).mpr ⟨Sum.inr 1,rfl⟩⟩

theorem square_one_is_triangle_only_insertion :
    ¬ EdgeRay triangle (outwardNormal square.vertex 1) := by
  rintro ⟨k,c,hc,he⟩
  fin_cases k
  · have hx := congrArg (fun x : Plane => x.ofLp 0) he
    norm_num [triangle,square,triangleVertices,squareVertices,next,
      outwardNormal,edgeVector,rotateCW] at hx
    nlinarith
  · have hx := congrArg (fun x : Plane => x.ofLp 0) he
    norm_num [triangle,square,triangleVertices,squareVertices,next,
      outwardNormal,edgeVector,rotateCW] at hx
    nlinarith
  ·
    have hx := congrArg (fun x : Plane => x.ofLp 0) he
    have hy := congrArg (fun x : Plane => x.ofLp 1) he
    norm_num [triangle,square,triangleVertices,squareVertices,next,
      outwardNormal,edgeVector,rotateCW] at hx hy
    nlinarith

theorem actual_inserted_ray_covered :
    ∃ g : Gap triangle square, gapSide triangle square g = insertedSide :=
  gapSide_surjective triangle square insertedSide

def actualInsertedEnumeration := orderedSideEnumeration triangle square
def actualSharedEnumeration := orderedSideEnumeration triangle triangle

end
end NormalFanSpliceSanity

#print axioms NormalFanSpliceSanity.triangle
#print axioms NormalFanSpliceSanity.square
#print axioms NormalFanSpliceSanity.square_one_is_triangle_only_insertion
#print axioms NormalFanSpliceSanity.actual_inserted_ray_covered
#check NormalFanSpliceSanity.actualInsertedEnumeration
#check NormalFanSpliceSanity.actualSharedEnumeration
