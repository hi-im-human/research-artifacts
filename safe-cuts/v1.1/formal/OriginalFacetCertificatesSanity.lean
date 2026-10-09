import OriginalFacetCertificates

/-! Uncompiled sanity source: actual data, not a conditional type alias. -/
open Set MergedNormalPrismatoid PolygonSupportCompleteness CommonSupportMerge
open OriginalFacetCertificates
namespace OriginalFacetCertificatesSanity
noncomputable section
open scoped Classical

def vertices : Fin 3 → Plane :=
  ![WithLp.toLp 2 ![0,0],WithLp.toLp 2 ![0,1],WithLp.toLp 2 ![1,0]]

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
    all_goals try
      norm_num [vertices,next,outwardNormal,edgeVector,rotateCW,inner,Fin.sum_univ_two] at hz
    all_goals norm_num [vertices,next]

def firstSide : Side triangle triangle :=
  ⟨unitRay (outwardNormal triangle.vertex 0),
    (mem_mergedRays triangle triangle _).mpr ⟨Sum.inl 0,rfl⟩⟩

def actualCertificate := certificate triangle triangle (h := 2) (by norm_num) firstSide

theorem actual_dimension : Module.finrank ℝ (FaceSpace triangle triangle 2 firstSide) = 2 :=
  faceSpace_finrank triangle triangle 2 firstSide

theorem actual_interior : (interior actualCertificate.domain).Nonempty :=
  ⟨actualCertificate.center,actualCertificate.center_interior⟩

theorem actual_plane_chart :
    Set.range actualCertificate.chart =
      {p | (halfspaces triangle triangle 2).row actualCertificate.row p = 0} :=
  actualCertificate.chart_range

end
end OriginalFacetCertificatesSanity
#print axioms OriginalFacetCertificatesSanity.triangle
#print axioms OriginalFacetCertificatesSanity.actualCertificate
#print axioms OriginalFacetCertificatesSanity.actual_dimension
#print axioms OriginalFacetCertificatesSanity.actual_interior
#check OriginalFacetCertificatesSanity.actual_plane_chart
