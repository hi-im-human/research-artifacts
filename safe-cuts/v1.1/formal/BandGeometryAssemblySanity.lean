import BandGeometryAssembly

/-! Conditional endpoint specializations, not constructions of polytope data.
Keeping the full remaining telescope means separate source spaces and all
original hypotheses survive in each specialized statement. -/

namespace BandGeometryAssemblySanity

noncomputable def singleFace :=
  @BandGeometryAssembly.exactRestriction_of_planeEmbeddings 0

noncomputable def threeFaces :=
  @BandGeometryAssembly.exactRestriction_of_planeEmbeddings 2

end BandGeometryAssemblySanity

#check BandGeometryAssemblySanity.singleFace
#check BandGeometryAssemblySanity.threeFaces
#print axioms BandGeometryAssemblySanity.singleFace
#print axioms BandGeometryAssemblySanity.threeFaces
