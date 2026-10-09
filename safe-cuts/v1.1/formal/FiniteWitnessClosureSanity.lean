import FiniteWitnessClosure

/-! Conditional seam-count specializations; no polytope or external theorem
is manufactured here. The original geometric telescope remains explicit. -/
namespace FiniteWitnessClosureSanity

noncomputable def oneSeam :=
  @FiniteWitnessClosure.exists_safe_original_seam_of_trimmed_existence (Fin 1) inferInstance

noncomputable def threeSeams :=
  @FiniteWitnessClosure.exists_safe_original_seam_of_trimmed_existence (Fin 3) inferInstance

end FiniteWitnessClosureSanity

#check @FiniteWitnessClosure.exists_safe_original_seam_of_trimmed_existence
#check FiniteWitnessClosureSanity.oneSeam
#check FiniteWitnessClosureSanity.threeSeams
#print axioms FiniteWitnessClosureSanity.oneSeam
#print axioms FiniteWitnessClosureSanity.threeSeams
