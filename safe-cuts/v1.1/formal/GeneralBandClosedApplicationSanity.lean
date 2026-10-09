import GeneralBandClosedApplication
import PolygonSetReconstructionSanity

open Set MergedNormalPrismatoid PolygonSetReconstruction
open PolygonSetReconstructionSanity GeneralBandClosedApplication
open CommonSupportMerge CyclicCutOrders CutSurfaceQuotient EuclideanPrismatoidCoordinates

namespace GeneralBandClosedApplicationSanity
noncomputable section

/-- Exact finite clouds extending the unit square in different directions. -/
def cloudA : Finset Plane := insert (pt 3 0) cloud
def cloudB : Finset Plane := insert (pt 0 3) cloud
def KA : Set Plane := convexHull ℝ (↑cloudA : Set Plane)
def KB : Set Plane := convexHull ℝ (↑cloudB : Set Plane)

lemma KA_finite_hull : ∃ S : Finset Plane, convexHull ℝ (↑S : Set Plane) = KA :=
  ⟨cloudA, rfl⟩
lemma KB_finite_hull : ∃ S : Finset Plane, convexHull ℝ (↑S : Set Plane) = KB :=
  ⟨cloudB, rfl⟩

lemma KA_interior : (interior KA).Nonempty := by
  apply cloud_interior.mono
  apply interior_mono
  apply convexHull_mono
  intro p hp
  exact Finset.mem_insert_of_mem hp

lemma KB_interior : (interior KB).Nonempty := by
  apply cloud_interior.mono
  apply interior_mono
  apply convexHull_mono
  intro p hp
  exact Finset.mem_insert_of_mem hp

private def coord (i : Fin 2) : Plane →ₗ[ℝ] ℝ where
  toFun := fun p => p i
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

lemma KA_y_le_one {p : Plane} (hp : p ∈ KA) : p 1 ≤ 1 := by
  have hs : (↑cloudA : Set Plane) ⊆ {p | coord 1 p ≤ 1} := by
    intro p hp
    change p 1 ≤ 1
    simp only [cloudA, cloud, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [coord, pt]
  exact convexHull_min hs (convex_halfSpace_le (coord 1).isLinear 1) hp

lemma KB_x_le_one {p : Plane} (hp : p ∈ KB) : p 0 ≤ 1 := by
  have hs : (↑cloudB : Set Plane) ⊆ {p | coord 0 p ≤ 1} := by
    intro p hp
    change p 0 ≤ 1
    simp only [cloudB, cloud, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [coord, pt]
  exact convexHull_min hs (convex_halfSpace_le (coord 0).isLinear 1) hp

/-- Stronger than failure of strict nesting: A is not even contained in B. -/
lemma KA_not_subset_KB : ¬ KA ⊆ KB := by
  intro hs
  have hm : pt 3 0 ∈ KA := subset_convexHull ℝ _ (by simp [cloudA])
  have hh := KB_x_le_one (hs hm)
  norm_num [pt] at hh

lemma KB_not_subset_KA : ¬ KB ⊆ KA := by
  intro hs
  have hm : pt 0 3 ∈ KB := subset_convexHull ℝ _ (by simp [cloudB])
  have hh := KA_y_le_one (hs hm)
  norm_num [pt] at hh

lemma KA_not_strictly_nested : ¬ KA ⊆ interior KB :=
  fun hs => KA_not_subset_KB (hs.trans interior_subset)
lemma KB_not_strictly_nested : ¬ KB ⊆ interior KA :=
  fun hs => KB_not_subset_KA (hs.trans interior_subset)

/-- Actual non-nested data at physical height one. The only unresolved input
is the ordinary external general-band theorem; no witness is fabricated. -/
theorem nonnested_cut_surface
    (hExternal : ExternalGeneralBandForSets KA KB (show (0 : ℝ) < 1 by norm_num)) :
    ∃ (PA : RawPresentation KA) (PB : RawPresentation KB),
      PA.polygon.body = KA ∧ PB.polygon.body = KB ∧
      physicalBodyOfSets KA KB 1 = physicalPrismatoid PA.polygon PB.polygon 1 ∧
      ∃ e : Fin (sideCount PA.polygon PB.polygon),
        Nonempty (CutSurfaceDevelopment PA.polygon PB.polygon
          (show (0 : ℝ) < 1 by norm_num) Plane e) := by
  exact exists_cut_surface_for_general_polygon_sets KA KB
    KA_finite_hull KB_finite_hull KA_interior KB_interior (by norm_num) hExternal

end
end GeneralBandClosedApplicationSanity

#check @GeneralBandClosedApplicationSanity.nonnested_cut_surface
#print axioms GeneralBandClosedApplicationSanity.nonnested_cut_surface
#print axioms GeneralBandClosedApplicationSanity.KA_not_strictly_nested
#print axioms GeneralBandClosedApplicationSanity.KB_not_strictly_nested
