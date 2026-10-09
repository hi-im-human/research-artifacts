import MergedNormalPrismatoid

/-!
# Distinguish affine product coordinates from the physical Euclidean metric

System, 2026-09-19. UNCOMPILED DRAFT.

The old Ambient := Plane × ℝ has the default MAXIMUM product norm. Its
convex-hull/height results remain valid algebra, but it is not physical R^3
with its Euclidean norm. The coordinate map below is LINEAR, NOT an isometry.
Use PhysicalAmbient for future physical face charts. No old definition changes.
-/
open Set
open MergedNormalPrismatoid
namespace EuclideanPrismatoidCoordinates
noncomputable section

abbrev PhysicalAmbient := EuclideanSpace ℝ (Fin 3)

def pack (p : Ambient) : PhysicalAmbient :=
  WithLp.toLp 2 ![p.1 0, p.1 1, p.2]

def unpack (p : PhysicalAmbient) : Ambient :=
  (WithLp.toLp 2 ![p 0, p 1], p 2)

/-- Coordinate/affine transport only; it does NOT preserve the old max norm. -/
def coordinateEquiv : Ambient ≃ₗ[ℝ] PhysicalAmbient where
  toFun := pack
  invFun := unpack
  left_inv := by
    rintro ⟨x,z⟩
    apply Prod.ext
    · ext k
      fin_cases k <;> rfl
    · rfl
  right_inv := by
    intro p
    ext k
    fin_cases k <;> rfl
  map_add' := by
    intro p q
    ext k
    fin_cases k <;> rfl
  map_smul' := by
    intro c p
    ext k
    fin_cases k <;> rfl

/-- The physical norm must satisfy Pythagoras, not take a maximum. -/
theorem physical_norm_sq (p : Ambient) :
    ‖pack p‖^2 = ‖p.1‖^2 + p.2^2 := by
  calc
    ‖pack p‖^2 = inner ℝ (pack p) (pack p) := (real_inner_self_eq_norm_sq _).symm
    _ = inner ℝ p.1 p.1 + p.2*p.2 := by
      simp [pack, inner, Fin.sum_univ_three, Fin.sum_univ_two]
      <;> ring
    _ = ‖p.1‖^2 + p.2^2 := by
      rw [real_inner_self_eq_norm_sq]
      ring

def physicalPrismatoid {nA nB : ℕ} [NeZero nA] [NeZero nB]
    (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB) (h : ℝ) :
    Set PhysicalAmbient :=
  convexHull ℝ ((fun x => pack (lowerLift x)) '' B.body ∪
    (fun x => pack (upperLift h x)) '' A.body)

/-- The old affine body is transported to the independently defined physical
Euclidean hull. This is set/linear equivalence, NOT a metric isometry. -/
theorem pack_prismatoid {nA nB : ℕ} [NeZero nA] [NeZero nB]
    (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB) (h : ℝ) :
    pack '' prismatoid A B h = physicalPrismatoid A B h := by
  change coordinateEquiv.toLinearMap ''
      convexHull ℝ (lowerLift '' B.body ∪ upperLift h '' A.body) = _
  rw [LinearMap.image_convexHull, Set.image_union, Set.image_image, Set.image_image]
  rfl

-- Deliberately no physical face-isometry claim is imported from old Ambient.
-- The universal constructor must use this Euclidean ambient (or equivalent).
end
end EuclideanPrismatoidCoordinates
#print axioms EuclideanPrismatoidCoordinates.physical_norm_sq
#check EuclideanPrismatoidCoordinates.coordinateEquiv
#print axioms EuclideanPrismatoidCoordinates.pack_prismatoid
