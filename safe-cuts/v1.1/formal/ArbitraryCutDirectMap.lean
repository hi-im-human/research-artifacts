import PhysicalRadialSupport
import PhysicalMixedTurnLayout
import RadialOriginalSeam

open Set
open scoped BigOperators Classical NNReal
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open CommonSupportMerge OriginalFacetCertificates NormalFanSplice MaximalSupportCells
open CyclicCutOrders EuclideanPrismatoidCoordinates PolyhedralInputBridge
open TrimmedFacetWitnesses BandGeometryAssembly FiniteWitnessClosure SingleCutRecovery
open CutSurfaceQuotient MixedTurnSafeCut PolygonSetReconstruction ConvexPolygonTurning

namespace GeneralTwoRimUnfolding
noncomputable section
set_option maxHeartbeats 8000000
open PhysicalMixedTurnSource

variable {nA nB : ℕ} [NeZero nA] [NeZero nB]
  (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
  {h : ℝ} (hh : 0 < h)

/-- The direct map with its source type exposed through the ordered-source alias. -/
noncomputable def directOrderedMapAt
    (k : Fin (MechanismN A B + 1))
    (i : Fin (sideCount A B - 1 + 1)) :
    FaceSpace A B h (cycle A B (orderSource A B k i)) →ᵃⁱ[ℝ]
      PhysicalMixedTurnSource.Plane := by
  change FaceSpace A B h (cycle A B (familySource A B k i.val)) →ᵃⁱ[ℝ]
    PhysicalMixedTurnSource.Plane
  exact directDevelopedMap A B hh k i.val

/-- Mixedness-free adapter from a mathematical entry cut to the existing
exit-edge source order. -/
noncomputable def arbitraryCutFaceMap
    (k : Fin (MechanismN A B + 1))
    (i : Fin (sideCount A B - 1 + 1)) :
    FaceSpace A B h (order A B (prev (sourceIndexEquiv A B k)) i) →ᵃⁱ[ℝ]
      PhysicalMixedTurnSource.Plane :=
  transportFaceMap A B (order_eq_cycle_orderSource A B k i)
    (directOrderedMapAt A B hh k i)

/-- The literal source-selected cut in the negative-defect branch.  This is
exactly the radial selector's original-seam index; it is unrelated to the
mixed-turn budget selector `fixedCutIndex`. -/
noncomputable def selectedNegativeCutIndex
    (hΔ : intrinsicDelta A B (hh := hh) < 0) : Fin (MechanismN A B + 1) :=
  (RadialOriginalSeam.selectedNegativeSeam A B hh hΔ).index

/-- The depth-independent direct maps rooted at the literal selected negative
seam.  The dependent face types are transported only along the proved
entry-cut/source-order equality. -/
noncomputable def selectedNegativeDirectMap
    (hΔ : intrinsicDelta A B (hh := hh) < 0)
    (i : Fin (sideCount A B - 1 + 1)) :
    FaceSpace A B h
        (order A B (prev (sourceIndexEquiv A B
          (selectedNegativeCutIndex A B hh hΔ))) i) →ᵃⁱ[ℝ]
      PhysicalMixedTurnSource.Plane :=
  arbitraryCutFaceMap A B hh (selectedNegativeCutIndex A B hh hΔ) i

lemma transportFaceMap_full_glue {u₀ v₀ u₁ v₁ : Side A B}
    (h₀ : u₀ = v₀) (h₁ : u₁ = v₁)
    (f₀ : FaceSpace A B h v₀ →ᵃⁱ[ℝ] PhysicalMixedTurnSource.Plane)
    (f₁ : FaceSpace A B h v₁ →ᵃⁱ[ℝ] PhysicalMixedTurnSource.Plane)
    (hg : ∀ x ∈ (certificate A B hh v₀).domain,
      ∀ y ∈ (certificate A B hh v₁).domain,
        (certificate A B hh v₀).chart x = (certificate A B hh v₁).chart y →
          f₀ x = f₁ y) :
    ∀ x ∈ (certificate A B hh u₀).domain,
      ∀ y ∈ (certificate A B hh u₁).domain,
        (certificate A B hh u₀).chart x = (certificate A B hh u₁).chart y →
          transportFaceMap A B h₀ f₀ x = transportFaceMap A B h₁ f₁ y := by
  subst v₀
  subst v₁
  exact hg


/-- Exact image of the selected negative-root map on the original height trim.
The equality transports the dependent source order before applying the direct
physical face image theorem; no mixed-turn assumption is involved. -/
theorem selectedNegativeDirectMap_heightTrim_image
    (hΔ : intrinsicDelta A B (hh := hh) < 0)
    {d : ℝ} (hd0 : 0 < d) (hd1 : d < (1 : ℝ) / 2)
    (i : Fin (MechanismN A B + 1)) :
    selectedNegativeDirectMap A B hh hΔ i ''
      heightTrim
        (certificate A B hh (order A B
          (prev (sourceIndexEquiv A B
            (selectedNegativeCutIndex A B hh hΔ))) i)).domain
        (certificate A B hh (order A B
          (prev (sourceIndexEquiv A B
            (selectedNegativeCutIndex A B hh hΔ))) i)).height d =
      (AffineIsometryEquiv.constVAdd ℝ PhysicalMixedTurnSource.Plane
        (localB A B hh d
          (familySource A B (selectedNegativeCutIndex A B hh hΔ) 0))) ''
        (physicalDevelopedFamily A B hh hd0 hd1).face
          (selectedNegativeCutIndex A B hh hΔ) i := by
  let k := selectedNegativeCutIndex A B hh hΔ
  change transportFaceMap A B (order_eq_cycle_orderSource A B k i)
      (directOrderedMapAt A B hh k i) '' _ = _
  rw [transportFaceMap_image_heightTrim A B hh]
  exact directDevelopedMap_heightTrim_image A B hh hd0 hd1 k i

#print selectedNegativeDirectMap_heightTrim_image
#print axioms selectedNegativeDirectMap_heightTrim_image

end
end GeneralTwoRimUnfolding



