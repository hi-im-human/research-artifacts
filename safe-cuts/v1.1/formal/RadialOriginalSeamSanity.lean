import RadialOriginalSeam

open Set
open scoped Classical NNReal
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open PhysicalMixedTurnSource RadialOriginalSeam

namespace RadialOriginalSeamSanity
noncomputable section

/-- Identical triples (the algebraic model of a retained triangular/tie case)
are accepted by the fixed selector; no pairwise-distinct assumption appears. -/
example (O U G : RadialOriginalSeam.Plane) :
    ∃ k ε, 0 < ε ∧ ∀ i δ, 0 < δ → δ < ε →
      ‖retainedUpperVector O ((fun _ : Fin 3 => U) i)
        ((fun _ : Fin 3 => G) i) δ‖ ^ 2 ≤
      ‖retainedUpperVector O ((fun _ : Fin 3 => U) k)
        ((fun _ : Fin 3 => G) k) δ‖ ^ 2 :=
  exists_fixed_eventual_retainedUpper_max O (fun _ : Fin 3 => U) (fun _ => G)

/-- The source selector is available directly in the negative RF branch. -/
example {nA nB : ℕ} [NeZero nA] [NeZero nB]
    (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
    {h : ℝ} (hh : 0 < h)
    (hΔ : intrinsicDelta A B (hh := hh) < 0) :
    0 < (selectedNegativeSeam A B hh hΔ).threshold :=
  (selectedNegativeSeam_spec A B hh hΔ).1

/-- The positive branch uses the globally reflected, rim-swapped geometry. -/
example {nA nB : ℕ} [NeZero nA] [NeZero nB]
    (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
    {h : ℝ} (hh : 0 < h)
    (hΔ : 0 < intrinsicDelta A B (hh := hh)) :
    0 < (selectedPositiveSeam A B hh hΔ).threshold :=
  (selectedPositiveSeam_spec A B hh hΔ).1

/-- Positive source: no RF, inwardness, or selector-correctness hypothesis. -/
example {nA nB : ℕ} [NeZero nA] [NeZero nB]
    (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
    {h : ℝ} (hh : 0 < h)
    (hΔ : 0 < intrinsicDelta A B (hh := hh)) :
    FixedBaselinePolarTrace.RadiallyInward
      (RadialExtremalSafety.reflectPlane
        (circuitPole A B hh 0 (ne_of_gt hΔ)))
      (selectedPositiveNormalizedSeamCurve A B hh hΔ) :=
  selectedPositiveNormalizedSeamCurve_radiallyInward A B hh hΔ

/-- Arbitrary unequal heights, including endpoint heights, stay cross-gap distinct. -/
example {nA nB : ℕ} [NeZero nA] [NeZero nB]
    (A : ReducedConvexPolygon nA) (B : ReducedConvexPolygon nB)
    {h : ℝ} (hh : 0 < h)
    (hΔ : 0 < intrinsicDelta A B (hh := hh)) :
    selectedPositiveNormalizedSeamCurve A B hh hΔ 0 ≠
      selectedPositiveNormalizedTerminalSeamCurve A B hh hΔ 1 :=
  selectedPositiveSeam_crossGap_allPairs_ne A B hh hΔ
    (by norm_num) (by norm_num) (by norm_num)

/-- A vanishing lower run is retained by the rim swap without dividing by it. -/
example {n : ℕ} (S : RadialExtremalSafety.TriangularRadialStrip n)
    (O : RadialOriginalSeam.Plane) (hR : S.PositiveRadialSupport O)
    (i : ℕ) (hz : S.lowerCoeff i = 0) :
    (S.reflectSwap).upperCoeff i = 0 ∧
      (S.reflectSwap).RadialSupport (RadialExtremalSafety.reflectPlane O) :=
  ⟨hz, RadialExtremalSafety.TriangularRadialStrip.reflectSwap_radialSupport hR⟩

/-- The upper-zero case is equally coefficient-safe. -/
example {n : ℕ} (S : RadialExtremalSafety.TriangularRadialStrip n)
    (O : RadialOriginalSeam.Plane) (hR : S.PositiveRadialSupport O)
    (i : ℕ) (hz : S.upperCoeff i = 0) :
    (S.reflectSwap).lowerCoeff i = 0 ∧
      (S.reflectSwap).RadialSupport (RadialExtremalSafety.reflectPlane O) :=
  ⟨hz, RadialExtremalSafety.TriangularRadialStrip.reflectSwap_radialSupport hR⟩

end
end RadialOriginalSeamSanity

#print axioms RadialOriginalSeam.exists_fixed_eventual_retainedUpper_max
#print axioms RadialOriginalSeam.selectedNegativeSeam_spec
#print axioms RadialOriginalSeam.selectedPositiveSeam_spec
#print axioms RadialOriginalSeam.selectedPositiveSeam_normalized_weak_endpoint_dot
#print axioms RadialOriginalSeam.selectedPositiveNormalizedSeamCurve_radiallyInward
#print axioms RadialOriginalSeam.selectedPositiveSeam_crossGap_allPairs_ne
