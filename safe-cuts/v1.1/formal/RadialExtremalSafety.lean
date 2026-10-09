import PhysicalMixedTurnDevelopment

open Set
open scoped BigOperators Classical NNReal

namespace RadialExtremalSafety
noncomputable section

abbrev Plane := MixedTurnSafeCut.Plane

/-- A concretely positioned finite radial strip.  All fields are primitive
panel geometry; no injectivity, polar trace, or seam-existence conclusion is
stored in the record. -/
structure PositionedRadialStrip (n : ℕ) where
  B : ℕ → Plane
  e : ℕ → Plane
  d : ℕ → Plane
  ratio : ℕ → ℝ
  ratio_pos : ∀ i ≤ n, 0 < ratio i
  lower_step : ∀ i < n, B (i + 1) = B i + e i
  hinge_step : ∀ i < n, d (i + 1) = d i + (ratio i - 1) • e i
  orientation_neg : ∀ i ≤ n, MixedTurnSafeCut.det (e i) (d i) < 0

def reflectPlane (z : Plane) : Plane := WithLp.toLp 2 ![z 0, -z 1]

lemma reflectPlane_add (x y : Plane) :
    reflectPlane (x + y) = reflectPlane x + reflectPlane y := by
  ext i
  fin_cases i <;> simp [reflectPlane] <;> ring

lemma reflectPlane_sub (x y : Plane) :
    reflectPlane (x - y) = reflectPlane x - reflectPlane y := by
  ext i
  fin_cases i <;> simp [reflectPlane] <;> ring

lemma reflectPlane_smul (a : ℝ) (x : Plane) :
    reflectPlane (a • x) = a • reflectPlane x := by
  ext i
  fin_cases i <;> simp [reflectPlane]

lemma reflectPlane_reflectPlane (x : Plane) :
    reflectPlane (reflectPlane x) = x := by
  ext i
  fin_cases i <;> simp [reflectPlane]

lemma reflectPlane_neg (x : Plane) :
    reflectPlane (-x) = -reflectPlane x := by
  simpa using reflectPlane_smul (-1) x

lemma reflectPlane_inner (x y : Plane) :
    inner ℝ (reflectPlane x) (reflectPlane y) = inner ℝ x y := by
  simp [reflectPlane, inner, Fin.sum_univ_two]

lemma reflectPlane_norm (x : Plane) : ‖reflectPlane x‖ = ‖x‖ := by
  have he := reflectPlane_inner x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at he
  nlinarith [norm_nonneg (reflectPlane x), norm_nonneg x]

lemma det_reflectPlane (x y : Plane) :
    MixedTurnSafeCut.det (reflectPlane x) (reflectPlane y) =
      -MixedTurnSafeCut.det x y := by
  simp [reflectPlane, MixedTurnSafeCut.det]
  ring

lemma det_smul_left (a : ℝ) (x y : Plane) :
    MixedTurnSafeCut.det (a • x) y = a * MixedTurnSafeCut.det x y := by
  simp [MixedTurnSafeCut.det]
  ring

lemma det_smul_right (a : ℝ) (x y : Plane) :
    MixedTurnSafeCut.det x (a • y) = a * MixedTurnSafeCut.det x y := by
  simp [MixedTurnSafeCut.det]
  ring

lemma det_neg_right (x y : Plane) :
    MixedTurnSafeCut.det x (-y) = -MixedTurnSafeCut.det x y := by
  simp [MixedTurnSafeCut.det]
  ring

/-- Coefficient form used by the actual two-rim source.  Either rim coefficient
may vanish, so this representation includes triangular original facets without
dividing by an edge length. -/
structure TriangularRadialStrip (n : ℕ) where
  B : ℕ → Plane
  v : ℕ → Plane
  d : ℕ → Plane
  lowerCoeff : ℕ → ℝ
  upperCoeff : ℕ → ℝ
  v_ne_zero : ∀ i ≤ n, v i ≠ 0
  lowerCoeff_nonneg : ∀ i ≤ n, 0 ≤ lowerCoeff i
  upperCoeff_nonneg : ∀ i ≤ n, 0 ≤ upperCoeff i
  lower_step : ∀ i < n, B (i + 1) = B i + lowerCoeff i • v i
  hinge_step : ∀ i < n,
    d (i + 1) = d i + (upperCoeff i - lowerCoeff i) • v i
  orientation_neg : ∀ i ≤ n, MixedTurnSafeCut.det (v i) (d i) < 0

namespace TriangularRadialStrip

def point {n : ℕ} (S : TriangularRadialStrip n) (i : ℕ) (s t : ℝ) : Plane :=
  S.B i + t • S.d i +
    (s * ((1 - t) * S.lowerCoeff i + t * S.upperCoeff i)) • S.v i

def RadialSupport {n : ℕ} (S : TriangularRadialStrip n) (O : Plane) : Prop :=
  ∀ i ≤ n,
    MixedTurnSafeCut.det (S.B i - O) (S.v i) < 0 ∧
    MixedTurnSafeCut.det (S.B i + S.d i - O) (S.v i) < 0

lemma det_point {n : ℕ} (S : TriangularRadialStrip n)
    (O : Plane) (i : ℕ) (s t : ℝ) :
    MixedTurnSafeCut.det (S.point i s t - O) (S.v i) =
      (1 - t) * MixedTurnSafeCut.det (S.B i - O) (S.v i) +
        t * MixedTurnSafeCut.det (S.B i + S.d i - O) (S.v i) := by
  simp [point, MixedTurnSafeCut.det]
  ring

lemma support_point {n : ℕ} {S : TriangularRadialStrip n} {O : Plane}
    (hR : S.RadialSupport O) {i : ℕ} (hi : i ≤ n)
    {s t : ℝ} (_hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    MixedTurnSafeCut.det (S.point i s t - O) (S.v i) < 0 := by
  rw [det_point]
  obtain ⟨hlo, hup⟩ := hR i hi
  by_cases ht0 : t = 0
  · simp [ht0, hlo]
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hl : (1 - t) * MixedTurnSafeCut.det (S.B i - O) (S.v i) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.2) hlo.le
    have hu : t * MixedTurnSafeCut.det (S.B i + S.d i - O) (S.v i) < 0 :=
      mul_neg_of_pos_of_neg htpos hup
    linarith

/-- Triangular facets retain the same no-pole conclusion; no positive edge
coefficient is used. -/
lemma point_ne_pole {n : ℕ} {S : TriangularRadialStrip n} {O : Plane}
    (hR : S.RadialSupport O) {i : ℕ} (hi : i ≤ n)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    S.point i s t ≠ O := by
  intro hp
  have hd := support_point hR hi hs ht
  rw [hp, sub_self] at hd
  simp [MixedTurnSafeCut.det] at hd

def PositiveRadialSupport {n : ℕ} (S : TriangularRadialStrip n) (O : Plane) : Prop :=
  ∀ i ≤ n,
    0 < MixedTurnSafeCut.det (S.B i - O) (S.v i) ∧
    0 < MixedTurnSafeCut.det (S.B i + S.d i - O) (S.v i)

noncomputable def reflectSwap {n : ℕ} (S : TriangularRadialStrip n) :
    TriangularRadialStrip n where
  B i := reflectPlane (S.B i + S.d i)
  v i := reflectPlane (S.v i)
  d i := -reflectPlane (S.d i)
  lowerCoeff i := S.upperCoeff i
  upperCoeff i := S.lowerCoeff i
  v_ne_zero i hi := by
    intro hz
    have h0 := congrArg (fun z : Plane => z 0) hz
    have h1 := congrArg (fun z : Plane => z 1) hz
    apply S.v_ne_zero i hi
    ext k
    fin_cases k
    · simpa [reflectPlane] using h0
    · simpa [reflectPlane] using congrArg Neg.neg h1
  lowerCoeff_nonneg i hi := S.upperCoeff_nonneg i hi
  upperCoeff_nonneg i hi := S.lowerCoeff_nonneg i hi
  lower_step i hi := by
    rw [S.lower_step i hi, S.hinge_step i hi]
    simp_rw [reflectPlane_add, reflectPlane_smul]
    module
  hinge_step i hi := by
    rw [S.hinge_step i hi]
    simp_rw [reflectPlane_add, reflectPlane_smul]
    module
  orientation_neg i hi := by
    rw [det_neg_right, det_reflectPlane]
    simpa only [neg_neg] using S.orientation_neg i hi

lemma reflectSwap_point {n : ℕ} (S : TriangularRadialStrip n)
    (i : ℕ) (s t : ℝ) :
    (reflectSwap S).point i s t = reflectPlane (S.point i s (1 - t)) := by
  simp only [point, reflectSwap, reflectPlane_add, reflectPlane_smul]
  module

lemma reflectSwap_radialSupport {n : ℕ} {S : TriangularRadialStrip n} {O : Plane}
    (hR : S.PositiveRadialSupport O) :
    (reflectSwap S).RadialSupport (reflectPlane O) := by
  intro i hi
  obtain ⟨hlo, hup⟩ := hR i hi
  constructor
  · change MixedTurnSafeCut.det
      (reflectPlane (S.B i + S.d i) - reflectPlane O)
      (reflectPlane (S.v i)) < 0
    rw [← reflectPlane_sub, det_reflectPlane]
    linarith
  · change MixedTurnSafeCut.det
      (reflectPlane (S.B i + S.d i) - reflectPlane (S.d i) - reflectPlane O)
      (reflectPlane (S.v i)) < 0
    rw [← reflectPlane_sub, ← reflectPlane_sub, det_reflectPlane]
    simp only [add_sub_cancel_right]
    linarith

end TriangularRadialStrip

namespace PositionedRadialStrip

def point {n : ℕ} (S : PositionedRadialStrip n) (i : ℕ) (s t : ℝ) : Plane :=
  MixedTurnSafeCut.panel (S.B i) (S.e i) (S.d i) (S.ratio i) s t

def face {n : ℕ} (S : PositionedRadialStrip n) (i : Fin (n + 1)) : Set Plane :=
  MixedTurnSafeCut.hull (S.B i) (S.e i) (S.d i) (S.ratio i)

def RadialSupport {n : ℕ} (S : PositionedRadialStrip n) (O : Plane) : Prop :=
  ∀ i ≤ n,
    MixedTurnSafeCut.det (S.B i - O) (S.e i) < 0 ∧
    MixedTurnSafeCut.det (S.B i + S.d i - O) (S.e i) < 0

def PositiveRadialSupport {n : ℕ} (S : PositionedRadialStrip n) (O : Plane) : Prop :=
  ∀ i ≤ n,
    0 < MixedTurnSafeCut.det (S.B i - O) (S.e i) ∧
    0 < MixedTurnSafeCut.det (S.B i + S.d i - O) (S.e i)

/-- Positive-defect normalization: globally reflect and interchange the two
rims.  The reciprocal is harmless because every physical ratio is positive. -/
noncomputable def reflectSwap {n : ℕ} (S : PositionedRadialStrip n) :
    PositionedRadialStrip n where
  B i := reflectPlane (S.B i + S.d i)
  e i := S.ratio i • reflectPlane (S.e i)
  d i := -reflectPlane (S.d i)
  ratio i := (S.ratio i)⁻¹
  ratio_pos i hi := inv_pos.mpr (S.ratio_pos i hi)
  lower_step i hi := by
    rw [S.lower_step i hi, S.hinge_step i hi]
    simp_rw [reflectPlane_add, reflectPlane_smul]
    module
  hinge_step i hi := by
    rw [S.hinge_step i hi]
    simp_rw [reflectPlane_add, reflectPlane_smul]
    have ha := ne_of_gt (S.ratio_pos i (Nat.le_of_lt hi))
    have hcoef : ((S.ratio i)⁻¹ - 1) * S.ratio i = 1 - S.ratio i := by
      field_simp [ha]
    rw [smul_smul, hcoef]
    module
  orientation_neg i hi := by
    simp only [det_smul_left, det_neg_right, det_reflectPlane]
    have ha := S.ratio_pos i hi
    have ho := S.orientation_neg i hi
    nlinarith

/-- Reflection plus rim interchange turns the positive-support branch into the
same negative-support convention without losing physical orientation. -/
theorem reflectSwap_radialSupport {n : ℕ} {S : PositionedRadialStrip n} {O : Plane}
    (hR : S.PositiveRadialSupport O) :
    (reflectSwap S).RadialSupport (reflectPlane O) := by
  intro i hi
  obtain ⟨hlo, hup⟩ := hR i hi
  have ha := S.ratio_pos i hi
  constructor
  · change MixedTurnSafeCut.det
      (reflectPlane (S.B i + S.d i) - reflectPlane O)
      (S.ratio i • reflectPlane (S.e i)) < 0
    rw [← reflectPlane_sub, det_smul_right, det_reflectPlane]
    nlinarith
  · change MixedTurnSafeCut.det
      (reflectPlane (S.B i + S.d i) - reflectPlane (S.d i) - reflectPlane O)
      (S.ratio i • reflectPlane (S.e i)) < 0
    rw [← reflectPlane_sub, ← reflectPlane_sub, det_smul_right, det_reflectPlane]
    simp only [add_sub_cancel_right]
    nlinarith

lemma det_point (B e d O : Plane) (a s t : ℝ) :
    MixedTurnSafeCut.det
        (MixedTurnSafeCut.panel B e d a s t - O) e =
      (1 - t) * MixedTurnSafeCut.det (B - O) e +
        t * MixedTurnSafeCut.det (B + d - O) e := by
  simp [MixedTurnSafeCut.panel, MixedTurnSafeCut.rho, MixedTurnSafeCut.det]
  ring

/-- Every material point of a supported panel lies strictly in its radial
halfplane. -/
lemma support_point {n : ℕ} {S : PositionedRadialStrip n} {O : Plane}
    (hR : S.RadialSupport O) {i : ℕ} (hi : i ≤ n)
    {s t : ℝ} (_hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    MixedTurnSafeCut.det (S.point i s t - O) (S.e i) < 0 := by
  rw [point, det_point]
  obtain ⟨hlo, hup⟩ := hR i hi
  by_cases ht0 : t = 0
  · simp [ht0, hlo]
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hleft : (1 - t) * MixedTurnSafeCut.det (S.B i - O) (S.e i) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.2) hlo.le
    have hright : t * MixedTurnSafeCut.det (S.B i + S.d i - O) (S.e i) < 0 :=
      mul_neg_of_pos_of_neg htpos hup
    linarith

lemma point_ne_pole {n : ℕ} {S : PositionedRadialStrip n} {O : Plane}
    (hR : S.RadialSupport O) {i : ℕ} (hi : i ≤ n)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    S.point i s t ≠ O := by
  intro heq
  have hp := support_point hR hi hs ht
  rw [heq, sub_self] at hp
  simp [MixedTurnSafeCut.det] at hp

lemma ray_denominator_neg {n : ℕ} {S : PositionedRadialStrip n} {O v : Plane}
    (hR : S.RadialSupport O) {i : ℕ} (hi : i ≤ n)
    {s t r : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hr : 0 < r) (hp : S.point i s t - O = r • v) :
    MixedTurnSafeCut.det v (S.e i) < 0 := by
  have hd := support_point hR hi hs ht
  rw [hp] at hd
  simp only [MixedTurnSafeCut.det, PiLp.smul_apply, smul_eq_mul] at hd ⊢
  nlinarith

/-- Exact affine radius equation on a fixed physical ray.  The preceding
strict denominator theorem shows this equation determines the radius. -/
lemma ray_radius_det_formula {n : ℕ} {S : PositionedRadialStrip n} {O v : Plane}
    {i : ℕ} {s t r : ℝ}
    (hp : S.point i s t - O = r • v) :
    r * MixedTurnSafeCut.det v (S.e i) =
      (1 - t) * MixedTurnSafeCut.det (S.B i - O) (S.e i) +
        t * MixedTurnSafeCut.det (S.B i + S.d i - O) (S.e i) := by
  calc
    _ = MixedTurnSafeCut.det (r • v) (S.e i) := by
      rw [det_smul_left]
    _ = MixedTurnSafeCut.det (S.point i s t - O) (S.e i) := by rw [hp]
    _ = _ := det_point (S.B i) (S.e i) (S.d i) O (S.ratio i) s t

end PositionedRadialStrip

/-- Coefficientwise lexicographic dominance for an exact quadratic family. -/
def QuadraticLexMax {ι : Type*} (c₀ c₁ c₂ : ι → ℝ) (k : ι) : Prop :=
  ∀ i, c₀ i < c₀ k ∨
    (c₀ i = c₀ k ∧ c₁ i < c₁ k) ∨
    (c₀ i = c₀ k ∧ c₁ i = c₁ k ∧ c₂ i ≤ c₂ k)

def quadraticValue {ι : Type*} (c₀ c₁ c₂ : ι → ℝ) (i : ι) (δ : ℝ) : ℝ :=
  c₀ i + δ * c₁ i + δ ^ 2 * c₂ i

theorem exists_quadraticLexMax {ι : Type*} [Fintype ι] [Nonempty ι]
    (c₀ c₁ c₂ : ι → ℝ) : ∃ k, QuadraticLexMax c₀ c₁ c₂ k := by
  let score : ι → (ℝ ×ₗ (ℝ ×ₗ ℝ)) := fun i =>
    toLex (c₀ i, toLex (c₁ i, c₂ i))
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ score Finset.univ_nonempty
  refine ⟨k, ?_⟩
  intro i
  have hi := hk i (Finset.mem_univ i)
  dsimp [score] at hi
  rw [Prod.Lex.toLex_le_toLex] at hi
  rcases hi with h0 | ⟨hc0, h12⟩
  · exact Or.inl h0
  · rw [Prod.Lex.toLex_le_toLex] at h12
    rcases h12 with h1 | ⟨hc1, h2⟩
    · exact Or.inr (Or.inl ⟨hc0, h1⟩)
    · exact Or.inr (Or.inr ⟨hc0, hc1, h2⟩)

/-- A lexicographic coefficient maximum really is an eventual maximum of the
exact quadratic family; this is the analytic selector used at an extremal
original seam. -/
theorem QuadraticLexMax.eventually_ge {ι : Type*} {c₀ c₁ c₂ : ι → ℝ} {k : ι}
    (hk : QuadraticLexMax c₀ c₁ c₂ k) :
    ∀ i, ∃ ε > 0, ∀ δ, 0 < δ → δ < ε →
      quadraticValue c₀ c₁ c₂ i δ ≤ quadraticValue c₀ c₁ c₂ k δ := by
  intro i
  rcases hk i with h0 | h1 | h2
  · let M := |c₁ i - c₁ k| + |c₂ i - c₂ k| + 1
    let ε := min 1 ((c₀ k - c₀ i) / (2 * M))
    have hM : 0 < M := by dsimp [M]; positivity
    have hgap : 0 < c₀ k - c₀ i := sub_pos.mpr h0
    have heps : 0 < ε := by dsimp [ε]; positivity
    refine ⟨ε, heps, ?_⟩
    intro δ hδ hδε
    have hd1 : δ < 1 := lt_of_lt_of_le hδε (min_le_left _ _)
    have hd2 : δ < (c₀ k - c₀ i) / (2 * M) :=
      lt_of_lt_of_le hδε (min_le_right _ _)
    have ha1 := le_abs_self (c₁ i - c₁ k)
    have ha2 := le_abs_self (c₂ i - c₂ k)
    have hδ2 : δ ^ 2 ≤ δ := by nlinarith
    dsimp [quadraticValue]
    have hbound : δ * |c₁ i - c₁ k| + δ ^ 2 * |c₂ i - c₂ k| <
        c₀ k - c₀ i := by
      have hmul := (lt_div_iff₀ (show 0 < 2 * M by positivity)).mp hd2
      dsimp [M] at hmul ⊢
      nlinarith [abs_nonneg (c₁ i - c₁ k), abs_nonneg (c₂ i - c₂ k)]
    nlinarith [mul_le_mul_of_nonneg_left ha1 hδ.le,
      mul_le_mul_of_nonneg_left ha2 (sq_nonneg δ)]
  · rcases h1 with ⟨hc0, hc1⟩
    let M := |c₂ i - c₂ k| + 1
    let ε := min 1 ((c₁ k - c₁ i) / (2 * M))
    have hM : 0 < M := by dsimp [M]; positivity
    have hgap : 0 < c₁ k - c₁ i := sub_pos.mpr hc1
    have heps : 0 < ε := by dsimp [ε]; positivity
    refine ⟨ε, heps, ?_⟩
    intro δ hδ hδε
    have hd1 : δ < 1 := lt_of_lt_of_le hδε (min_le_left _ _)
    have hd2 : δ < (c₁ k - c₁ i) / (2 * M) :=
      lt_of_lt_of_le hδε (min_le_right _ _)
    have ha2 := le_abs_self (c₂ i - c₂ k)
    have hmul := (lt_div_iff₀ (show 0 < 2 * M by positivity)).mp hd2
    dsimp [quadraticValue, M] at hmul ⊢
    rw [hc0]
    have hδ2 : δ ^ 2 ≤ δ := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left ha2 (sq_nonneg δ),
      abs_nonneg (c₂ i - c₂ k)]
  · rcases h2 with ⟨hc0, hc1, hc2⟩
    refine ⟨1, by norm_num, ?_⟩
    intro δ hδ _
    dsimp [quadraticValue]
    rw [hc0, hc1]
    have hmul := mul_le_mul_of_nonneg_left hc2 (sq_nonneg δ)
    linarith

/-- A finite exact quadratic family has one fixed eventual maximizer and one
uniform positive threshold.  No per-depth seam choice occurs. -/
theorem exists_eventual_quadratic_max {ι : Type*} [Fintype ι] [Nonempty ι]
    (c₀ c₁ c₂ : ι → ℝ) :
    ∃ k ε, 0 < ε ∧ ∀ i δ, 0 < δ → δ < ε →
      quadraticValue c₀ c₁ c₂ i δ ≤ quadraticValue c₀ c₁ c₂ k δ := by
  obtain ⟨k, hk⟩ := exists_quadraticLexMax c₀ c₁ c₂
  have hlocal := hk.eventually_ge
  let εi : ι → ℝ := fun i => Classical.choose (hlocal i)
  have hεi : ∀ i, 0 < εi i := fun i => (Classical.choose_spec (hlocal i)).1
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ εi Finset.univ_nonempty
  refine ⟨k, εi j, hεi j, ?_⟩
  intro i δ hδ hδε
  exact (Classical.choose_spec (hlocal i)).2 δ hδ
    (lt_of_lt_of_le hδε (hj i (Finset.mem_univ i)))

/-- Squared norm expansion used by the extremal selector. -/
lemma norm_sq_add (x y : Plane) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ x y + ‖y‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right]
  rw [real_inner_comm y x]
  ring

lemma incoming_dot_lower {a f : Plane}
    (hmax : ‖a - f‖ ^ 2 ≤ ‖a‖ ^ 2) :
    ‖f‖ ^ 2 / 2 ≤ inner ℝ a f := by
  have he := norm_sq_add a (-f)
  rw [norm_neg, inner_neg_right] at he
  have haf : a + -f = a - f := by abel
  rw [haf] at he
  nlinarith

lemma incoming_dot_pos {a f : Plane} (hf : f ≠ 0)
    (hmax : ‖a - f‖ ^ 2 ≤ ‖a‖ ^ 2) : 0 < inner ℝ a f := by
  have hl := incoming_dot_lower hmax
  have hn : 0 < ‖f‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hf)
  nlinarith

lemma outgoing_dot_upper {a e : Plane}
    (hmax : ‖a + e‖ ^ 2 ≤ ‖a‖ ^ 2) :
    inner ℝ a e ≤ -(‖e‖ ^ 2 / 2) := by
  have he := norm_sq_add a e
  nlinarith

lemma outgoing_dot_neg {a e : Plane} (he0 : e ≠ 0)
    (hmax : ‖a + e‖ ^ 2 ≤ ‖a‖ ^ 2) : inner ℝ a e < 0 := by
  have hu := outgoing_dot_upper hmax
  have hn : 0 < ‖e‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr he0)
  nlinarith

/-- Coordinate-free two-dimensional determinant/inner-product identity. -/
lemma norm_sq_mul_det (a f e : Plane) :
    ‖a‖ ^ 2 * MixedTurnSafeCut.det f e =
      inner ℝ a f * MixedTurnSafeCut.det a e -
        MixedTurnSafeCut.det a f * inner ℝ a e := by
  rw [← real_inner_self_eq_norm_sq]
  simp [MixedTurnSafeCut.det, inner, Fin.sum_univ_two]
  ring

lemma det_incident_neg {a f e : Plane}
    (ha : a ≠ 0)
    (haf_dot : 0 < inner ℝ a f)
    (hae_dot : inner ℝ a e < 0)
    (haf_det : MixedTurnSafeCut.det a f < 0)
    (hae_det : MixedTurnSafeCut.det a e < 0) :
    MixedTurnSafeCut.det f e < 0 := by
  have hid := norm_sq_mul_det a f e
  have hnorm : 0 < ‖a‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr ha)
  have hrhs : inner ℝ a f * MixedTurnSafeCut.det a e -
      MixedTurnSafeCut.det a f * inner ℝ a e < 0 := by
    nlinarith [mul_neg_of_pos_of_neg haf_dot hae_det,
      mul_pos_of_neg_of_neg haf_det hae_dot]
  nlinarith

/-- Cramer's formula in the project plane. -/
lemma cramer_two_dimensional {f e g : Plane}
    (hfe : MixedTurnSafeCut.det f e ≠ 0) :
    g = (MixedTurnSafeCut.det g e / MixedTurnSafeCut.det f e) • f +
      (MixedTurnSafeCut.det f g / MixedTurnSafeCut.det f e) • e := by
  ext i
  fin_cases i
  · change g 0 = _
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp [hfe]
    simp only [MixedTurnSafeCut.det]
    simp
    ring
  · change g 1 = _
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp [hfe]
    simp only [MixedTurnSafeCut.det]
    simp
    ring

lemma hinge_in_negative_positive_cone {f e g : Plane}
    (hfe : MixedTurnSafeCut.det f e < 0)
    (hfg : MixedTurnSafeCut.det f g < 0)
    (heg : MixedTurnSafeCut.det e g < 0) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ g = A • (-f) + B • e := by
  let K := -MixedTurnSafeCut.det f e
  let A := MixedTurnSafeCut.det g e / K
  let B := -MixedTurnSafeCut.det f g / K
  have hK : 0 < K := by dsimp [K]; linarith
  have hge : 0 < MixedTurnSafeCut.det g e := by
    simp only [MixedTurnSafeCut.det] at heg ⊢
    linarith
  have hA : 0 < A := div_pos hge hK
  have hB : 0 < B := div_pos (neg_pos.mpr hfg) hK
  refine ⟨A, B, hA, hB, ?_⟩
  have hc := cramer_two_dimensional (f := f) (e := e) (g := g) (ne_of_lt hfe)
  rw [hc]
  dsimp [A, B, K]
  module

lemma inner_hinge_neg_of_incident_cone {a f e g : Plane}
    (haf : 0 < inner ℝ a f) (hae : inner ℝ a e < 0)
    (hcone : ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ g = A • (-f) + B • e) :
    inner ℝ a g < 0 := by
  rcases hcone with ⟨A, B, hA, hB, rfl⟩
  simp only [inner_add_right, inner_smul_right, inner_neg_right]
  nlinarith [mul_pos hA haf, mul_neg_of_pos_of_neg hB hae]

/-- A point on the hinge, written from its upper endpoint. -/
def hingePoint (U G : Plane) (t : ℝ) : Plane := U - (1 - t) • G

theorem hinge_normSq_sub (U G : Plane) {t₁ t₂ : ℝ} :
    ‖hingePoint U G t₂‖ ^ 2 - ‖hingePoint U G t₁‖ ^ 2 =
      (t₂ - t₁) *
        (2 * inner ℝ U G - (2 - t₁ - t₂) * ‖G‖ ^ 2) := by
  have h₁ := norm_sq_add U (-(1 - t₁) • G)
  have h₂ := norm_sq_add U (-(1 - t₂) • G)
  have ha₁ : |1 + -t₁| ^ 2 = (1 + -t₁) ^ 2 := sq_abs (1 + -t₁)
  have ha₂ : |1 + -t₂| ^ 2 = (1 + -t₂) ^ 2 := sq_abs (1 + -t₂)
  simp only [hingePoint, sub_eq_add_neg, neg_smul, norm_smul, norm_neg,
    Real.norm_eq_abs, inner_smul_right] at h₁ h₂ ⊢
  rw [mul_pow, ha₁] at h₁
  rw [mul_pow, ha₂] at h₂
  rw [h₂, h₁]
  simp only [inner_neg_right, inner_smul_right]
  ring

/-- The weak endpoint derivative is enough for strict inward motion on the
whole physical hinge, including restored triangular facets. -/
theorem hinge_normSq_strictAntiOn {U G : Plane} (hG : G ≠ 0)
    (hUG : inner ℝ U G ≤ 0) :
    StrictAntiOn (fun t => ‖hingePoint U G t‖ ^ 2) (Icc (0 : ℝ) 1) := by
  intro t₁ ht₁ t₂ ht₂ hlt
  have he := hinge_normSq_sub U G (t₁ := t₁) (t₂ := t₂)
  have hnorm : 0 < ‖G‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hG)
  have hcoef : 0 < 2 - t₁ - t₂ := by linarith [ht₁.2, ht₂.2]
  have hbracket : 2 * inner ℝ U G - (2 - t₁ - t₂) * ‖G‖ ^ 2 < 0 := by
    nlinarith [mul_pos hcoef hnorm]
  nlinarith

end
end RadialExtremalSafety
