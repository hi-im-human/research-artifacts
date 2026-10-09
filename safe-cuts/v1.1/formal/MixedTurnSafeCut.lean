import FiniteWitnessClosure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
Position-sensitive mixed-turn safe-cut mechanism for explicitly certified
families. The fixed-X argument uses finite induction on panel count and the
intermediate value theorem instead of explicitly sorting transition times.
No safety premise is packaged as local geometry. The bridge from original
3D polytope data to DevelopedFamily remains a separate obligation.
-/
namespace MixedTurnSafeCut
open Set
open scoped BigOperators
noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def det (e d : Plane) : ℝ := e 0 * d 1 - e 1 * d 0

def rho (a t : ℝ) : ℝ := 1 - t + t * a

def panel (B e d : Plane) (a s t : ℝ) : Plane :=
  B + t • d + (s * rho a t) • e

lemma rho_pos {a t : ℝ} (ha : 0 < a) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < rho a t := by
  unfold rho
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h]; norm_num
  · have := mul_pos h ha
    linarith [ht.2]

/-- Local endpoint data only; global direction, injectivity and safety are absent. -/
structure Strip (m : ℕ) where
  B : Fin (m + 1) → Plane
  A : Fin (m + 1) → Plane
  ratio : Fin m → ℝ
  ratio_pos : ∀ i, 0 < ratio i
  parallel : ∀ i, A i.succ - A i.castSucc = ratio i • (B i.succ - B i.castSucc)
  orientation : (∀ i : Fin m, 0 < det (B i.succ - B i.castSucc) (A i.castSucc - B i.castSucc)) ∨
    (∀ i : Fin m, det (B i.succ - B i.castSucc) (A i.castSucc - B i.castSucc) < 0)

def Strip.face {m : ℕ} (S : Strip m) (i : Fin m) : Set Plane :=
  convexHull ℝ {S.B i.castSucc, S.B i.succ, S.A i.succ, S.A i.castSucc}

def Strip.map {m : ℕ} (S : Strip m) (i : Fin m) (s t : ℝ) : Plane :=
  panel (S.B i.castSucc) (S.B i.succ - S.B i.castSucc)
    (S.A i.castSucc - S.B i.castSucc) (S.ratio i) s t

/-- Actual matched hinges, including their endpoints. -/
theorem panel_right (B e d : Plane) (a t : ℝ) :
    panel B e d a 1 t = (B + e) + t • ((B + d + a • e) - (B + e)) := by
  ext k
  simp [panel, rho]
  ring

/-- Exact fixed-X affine trace. No generic-position exclusion on d.X. -/
theorem trace_identity (B e d : Plane) (a s t : ℝ) (he : e 0 ≠ 0) :
    (panel B e d a s t) 1 = B 1 + e 1 / e 0 * ((panel B e d a s t) 0 - B 0) +
      t * det e d / e 0 := by
  simp [panel, det]
  field_simp
  <;> ring

/-- The vertical-hinge case uses exactly the same trace slope. -/
theorem vertical_hinge_slope (e d : Plane) (he : e 0 ≠ 0) (hd : d 0 = 0) :
    det e d / e 0 = d 1 := by
  simp [det, hd, he]

/-- Quantitative comparison inside one panel at a common forward coordinate. -/
theorem trace_difference (B e d : Plane) (a s t r u : ℝ) (he : e 0 ≠ 0)
    (hx : (panel B e d a s t) 0 = (panel B e d a r u) 0) :
    (panel B e d a r u) 1 - (panel B e d a s t) 1 =
      (u - t) * (det e d / e 0) := by
  rw [trace_identity B e d a r u he, trace_identity B e d a s t he, hx]
  ring

/-- Local injectivity is not global strip injectivity. -/
theorem panel_injective (B e d : Plane) (a : ℝ) (ha : 0 < a)
    (hd : det e d ≠ 0) {s t r u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1)
    (h : panel B e d a s t = panel B e d a r u) : t = u ∧ s = r := by
  have h0 := congrArg (fun p : Plane => p 0) h
  have h1 := congrArg (fun p : Plane => p 1) h
  simp only [panel, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h0 h1
  have htu : (t-u) * det e d = 0 := by
    unfold det
    linear_combination e 0 * h1 - e 1 * h0
  have htu' : t = u := by
    rcases mul_eq_zero.mp htu with htu | hbad
    · linarith
    · exact False.elim (hd hbad)
  refine ⟨htu', ?_⟩
  subst u
  have hp := rho_pos ha ht
  have he : e 0 ≠ 0 ∨ e 1 ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hd (by simp [det, hn.1, hn.2])
  rcases he with he | he
  · have : (s-r) * rho a t * e 0 = 0 := by nlinarith [h0]
    rcases mul_eq_zero.mp this with hsr | hbad
    · exact sub_eq_zero.mp ((mul_eq_zero.mp hsr).resolve_right (ne_of_gt hp))
    · exact False.elim (he hbad)
  · have : (s-r) * rho a t * e 1 = 0 := by nlinarith [h1]
    rcases mul_eq_zero.mp this with hsr | hbad
    · exact sub_eq_zero.mp ((mul_eq_zero.mp hsr).resolve_right (ne_of_gt hp))
    · exact False.elim (he hbad)

/-- The eligible-height set is convex, hence cannot have a missing interval. -/
theorem eligible_convex (b0 d0 bm dm x : ℝ) :
    Convex ℝ {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ b0 + t*d0 ≤ x ∧ x ≤ bm + t*dm} := by
  intro t ht u hu a b ha hb hab
  refine ⟨(convex_Icc (0 : ℝ) 1) ht.1 hu.1 ha hb hab, ?_, ?_⟩
  · dsimp
    have hsum := add_le_add (mul_le_mul_of_nonneg_left ht.2.1 ha)
      (mul_le_mul_of_nonneg_left hu.2.1 hb)
    nlinarith [congrArg (fun z : ℝ => z*b0) hab, congrArg (fun z : ℝ => z*x) hab]
  · dsimp
    have hsum := add_le_add (mul_le_mul_of_nonneg_left ht.2.2 ha)
      (mul_le_mul_of_nonneg_left hu.2.2 hb)
    nlinarith [congrArg (fun z : ℝ => z*bm) hab, congrArg (fun z : ℝ => z*x) hab]

/-- Scalar selection permits zero T at either end of the sign interval. -/
theorem mixed_budget_selection {ι : Type*} (q : ι → ℝ) (P N c : ℝ)
    (hTotal : P + N < 2*c)
    (hNeg : ∃ i, q i - (P-N) ≤ 0) (hPos : ∃ j, 0 ≤ q j - (P-N)) :
    ∃ k, P - max (q k) 0 < c ∧ N - max (-q k) 0 < c := by
  by_cases hP : P < c
  · by_cases hN : N < c
    · obtain ⟨k, _⟩ := hNeg
      exact ⟨k, by linarith [le_max_right (q k) 0],
        by linarith [le_max_right (-q k) 0]⟩
    · obtain ⟨k, hk⟩ := hNeg
      have hq : q k < 0 := by linarith
      refine ⟨k, ?_, ?_⟩
      · rw [max_eq_right (le_of_lt hq)]; linarith
      · rw [max_eq_left (by linarith : 0 ≤ -q k)]; linarith
  · obtain ⟨k, hk⟩ := hPos
    have hq : 0 < q k := by linarith
    refine ⟨k, ?_, ?_⟩
    · rw [max_eq_left (le_of_lt hq)]; linarith
    · rw [max_eq_right (by linarith : -q k ≤ 0)]; linarith

/-- No finiteness is needed for this pointwise zero-boundary fact. -/
theorem zero_cut_budgets (P N q c : ℝ) (hTotal : P+N < 2*c)
    (hq : q = P-N) : P-max q 0 < c ∧ N-max (-q) 0 < c := by
  by_cases h : 0 ≤ q
  · rw [max_eq_left h, max_eq_right (by linarith : -q ≤ 0)]
    constructor <;> linarith
  · have hn : q ≤ 0 := le_of_not_ge h
    rw [max_eq_right hn, max_eq_left (by linarith : 0 ≤ -q)]
    constructor <;> linarith

/-- Finite-strip trace comparison by removing the last panel. The intermediate
value argument includes constant/vertical hinges and zero-length transitions.
This replaces an explicit time partition; the induction is over actual panels. -/
theorem finite_trace_comparison (m : ℕ) (L Y : ℕ → ℝ → ℝ) (x μ : ℝ)
    (hcont : ∀ i, Continuous (L i))
    (horder : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i j, i ≤ j → j ≤ m → L i t ≤ L j t)
    (hinc : ∀ i < m, ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      t ≤ u → μ*(u-t) ≤ Y i u - Y i t)
    (hglue : ∀ i, i+1 < m → ∀ t ∈ Icc (0 : ℝ) 1,
      L (i+1) t = x → Y i t = Y (i+1) t)
    (i j : ℕ) (hi : i < m) (hj : j < m)
    (t u : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) (htu : t ≤ u)
    (hit : L i t ≤ x ∧ x ≤ L (i+1) t)
    (hju : L j u ≤ x ∧ x ≤ L (j+1) u) :
    μ*(u-t) ≤ Y j u - Y i t := by
  induction m generalizing i j t u with
  | zero => omega
  | succ m ih =>
    by_cases him : i < m
    · by_cases hjm : j < m
      · exact ih (fun t ht i j hij hj => horder t ht i j hij (by omega))
          (fun i hi => hinc i (by omega))
          (fun i hi => hglue i (by omega)) i j him hjm t u ht hu htu hit hju
      · have hj' : j = m := by omega
        subst j
        have hx : x ≤ L m t := hit.2.trans (horder t ht (i+1) m (by omega) (by omega))
        obtain ⟨v, hv, hvx⟩ := intermediate_value_Icc' htu (hcont m).continuousOn
          (show x ∈ Icc (L m u) (L m t) from ⟨hju.1, hx⟩)
        have hv01 : v ∈ Icc (0 : ℝ) 1 := ⟨ht.1.trans hv.1, hv.2.trans hu.2⟩
        have hm : m-1+1 = m := by omega
        have hprev : L (m-1) v ≤ x ∧ x ≤ L (m-1+1) v := by
          rw [hm, ← hvx]
          exact ⟨horder v hv01 (m-1) m (by omega) (by omega), le_rfl⟩
        have hp := ih (fun t ht i j hij hj => horder t ht i j hij (by omega))
          (fun i hi => hinc i (by omega))
          (fun i hi => hglue i (by omega)) i (m-1) him (by omega)
          t v ht hv01 hv.1 hit hprev
        have hg := hglue (m-1) (by omega) v hv01 (by simpa only [hm] using hvx)
        rw [hm] at hg
        have hn := hinc m (by omega) v hv01 u hu hv.2
        rw [hg] at hp
        nlinarith
    · have hi' : i = m := by omega
      subst i
      by_cases hjm : j < m
      · have hx : x ≤ L m u := hju.2.trans (horder u hu (j+1) m (by omega) (by omega))
        obtain ⟨v, hv, hvx⟩ := intermediate_value_Icc htu (hcont m).continuousOn
          (show x ∈ Icc (L m t) (L m u) from ⟨hit.1, hx⟩)
        have hv01 : v ∈ Icc (0 : ℝ) 1 := ⟨ht.1.trans hv.1, hv.2.trans hu.2⟩
        have hm : m-1+1 = m := by omega
        have hprev : L (m-1) v ≤ x ∧ x ≤ L (m-1+1) v := by
          rw [hm, ← hvx]
          exact ⟨horder v hv01 (m-1) m (by omega) (by omega), le_rfl⟩
        have hp := ih (fun t ht i j hij hj => horder t ht i j hij (by omega))
          (fun i hi => hinc i (by omega))
          (fun i hi => hglue i (by omega)) (m-1) j (by omega) hjm
          v u hv01 hu hv.2 hprev hju
        have hg := hglue (m-1) (by omega) v hv01 (by simpa only [hm] using hvx)
        rw [hm] at hg
        have hn := hinc m (by omega) t ht v hv01 hv.1
        rw [hg] at hp
        nlinarith
      · have hj' : j = m := by omega
        subst j
        exact hinc m (by omega) t ht u hu htu

def posVariation (θ : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, max (θ (k+1) - θ k) 0

lemma heading_difference_bound (θ : ℕ → ℝ) {i j : ℕ} (hij : i ≤ j) :
    θ j - θ i ≤ posVariation θ j - posVariation θ i := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    unfold posVariation at *
    rw [Finset.sum_range_succ]
    have := le_max_left (θ (j+1) - θ j) 0
    linarith

lemma posVariation_nonneg (θ : ℕ → ℝ) (n : ℕ) : 0 ≤ posVariation θ n :=
  Finset.sum_nonneg (fun i _ => le_max_right _ _)

lemma posVariation_mono (θ : ℕ → ℝ) {i j : ℕ} (hij : i ≤ j) :
    posVariation θ i ≤ posVariation θ j := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij)
    (fun k _ _ => le_max_right _ _)

/-- Controls every pair of headings, not just the terminal difference. -/
theorem heading_range (θ : ℕ → ℝ) (n : ℕ)
    (hP : posVariation θ n < Real.pi)
    (hN : posVariation (fun k => -θ k) n < Real.pi)
    (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) : θ j - θ i < Real.pi := by
  rcases le_total i j with hij | hji
  · have := heading_difference_bound θ hij
    have := posVariation_mono θ hj
    have := posVariation_nonneg θ i
    linarith
  · have := heading_difference_bound (fun k => -θ k) hji
    have := posVariation_mono (fun k => -θ k) hi
    have := posVariation_nonneg (fun k => -θ k) j
    linarith

/-- A physical unit direction in the genuine Euclidean plane. -/
def direction (θ : ℝ) : Plane := WithLp.toLp 2 ![Real.cos θ, Real.sin θ]

def forward (α : ℝ) (v : Plane) : ℝ := v 0 * Real.cos α + v 1 * Real.sin α

theorem forward_heading (θ α r : ℝ) :
    forward α (r • direction θ) = r * Real.cos (θ-α) := by
  simp [forward, direction, Real.cos_sub]
  ring

/-- The direction is derived from both budgets and actual heading representations.
There is no direction field in the input certificate. -/
theorem exists_forward_of_variations (n : ℕ) (θ : ℕ → ℝ)
    (e : Fin (n+1) → Plane) (length : Fin (n+1) → ℝ)
    (hlen : ∀ i, 0 < length i)
    (hrep : ∀ i, e i = length i • direction (θ i))
    (hP : posVariation θ n < Real.pi)
    (hN : posVariation (fun k => -θ k) n < Real.pi) :
    ∃ α : ℝ, ∀ i, 0 < forward α (e i) := by
  obtain ⟨imin, hmin⟩ := Finite.exists_min (fun i : Fin (n+1) => θ i)
  obtain ⟨imax, hmax⟩ := Finite.exists_max (fun i : Fin (n+1) => θ i)
  let α := (θ imin + θ imax)/2
  refine ⟨α, fun i => ?_⟩
  rw [hrep i, forward_heading]
  apply mul_pos (hlen i)
  apply Real.cos_pos_of_mem_Ioo
  have hwidth := heading_range θ n hP hN imin imax (by omega) (by omega)
  have hlo := hmin i
  have hhi := hmax i
  dsimp [α]
  constructor <;> linarith

/-- Equal longitudinal coordinates at unequal heights are impossible once the
local affine trace slopes and their hinge identities have been established. -/
theorem trace_height_unique (m : ℕ) (L Y : ℕ → ℝ → ℝ) (x μ : ℝ) (hμ : 0 < μ)
    (hcont : ∀ i, Continuous (L i))
    (horder : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i j, i ≤ j → j ≤ m → L i t ≤ L j t)
    (hinc : ∀ i < m, ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      t ≤ u → μ*(u-t) ≤ Y i u - Y i t)
    (hglue : ∀ i, i+1 < m → ∀ t ∈ Icc (0 : ℝ) 1,
      L (i+1) t = x → Y i t = Y (i+1) t)
    (i j : ℕ) (hi : i < m) (hj : j < m)
    (t u : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1)
    (hit : L i t ≤ x ∧ x ≤ L (i+1) t)
    (hju : L j u ≤ x ∧ x ≤ L (j+1) u)
    (hy : Y i t = Y j u) : t = u := by
  rcases lt_trichotomy t u with h | h | h
  · have := finite_trace_comparison m L Y x μ hcont horder hinc hglue
      i j hi hj t u ht hu (le_of_lt h) hit hju
    have := mul_pos hμ (sub_pos.mpr h)
    linarith
  · exact h
  · have := finite_trace_comparison m L Y x μ hcont horder hinc hglue
      j i hj hi u t hu ht (le_of_lt h) hju hit
    have := mul_pos hμ (sub_pos.mpr h)
    linarith

/-- Geometric global-height uniqueness from local positioned vectors, positive
parallel edges and coherent orientation in common-forward coordinates. No
trace, partition, monotonicity or injectivity hypothesis is supplied. -/
theorem positioned_height_unique (m : ℕ) (B e d : ℕ → Plane) (a : ℕ → ℝ)
    (ha : ∀ i < m, 0 < a i)
    (he : ∀ i < m, 0 < e i 0)
    (hd : ∀ i < m, 0 < det (e i) (d i))
    (hB : ∀ i < m, B (i+1) = B i + e i)
    (hdstep : ∀ i < m, d (i+1) = d i + (a i - 1) • e i)
    (i j : ℕ) (hi : i < m) (hj : j < m) (s t r u : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hr : r ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1)
    (hp : panel (B i) (e i) (d i) (a i) s t = panel (B j) (e j) (d j) (a j) r u) :
    t = u := by
  let L : ℕ → ℝ → ℝ := fun k v => B k 0 + v*d k 0
  let x := (panel (B i) (e i) (d i) (a i) s t) 0
  let Y : ℕ → ℝ → ℝ := fun k v =>
    B k 1 + e k 1 / e k 0 * (x-B k 0) + v * (det (e k) (d k) / e k 0)
  let slope : Fin m → ℝ := fun k => det (e k) (d k) / e k 0
  have hm : Nonempty (Fin m) := ⟨⟨i, hi⟩⟩
  letI := hm
  obtain ⟨kmin, hkmin⟩ := Finite.exists_min slope
  let μ := slope kmin
  have hμ : 0 < μ := div_pos (hd kmin kmin.isLt) (he kmin kmin.isLt)
  have hstep (k : ℕ) (hk : k < m) (v : ℝ) :
      L (k+1) v - L k v = rho (a k) v * e k 0 := by
    dsimp [L]
    rw [hB k hk, hdstep k hk]
    simp [rho]
    ring
  have horder (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) (k l : ℕ)
      (hkl : k ≤ l) (hl : l ≤ m) : L k v ≤ L l v := by
    induction l, hkl using Nat.le_induction with
    | base => exact le_rfl
    | succ l hkl ih =>
      have hh := hstep l (by omega) v
      have hhpos := mul_pos (rho_pos (ha l (by omega)) hv) (he l (by omega))
      have hprev := ih (by omega)
      linarith
  have hright (k : ℕ) (hk : k < m) (v : ℝ) :
      panel (B k) (e k) (d k) (a k) 1 v = B (k+1) + v • d (k+1) := by
    rw [hB k hk, hdstep k hk]
    ext c
    simp [panel, rho]
    ring
  have htrace (k : ℕ) (hk : k < m) (w v : ℝ)
      (hx : (panel (B k) (e k) (d k) (a k) w v) 0 = x) :
      (panel (B k) (e k) (d k) (a k) w v) 1 = Y k v := by
    rw [trace_identity _ _ _ _ _ _ (ne_of_gt (he k hk)), hx]
    dsimp [Y]
    ring
  have hglue (k : ℕ) (hk : k+1 < m) (v : ℝ) (_hv : v ∈ Icc (0 : ℝ) 1)
      (hx : L (k+1) v = x) : Y k v = Y (k+1) v := by
    have hleft : panel (B (k+1)) (e (k+1)) (d (k+1)) (a (k+1)) 0 v =
        B (k+1) + v • d (k+1) := by simp [panel]
    have hx1 : (panel (B k) (e k) (d k) (a k) 1 v) 0 = x := by
      rw [hright k (by omega)]; exact hx
    have hx0 : (panel (B (k+1)) (e (k+1)) (d (k+1)) (a (k+1)) 0 v) 0 = x := by
      rw [hleft]; exact hx
    rw [← htrace k (by omega) 1 v hx1, ← htrace (k+1) hk 0 v hx0,
      hright k (by omega), hleft]
  have hbounds (k : ℕ) (hk : k < m) (w v : ℝ)
      (hw : w ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1)
      (hx : (panel (B k) (e k) (d k) (a k) w v) 0 = x) :
      L k v ≤ x ∧ x ≤ L (k+1) v := by
    have hp := mul_pos (rho_pos (ha k hk) hv) (he k hk)
    have hh := hstep k hk v
    have hx' : x = L k v + w * (rho (a k) v * e k 0) := by
      rw [← hx]; simp [panel, L]; ring
    rw [hx']
    constructor <;> nlinarith [hw.1, hw.2]
  have hxi : (panel (B i) (e i) (d i) (a i) s t) 0 = x := rfl
  have hxj : (panel (B j) (e j) (d j) (a j) r u) 0 = x := by rw [← hp]
  apply trace_height_unique m L Y x μ hμ (by intro k; dsimp [L]; fun_prop)
    horder ?_ hglue i j hi hj t u ht hu (hbounds i hi s t hs ht hxi)
    (hbounds j hj r u hr hu hxj)
  · rw [← htrace i hi s t hxi, ← htrace j hj r u hxj, hp]
  · intro k hk v hv w hw hvw
    have hmin := hkmin (⟨k, hk⟩ : Fin m)
    change μ ≤ det (e k) (d k) / e k 0 at hmin
    dsimp [Y]
    nlinarith [mul_nonneg (sub_nonneg.mpr hvw) (sub_nonneg.mpr hmin)]

/-- No gap in a finite horizontal chain. This also works at shared endpoints. -/
lemma finite_intervals_cover (m : ℕ) (hm : 0 < m) (L : ℕ → ℝ) (x : ℝ)
    (h0 : L 0 ≤ x) (hmx : x ≤ L m) :
    ∃ i < m, L i ≤ x ∧ x ≤ L (i+1) := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases h : x ≤ L m
    · by_cases hm0 : m = 0
      · subst m; exact ⟨0, by omega, h0, hmx⟩
      · obtain ⟨i, hi, hli, hri⟩ := ih (by omega) h
        exact ⟨i, by omega, hli, hri⟩
    · exact ⟨m, by omega, (le_of_not_ge h), hmx⟩

/-- Exact eligible-height characterization of a strictly ordered horizontal
slice. Combined with eligible_convex, the height domain has no missing interval. -/
lemma eligible_height_iff (m : ℕ) (hm : 0 < m) (L : ℕ → ℝ) (x : ℝ)
    (hL : ∀ i j, i < j → j ≤ m → L i < L j) :
    (∃ i < m, ∃ s ∈ Icc (0 : ℝ) 1, x = L i+s*(L (i+1)-L i)) ↔
      L 0 ≤ x ∧ x ≤ L m := by
  have hle (i j : ℕ) (hij : i ≤ j) (hj : j ≤ m) : L i ≤ L j := by
    rcases eq_or_lt_of_le hij with h | h
    · rw [h]
    · exact (hL i j h hj).le
  constructor
  · rintro ⟨i, hi, s, hs, rfl⟩
    have hp := hL i (i+1) (by omega) (by omega)
    have hl := hle 0 i (by omega) (by omega)
    have hr := hle (i+1) m (by omega) (by omega)
    constructor <;> nlinarith [hs.1, hs.2]
  · rintro ⟨hl, hr⟩
    obtain ⟨i, hi, hli, hri⟩ := finite_intervals_cover m hm L x hl hr
    have hp : 0 < L (i+1)-L i := sub_pos.mpr (hL i (i+1) (by omega) (by omega))
    refine ⟨i, hi, (x-L i)/(L (i+1)-L i),
      ⟨div_nonneg (sub_nonneg.mpr hli) hp.le, (div_le_one hp).mpr (by linarith)⟩, ?_⟩
    rw [div_mul_cancel₀ _ (ne_of_gt hp)]
    ring

lemma linear_chain_unique (m : ℕ) (L : ℕ → ℝ)
    (hL : ∀ i j, i < j → j ≤ m → L i < L j)
    (i j : ℕ) (hi : i < m) (hj : j < m) (s r : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1)
    (hx : L i + s*(L (i+1)-L i) = L j + r*(L (j+1)-L j)) :
    (i : ℝ)+s = (j : ℝ)+r := by
  wlog hij : i ≤ j generalizing i j s r
  · exact (this j i hj hi r s hr hs hx.symm (by omega)).symm
  rcases eq_or_lt_of_le hij with h | h
  · subst j
    have hp := hL i (i+1) (by omega) (by omega)
    have : s = r := by nlinarith
    rw [this]
  · have hpi := hL i (i+1) (by omega) (by omega)
    have hpj := hL j (j+1) (by omega) (by omega)
    have hle : L (i+1) ≤ L j := by
      rcases eq_or_lt_of_le (show i+1 ≤ j by omega) with heq | hlt
      · rw [heq]
      · exact (hL (i+1) j hlt (by omega)).le
    have hs' : s = 1 := by nlinarith [hs.2, mul_nonneg hr.1 (sub_nonneg.mpr hpj.le)]
    have hr' : r = 0 := by nlinarith [hr.1, mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hpi.le)]
    have heq : j = i+1 := by
      by_contra hn
      have := hL (i+1) j (by omega) (by omega)
      rw [hs', hr'] at hx
      linarith
    simp [heq, hs', hr']

/-- Glued-strip injectivity in forward coordinates. Closed-square tags are not
claimed injective: i+s=j+r permits precisely the intended shared endpoints. -/
theorem positioned_injective (m : ℕ) (B e d : ℕ → Plane) (a : ℕ → ℝ)
    (ha : ∀ i < m, 0 < a i)
    (he : ∀ i < m, 0 < e i 0)
    (hd : ∀ i < m, 0 < det (e i) (d i))
    (hB : ∀ i < m, B (i+1) = B i + e i)
    (hdstep : ∀ i < m, d (i+1) = d i + (a i - 1) • e i)
    (i j : ℕ) (hi : i < m) (hj : j < m) (s t r u : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hr : r ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1)
    (hp : panel (B i) (e i) (d i) (a i) s t = panel (B j) (e j) (d j) (a j) r u) :
    t = u ∧ (i : ℝ)+s = (j : ℝ)+r := by
  have htu := positioned_height_unique m B e d a ha he hd hB hdstep
    i j hi hj s t r u hs ht hr hu hp
  refine ⟨htu, ?_⟩
  subst u
  let L : ℕ → ℝ := fun k => B k 0 + t*d k 0
  have hstep (k : ℕ) (hk : k < m) :
      L (k+1)-L k = rho (a k) t * e k 0 := by
    dsimp [L]
    rw [hB k hk, hdstep k hk]
    simp [rho]
    ring
  have hpos (k : ℕ) (hk : k < m) : L k < L (k+1) := by
    have := hstep k hk
    have := mul_pos (rho_pos (ha k hk) ht) (he k hk)
    linarith
  have hL (k l : ℕ) (hkl : k < l) (hl : l ≤ m) : L k < L l := by
    have hle : k+1 ≤ l := hkl
    induction l, hle using Nat.le_induction with
    | base => exact hpos k (by omega)
    | succ l hkl ih => exact (ih (by omega) (by omega)).trans (hpos l (by omega))
  apply linear_chain_unique m L hL i j hi hj s r hs hr
  have hx := congrArg (fun p : Plane => p 0) hp
  simp only [panel, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hx
  rw [hstep i hi, hstep j hj]
  dsimp [L]
  nlinarith

def frame (α σ : ℝ) (v : Plane) : Plane :=
  WithLp.toLp 2 ![forward α v, σ*(-v 0 * Real.sin α + v 1 * Real.cos α)]

lemma frame_add (α σ : ℝ) (v w : Plane) : frame α σ (v+w) = frame α σ v + frame α σ w := by
  ext k; fin_cases k <;> simp [frame, forward] <;> ring

lemma frame_smul (α σ c : ℝ) (v : Plane) : frame α σ (c • v) = c • frame α σ v := by
  ext k; fin_cases k <;> simp [frame, forward] <;> ring

lemma frame_det (α σ : ℝ) (v w : Plane) : det (frame α σ v) (frame α σ w) = σ * det v w := by
  calc
    _ = σ * det v w * (Real.cos α ^ 2 + Real.sin α ^ 2) := by
      change (v 0 * Real.cos α + v 1 * Real.sin α) * (σ*(-w 0 * Real.sin α + w 1 * Real.cos α)) -
        (σ*(-v 0 * Real.sin α + v 1 * Real.cos α)) * (w 0 * Real.cos α + w 1 * Real.sin α) =
        σ * (v 0*w 1-v 1*w 0) * (Real.cos α ^ 2 + Real.sin α ^ 2)
      ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq]; ring

/-- These coordinates are rigid, not an arbitrary positive linear projection. -/
lemma frame_norm_sq (α σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (v : Plane) :
    ‖frame α σ v‖^2 = ‖v‖^2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  have htrig := Real.cos_sq_add_sin_sq α
  rcases hσ with rfl | rfl <;>
    simp [frame, forward, inner, Fin.sum_univ_two] <;>
    nlinarith [congrArg (fun z : ℝ => v 0 ^ 2 * z) htrig,
      congrArg (fun z : ℝ => v 1 ^ 2 * z) htrig]

lemma frame_panel (α σ : ℝ) (B e d : Plane) (a s t : ℝ) :
    frame α σ (panel B e d a s t) =
      panel (frame α σ B) (frame α σ e) (frame α σ d) a s t := by
  simp [panel, frame_add, frame_smul]

/-- Both signs of coherent orientation are supported with ONE transverse flip.
The common forward direction is derived, not assumed. -/
theorem small_variation_injective (n : ℕ) (B e d : ℕ → Plane) (a θ length : ℕ → ℝ)
    (ha : ∀ i ≤ n, 0 < a i)
    (hlen : ∀ i ≤ n, 0 < length i)
    (hrep : ∀ i ≤ n, e i = length i • direction (θ i))
    (horient : (∀ i ≤ n, 0 < det (e i) (d i)) ∨ (∀ i ≤ n, det (e i) (d i) < 0))
    (hB : ∀ i ≤ n, B (i+1) = B i + e i)
    (hdstep : ∀ i ≤ n, d (i+1) = d i + (a i - 1) • e i)
    (hP : posVariation θ n < Real.pi)
    (hN : posVariation (fun k => -θ k) n < Real.pi)
    (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) (s t r u : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hr : r ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1)
    (hp : panel (B i) (e i) (d i) (a i) s t = panel (B j) (e j) (d j) (a j) r u) :
    t = u ∧ (i : ℝ)+s = (j : ℝ)+r := by
  obtain ⟨α, hα⟩ := exists_forward_of_variations n θ (fun k => e k) (fun k => length k)
    (fun k => hlen k (by omega)) (fun k => hrep k (by omega)) hP hN
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, ∀ k ≤ n, 0 < σ * det (e k) (d k) := by
    rcases horient with h | h
    · exact ⟨1, by simpa using h⟩
    · refine ⟨-1, fun k hk => ?_⟩
      have := h k hk
      linarith
  apply positioned_injective (n+1) (fun k => frame α σ (B k))
    (fun k => frame α σ (e k)) (fun k => frame α σ (d k)) a
    (fun k hk => ha k (by omega))
    (fun k hk => hα ⟨k, hk⟩)
    (by intro k hk; rw [frame_det]; exact hσ k (by omega))
    (by intro k hk; rw [hB k (by omega), frame_add])
    (by intro k hk; rw [hdstep k (by omega), frame_add, frame_smul])
    i j (by omega) (by omega) s t r u hs ht hr hu
  rw [← frame_panel, ← frame_panel, hp]

def hull (B e d : Plane) (a : ℝ) : Set Plane :=
  convexHull ℝ {B, B+e, B+d+a • e, B+d}

def scalarAffine (c0 c1 c : ℝ) : Plane →ᵃ[ℝ] ℝ where
  toFun p := c0*p 0 + c1*p 1 + c
  linear := {
    toFun p := c0*p 0+c1*p 1
    map_add' := by intros; simp; ring
    map_smul' := by intros; simp; ring }
  map_vadd' := by intros; simp; ring

def tCoord (B e d : Plane) : Plane →ᵃ[ℝ] ℝ :=
  scalarAffine (-e 1 / det e d) (e 0 / det e d)
    ((e 1*B 0-e 0*B 1)/det e d)

def zCoord (B e d : Plane) : Plane →ᵃ[ℝ] ℝ :=
  scalarAffine (d 1 / det e d) (-d 0 / det e d)
    ((d 0*B 1-d 1*B 0)/det e d)

lemma tCoord_apply (B e d p : Plane) : tCoord B e d p = det e (p-B)/det e d := by
  simp [tCoord, scalarAffine, det]; ring

lemma zCoord_apply (B e d p : Plane) : zCoord B e d p = det (p-B) d/det e d := by
  simp [zCoord, scalarAffine, det]; ring

lemma coords_linear (B e d : Plane) (hdet : det e d ≠ 0) (t z : ℝ) :
    tCoord B e d (B+t • d+z • e) = t ∧ zCoord B e d (B+t • d+z • e) = z := by
  rw [tCoord_apply, zCoord_apply]
  constructor <;> apply (div_eq_iff hdet).mpr <;> simp [det] <;> ring

lemma coords_reconstruct (B e d p : Plane) (hdet : det e d ≠ 0) :
    p = B + tCoord B e d p • d + zCoord B e d p • e := by
  rw [tCoord_apply, zCoord_apply]
  ext k; fin_cases k <;> simp [det] <;>
    field_simp [show e 0*d 1-e 1*d 0 ≠ 0 from hdet] <;> ring

lemma panel_mem_hull (B e d : Plane) (a s t : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    panel B e d a s t ∈ hull B e d a := by
  have hb : B ∈ hull B e d a := subset_convexHull ℝ _ (by simp)
  have he : B+e ∈ hull B e d a := subset_convexHull ℝ _ (by simp)
  have hd : B+d ∈ hull B e d a := subset_convexHull ℝ _ (by simp)
  have ha : B+d+a • e ∈ hull B e d a := subset_convexHull ℝ _ (by simp)
  have hc := convex_convexHull ℝ {B, B+e, B+d+a • e, B+d}
  have hlow := hc hb he (sub_nonneg.mpr hs.2) hs.1 (by ring : (1-s)+s=1)
  have hupp := hc hd ha (sub_nonneg.mpr hs.2) hs.1 (by ring : (1-s)+s=1)
  have hmid := hc hlow hupp (sub_nonneg.mpr ht.2) ht.1 (by ring : (1-t)+t=1)
  have heq : panel B e d a s t = (1-t) • ((1-s) • B+s • (B+e)) +
      t • ((1-s) • (B+d)+s • (B+d+a • e)) := by
    ext k
    simp [panel, rho]
    ring
  rw [heq]
  exact hmid

/-- A nonconstant affine supporting inequality is strict in the planar interior. -/
lemma support_strict (f : Plane →ᵃ[ℝ] ℝ) (hf : Continuous f)
    (hsurj : Function.Surjective f) (K : Set Plane)
    (hK : ∀ p ∈ K, 0 ≤ f p) {p : Plane} (hp : p ∈ interior K) : 0 < f p := by
  have hsub : f '' interior K ⊆ Ici (0 : ℝ) := by
    rintro y ⟨q, hq, rfl⟩
    exact hK q (interior_subset hq)
  have hopen := f.isOpenMap hf hsurj
  have hh := interior_maximal hsub (hopen (interior K) isOpen_interior)
  have := hh (show f p ∈ f '' interior K from ⟨p, hp, rfl⟩)
  simpa only [interior_Ici, mem_Ioi] using this

/-- Four affine supports of the actual convex hull. -/
lemma hull_supports (B e d : Plane) (a : ℝ) (ha : 0 < a) (hdet : det e d ≠ 0)
    {p : Plane} (hp : p ∈ hull B e d a) :
    0 ≤ tCoord B e d p ∧ tCoord B e d p ≤ 1 ∧
    0 ≤ zCoord B e d p ∧ zCoord B e d p ≤ rho a (tCoord B e d p) := by
  let T := tCoord B e d
  let Z := zCoord B e d
  have hcoords : T B = 0 ∧ Z B = 0 ∧ T (B+e) = 0 ∧ Z (B+e) = 1 ∧
      T (B+d+a • e) = 1 ∧ Z (B+d+a • e) = a ∧ T (B+d) = 1 ∧ Z (B+d) = 0 := by
    have h00 := coords_linear B e d hdet 0 0
    have h01 := coords_linear B e d hdet 0 1
    have h1a := coords_linear B e d hdet 1 a
    have h10 := coords_linear B e d hdet 1 0
    simp only [zero_smul, one_smul, add_zero] at h00 h01 h1a h10
    exact ⟨h00.1, h00.2, h01.1, h01.2, h1a.1, h1a.2, h10.1, h10.2⟩
  have supp (f : Plane →ᵃ[ℝ] ℝ)
      (hv : ∀ q ∈ ({B, B+e, B+d+a • e, B+d} : Set Plane), 0 ≤ f q) : 0 ≤ f p :=
    convexHull_min hv ((convex_Ici (0 : ℝ)).affine_preimage f) hp
  have hT := supp T (by
    intro q hq
    simp only [mem_insert_iff, mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> simp_all)
  have h1T := supp (AffineMap.const ℝ Plane (1 : ℝ) - T) (by
    intro q hq; simp only [mem_insert_iff, mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> simp_all)
  have hZ := supp Z (by
    intro q hq
    simp only [mem_insert_iff, mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> simp_all [le_of_lt ha])
  have hR := supp (AffineMap.const ℝ Plane (1 : ℝ) + (a-1) • T - Z) (by
    intro q hq; simp only [mem_insert_iff, mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> simp_all <;> linarith)
  change 0 ≤ 1 - T p at h1T
  change 0 ≤ 1+(a-1)*T p-Z p at hR
  change 0 ≤ T p ∧ T p ≤ 1 ∧ 0 ≤ Z p ∧ Z p ≤ rho a (T p)
  unfold rho
  exact ⟨hT, by linarith, hZ, by linarith⟩

/-- Exact closed-image equality with the four-vertex hull, not an assumed image identity. -/
theorem hull_eq_panel_image (B e d : Plane) (a : ℝ) (ha : 0 < a) (hdet : det e d ≠ 0) :
    hull B e d a = {p | ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, panel B e d a s t = p} := by
  ext p
  constructor
  · intro hp
    obtain ⟨ht0, ht1, hz0, hz1⟩ := hull_supports B e d a ha hdet hp
    have hρ := rho_pos ha ⟨ht0, ht1⟩
    refine ⟨zCoord B e d p / rho a (tCoord B e d p),
      ⟨div_nonneg hz0 hρ.le, (div_le_one hρ).mpr hz1⟩,
      tCoord B e d p, ⟨ht0, ht1⟩, ?_⟩
    unfold panel
    rw [div_mul_cancel₀ _ (ne_of_gt hρ)]
    exact (coords_reconstruct B e d p hdet).symm
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact panel_mem_hull B e d a s t hs ht

/-- Interior points have strict local square coordinates. This conclusion is
about the planar interior of the actual convex hull. -/
theorem hull_interior_parameters (B e d : Plane) (a : ℝ) (ha : 0 < a) (hdet : det e d ≠ 0)
    {p : Plane} (hp : p ∈ interior (hull B e d a)) :
    ∃ s ∈ Ioo (0 : ℝ) 1, ∃ t ∈ Ioo (0 : ℝ) 1, panel B e d a s t = p := by
  let T := tCoord B e d
  let Z := zCoord B e d
  have h00 := coords_linear B e d hdet 0 0
  have h01 := coords_linear B e d hdet 0 1
  have h10 := coords_linear B e d hdet 1 0
  simp only [zero_smul, one_smul, add_zero] at h00 h01 h10
  have hTc : Continuous T := by dsimp [T, tCoord, scalarAffine]; fun_prop
  have hZc : Continuous Z := by dsimp [Z, zCoord, scalarAffine]; fun_prop
  have hTs : Function.Surjective T :=
    FiniteWitnessClosure.height_surjective_of_endpoints T h00.1 h10.1
  have hZs : Function.Surjective Z :=
    FiniteWitnessClosure.height_surjective_of_endpoints Z h00.2 h01.2
  have hTb (q) (hq : q ∈ hull B e d a) := hull_supports B e d a ha hdet hq
  have ht := FiniteWitnessClosure.interior_height_strict T hTc hTs
    (fun q hq => ⟨(hTb q hq).1, (hTb q hq).2.1⟩) hp
  have hz := support_strict Z hZc hZs (hull B e d a) (fun q hq => (hTb q hq).2.2.1) hp
  let R : Plane →ᵃ[ℝ] ℝ := AffineMap.const ℝ Plane (1 : ℝ) + (a-1) • T - Z
  have hRc : Continuous R := by change Continuous (fun q => 1+(a-1)*T q-Z q); fun_prop
  have hRs : Function.Surjective R :=
    FiniteWitnessClosure.height_surjective_of_endpoints R
      (by change 1+(a-1)*T (B+e)-Z (B+e)=0; rw [h01.1, h01.2]; ring)
      (by change 1+(a-1)*T B-Z B=1; rw [h00.1, h00.2]; ring)
  have hR := support_strict R hRc hRs (hull B e d a) (by
    intro q hq
    have h := (hTb q hq).2.2.2
    change 0 ≤ 1+(a-1)*T q-Z q
    change Z q ≤ rho a (T q) at h
    unfold rho at h
    linarith) hp
  change 0 < 1+(a-1)*T p-Z p at hR
  have hρ := rho_pos ha ⟨ht.1.le, ht.2.le⟩
  have hzr : Z p < rho a (T p) := by unfold rho; linarith
  refine ⟨Z p/rho a (T p), ⟨div_pos hz hρ, (div_lt_one hρ).mpr hzr⟩,
    T p, ht, ?_⟩
  unfold panel
  rw [div_mul_cancel₀ _ (ne_of_gt hρ)]
  exact (coords_reconstruct B e d p hdet).symm

/-- The actual hull-interior consequence of the small-variation theorem. -/
theorem small_variation_nonoverlap (n : ℕ) (B e d : ℕ → Plane) (a θ length : ℕ → ℝ)
    (ha : ∀ i ≤ n, 0 < a i)
    (hlen : ∀ i ≤ n, 0 < length i)
    (hrep : ∀ i ≤ n, e i = length i • direction (θ i))
    (horient : (∀ i ≤ n, 0 < det (e i) (d i)) ∨ (∀ i ≤ n, det (e i) (d i) < 0))
    (hB : ∀ i ≤ n, B (i+1) = B i + e i)
    (hdstep : ∀ i ≤ n, d (i+1) = d i + (a i - 1) • e i)
    (hP : posVariation θ n < Real.pi)
    (hN : posVariation (fun k => -θ k) n < Real.pi)
    (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) (hij : i ≠ j) :
    Disjoint (interior (hull (B i) (e i) (d i) (a i)))
      (interior (hull (B j) (e j) (d j) (a j))) := by
  have hd (k : ℕ) (hk : k ≤ n) : det (e k) (d k) ≠ 0 := by
    rcases horient with h | h
    · exact ne_of_gt (h k hk)
    · exact ne_of_lt (h k hk)
  apply Set.disjoint_left.mpr
  intro p hpi hpj
  obtain ⟨s, hs, t, ht, hst⟩ := hull_interior_parameters _ _ _ _ (ha i hi) (hd i hi) hpi
  obtain ⟨r, hr, u, hu, hru⟩ := hull_interior_parameters _ _ _ _ (ha j hj) (hd j hj) hpj
  have heq := (small_variation_injective n B e d a θ length ha hlen hrep horient hB hdstep hP hN
    i j hi hj s t r u ⟨hs.1.le, hs.2.le⟩ ⟨ht.1.le, ht.2.le⟩
    ⟨hr.1.le, hr.2.le⟩ ⟨hu.1.le, hu.2.le⟩ (hst.trans hru.symm)).2
  rcases lt_or_gt_of_ne hij with h | h
  · have hh : (i : ℝ)+1 ≤ j := by exact_mod_cast h
    linarith [hs.1, hs.2, hr.1, hr.2]
  · have hh : (j : ℝ)+1 ≤ i := by exact_mod_cast h
    linarith [hs.1, hs.2, hr.1, hr.2]

/-- The reverse interior implication, useful for exact overlap negative controls. -/
theorem strict_parameters_interior (B e d : Plane) (a : ℝ) (ha : 0 < a) (hdet : det e d ≠ 0)
    (s t : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    panel B e d a s t ∈ interior (hull B e d a) := by
  let T := tCoord B e d
  let Z := zCoord B e d
  let O : Set Plane := {p | 0 < T p ∧ T p < 1 ∧ 0 < Z p ∧ Z p < rho a (T p)}
  have hTc : Continuous T := by dsimp [T, tCoord, scalarAffine]; fun_prop
  have hZc : Continuous Z := by dsimp [Z, zCoord, scalarAffine]; fun_prop
  have ho : IsOpen O := by
    exact (isOpen_lt continuous_const hTc).inter
      ((isOpen_lt hTc continuous_const).inter
        ((isOpen_lt continuous_const hZc).inter (isOpen_lt hZc (by unfold rho; fun_prop))))
  have hsub : O ⊆ hull B e d a := by
    intro p hp
    rcases hp with ⟨ht0, ht1, hz0, hz1⟩
    have hρ := rho_pos ha ⟨ht0.le, ht1.le⟩
    rw [hull_eq_panel_image B e d a ha hdet]
    refine ⟨Z p/rho a (T p), ⟨(div_pos hz0 hρ).le, ((div_lt_one hρ).mpr hz1).le⟩,
      T p, ⟨ht0.le, ht1.le⟩, ?_⟩
    unfold panel
    rw [div_mul_cancel₀ _ (ne_of_gt hρ)]
    exact (coords_reconstruct B e d p hdet).symm
  apply interior_maximal hsub ho
  have hc := coords_linear B e d hdet t (s*rho a t)
  change T (panel B e d a s t) = t ∧ Z (panel B e d a s t) = s*rho a t at hc
  change 0 < T _ ∧ T _ < 1 ∧ 0 < Z _ ∧ Z _ < rho a (T _)
  rw [hc.1, hc.2]
  have hρ := rho_pos ha ⟨ht.1.le, ht.2.le⟩
  exact ⟨ht.1, ht.2, mul_pos hs.1 hρ, by nlinarith [hs.2]⟩

def positiveBudget {n : ℕ} (q : Fin (n+1) → ℝ) : ℝ := ∑ k, max (q k) 0

def negativeBudget {n : ℕ} (q : Fin (n+1) → ℝ) : ℝ := ∑ k, max (-q k) 0

/-- The cyclic sum removes index k exactly once; internal steps start at k+1. -/
lemma cyclic_omission (n : ℕ) (f : Fin (n+1) → ℝ) (k : Fin (n+1)) :
    (∑ i : Fin n, f (k+i.succ)) = (∑ j, f j) - f k := by
  have hperm : (∑ i : Fin (n+1), f (k+i)) = ∑ j, f j := by
    exact Equiv.sum_comp (Equiv.addLeft k) f
  rw [Fin.sum_univ_succ] at hperm
  simp only [add_zero] at hperm
  linarith

/-- No global geometric conclusion or forward direction occurs in this record.
The same q and physical cyclic traversal are used for every cut. -/
structure DevelopedFamily (n : ℕ) where
  q : Fin (n+1) → ℝ
  B : Fin (n+1) → ℕ → Plane
  e : Fin (n+1) → ℕ → Plane
  d : Fin (n+1) → ℕ → Plane
  ratio : Fin (n+1) → ℕ → ℝ
  heading : Fin (n+1) → ℕ → ℝ
  length : Fin (n+1) → ℕ → ℝ
  ratio_pos : ∀ k i, i ≤ n → 0 < ratio k i
  length_pos : ∀ k i, i ≤ n → 0 < length k i
  represents : ∀ k i, i ≤ n → e k i = length k i • direction (heading k i)
  orientation : ∀ k, (∀ i ≤ n, 0 < det (e k i) (d k i)) ∨
    (∀ i ≤ n, det (e k i) (d k i) < 0)
  lower_step : ∀ k i, i ≤ n → B k (i+1) = B k i + e k i
  hinge_step : ∀ k i, i ≤ n → d k (i+1) = d k i + (ratio k i-1) • e k i
  internal_step : ∀ k (i : Fin n), heading k (i+1)-heading k i = q (k+i.succ)
  total_variation : positiveBudget q + negativeBudget q < 2*Real.pi

def DevelopedFamily.face {n : ℕ} (D : DevelopedFamily n) (k i : Fin (n+1)) : Set Plane :=
  hull (D.B k i) (D.e k i) (D.d k i) (D.ratio k i)

lemma retained_variations {n : ℕ} (D : DevelopedFamily n) (k : Fin (n+1)) :
    posVariation (D.heading k) n = positiveBudget D.q - max (D.q k) 0 ∧
    posVariation (fun i => -D.heading k i) n = negativeBudget D.q - max (-D.q k) 0 := by
  have hP : posVariation (D.heading k) n = ∑ i : Fin n, max (D.q (k+i.succ)) 0 := by
    unfold posVariation
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [D.internal_step k i]
  have hN : posVariation (fun i => -D.heading k i) n = ∑ i : Fin n, max (-D.q (k+i.succ)) 0 := by
    unfold posVariation
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    dsimp
    rw [show -D.heading k (↑i+1) - -D.heading k i = -(D.heading k (↑i+1)-D.heading k i) by ring,
      D.internal_step k i]
  rw [hP, hN]
  exact ⟨cyclic_omission n (fun j => max (D.q j) 0) k,
    cyclic_omission n (fun j => max (-D.q j) 0) k⟩

/-- Actual positioned hulls, not an angular proxy for nonoverlap. -/
theorem mixed_family_safe_cut {n : ℕ} (D : DevelopedFamily n)
    (hneg : ∃ k, D.q k-(positiveBudget D.q-negativeBudget D.q) ≤ 0)
    (hpos : ∃ k, 0 ≤ D.q k-(positiveBudget D.q-negativeBudget D.q)) :
    ∃ k : Fin (n+1), ∀ i j : Fin (n+1), i ≠ j →
      Disjoint (interior (D.face k i)) (interior (D.face k j)) := by
  obtain ⟨k, hP, hN⟩ := mixed_budget_selection D.q _ _ _ D.total_variation hneg hpos
  obtain ⟨hp, hn⟩ := retained_variations D k
  refine ⟨k, fun i j hij => ?_⟩
  apply small_variation_nonoverlap n (D.B k) (D.e k) (D.d k) (D.ratio k) (D.heading k) (D.length k)
    (D.ratio_pos k) (D.length_pos k) (D.represents k) (D.orientation k)
    (D.lower_step k) (D.hinge_step k) (by linarith) (by linarith)
    i j (by omega) (by omega)
  exact fun heq => hij (Fin.ext heq)

/-- Adapter to the unchanged downstream Safe predicate, using only local image
identities for supplied affine-isometric maps. Safety is derived above. -/
theorem mixed_family_safe_adapter {n : ℕ} (D : DevelopedFamily n)
    {E : Fin (n+1) → Fin (n+1) → Type*}
    [∀ k i, NormedAddCommGroup (E k i)] [∀ k i, InnerProductSpace ℝ (E k i)]
    [∀ k i, FiniteDimensional ℝ (E k i)]
    (F : (k i : Fin (n+1)) → Set (E k i))
    (U : (k i : Fin (n+1)) → E k i →ᵃⁱ[ℝ] Plane)
    (himage : ∀ k i, U k i '' F k i = D.face k i)
    (hneg : ∃ k, D.q k-(positiveBudget D.q-negativeBudget D.q) ≤ 0)
    (hpos : ∃ k, 0 ≤ D.q k-(positiveBudget D.q-negativeBudget D.q)) :
    ∃ k, FiniteWitnessClosure.Safe (F k) (fun i => U k i) := by
  obtain ⟨k, hk⟩ := mixed_family_safe_cut D hneg hpos
  refine ⟨k, fun i j hij => ?_⟩
  change Disjoint (interior (U k i '' F k i)) (interior (U k j '' F k j))
  rw [himage, himage]
  exact hk i j hij

end
end MixedTurnSafeCut

#print axioms MixedTurnSafeCut.panel_injective
#print axioms MixedTurnSafeCut.trace_identity
#print axioms MixedTurnSafeCut.eligible_convex
#print axioms MixedTurnSafeCut.mixed_budget_selection
#print axioms MixedTurnSafeCut.zero_cut_budgets
#print axioms MixedTurnSafeCut.finite_trace_comparison
#print axioms MixedTurnSafeCut.positioned_injective
#print axioms MixedTurnSafeCut.exists_forward_of_variations
#print axioms MixedTurnSafeCut.small_variation_injective
#print axioms MixedTurnSafeCut.hull_eq_panel_image
#print axioms MixedTurnSafeCut.hull_interior_parameters
#print axioms MixedTurnSafeCut.strict_parameters_interior
#print axioms MixedTurnSafeCut.small_variation_nonoverlap
#print axioms MixedTurnSafeCut.cyclic_omission
#print axioms MixedTurnSafeCut.retained_variations
#print axioms MixedTurnSafeCut.mixed_family_safe_cut
#print axioms MixedTurnSafeCut.mixed_family_safe_adapter
