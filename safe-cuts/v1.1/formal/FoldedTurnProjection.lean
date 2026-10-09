import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Set
open scoped BigOperators Classical

namespace FoldedTurnProjection
noncomputable section

/-- A linearly indexed presentation of one complete cyclic turnValue.  There are
`n+1` source intervals and weighted nodes, and therefore `n+2` endpoint knots.
The last interval is the virtual closing turnValue. -/
structure Chain (n : ℕ) where
  gap : Fin (n + 1) → ℝ
  turnValue : Fin (n + 1) → ℝ
  weight : Fin (n + 1) → ℝ
  sourcePos : Fin (n + 2) → ℝ
  heading : Fin (n + 2) → ℝ
  gap_pos : ∀ i, 0 < gap i
  turnValue_strict : ∀ i, |turnValue i| < gap i
  source_zero : sourcePos 0 = 0
  heading_zero : heading 0 = 0
  source_step : ∀ i : Fin (n + 1),
    sourcePos i.succ - sourcePos i.castSucc = gap i
  heading_step : ∀ i : Fin (n + 1),
    heading i.succ - heading i.castSucc = turnValue i
  source_last : sourcePos (Fin.last (n + 1)) = 2 * Real.pi
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum_pos : 0 < ∑ i, weight i
  closure_cos :
    (∑ i, weight i * Real.cos (sourcePos i.castSucc)) = 0
  closure_sin :
    (∑ i, weight i * Real.sin (sourcePos i.castSucc)) = 0

noncomputable def Chain.delta {n : ℕ} (C : Chain n) : ℝ :=
  C.heading (Fin.last (n + 1))

/-- Circular distance on the chosen `[0,2π]` representative interval. -/
def circularDist (s t : ℝ) : ℝ := min |s - t| (2 * Real.pi - |s - t|)

private lemma sum_fin_steps {n : ℕ} (f : Fin (n + 2) → ℝ) :
    (∑ i : Fin (n + 1),
      (fun j : Fin (n + 1) => f j.succ - f j.castSucc) i) =
      f (Fin.last (n + 1)) - f 0 := by
  let g : ℕ → ℝ := fun i => if hi : i < n + 2 then f ⟨i, hi⟩ else 0
  have ht := Finset.sum_range_sub g (n + 1)
  calc
    _ = ∑ i : Fin (n + 1),
        (fun j : Fin (n + 1) => g (j.val + 1) - g j.val) i := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [g]
      rw [dif_pos (by omega), dif_pos (by omega)]
      congr 1 <;> apply Fin.ext <;> rfl
    _ = ∑ i ∈ Finset.range (n + 1), (g (i + 1) - g i) :=
      Fin.sum_univ_eq_sum_range (fun i => g (i + 1) - g i) (n + 1)
    _ = g (n + 1) - g 0 := ht
    _ = _ := by
      dsimp [g]
      rw [dif_pos (by omega)]
      congr 1

lemma Chain.sum_gap_eq_two_pi {n : ℕ} (C : Chain n) :
    (∑ i, C.gap i) = 2 * Real.pi := by
  calc
    (∑ i, C.gap i) = ∑ i,
        (fun j : Fin (n + 1) =>
          C.sourcePos j.succ - C.sourcePos j.castSucc) i := by
      apply Finset.sum_congr rfl
      intro i _
      exact (C.source_step i).symm
    _ = C.sourcePos (Fin.last (n + 1)) - C.sourcePos 0 :=
      sum_fin_steps C.sourcePos
    _ = 2 * Real.pi := by rw [C.source_last, C.source_zero, sub_zero]

lemma Chain.sourcePos_strictMono {n : ℕ} (C : Chain n) :
    StrictMono C.sourcePos := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  have hs := C.source_step i
  have hg := C.gap_pos i
  linarith

lemma Chain.heading_contracts_between_knots {n : ℕ} (C : Chain n)
    (i j : Fin (n + 2)) (hij : i < j) :
    |C.heading j - C.heading i| < C.sourcePos j - C.sourcePos i := by
  induction j using Fin.induction with
  | zero => exact (Fin.not_lt_zero i hij).elim
  | succ j ih =>
      have hle : i ≤ j.castSucc := by
        apply Fin.le_iff_val_le_val.mpr
        have hv : i.val < j.succ.val := Fin.lt_iff_val_lt_val.mp hij
        exact Nat.le_of_lt_succ hv
      rcases hle.eq_or_lt with heq | hlt
      · subst i
        simpa only [C.heading_step j, C.source_step j] using
          C.turnValue_strict j
      · have hprev := ih hlt
        have htri : |C.heading j.succ - C.heading i| ≤
            |C.heading j.succ - C.heading j.castSucc| +
              |C.heading j.castSucc - C.heading i| := by
          exact abs_sub_le _ _ _
        have hstep : |C.heading j.succ - C.heading j.castSucc| < C.gap j := by
          rw [C.heading_step j]
          exact C.turnValue_strict j
        calc
          |C.heading j.succ - C.heading i| ≤
              |C.heading j.succ - C.heading j.castSucc| +
                |C.heading j.castSucc - C.heading i| := htri
          _ < C.gap j + (C.sourcePos j.castSucc - C.sourcePos i) :=
            add_lt_add hstep hprev
          _ = C.sourcePos j.succ - C.sourcePos i := by
            rw [← C.source_step j]
            ring

lemma Chain.heading_contracts_between_knots_le {n : ℕ} (C : Chain n)
    (i j : Fin (n + 2)) (hij : i ≤ j) :
    |C.heading j - C.heading i| ≤ C.sourcePos j - C.sourcePos i := by
  rcases hij.eq_or_lt with heq | hlt
  · subst i
    simp
  · exact (C.heading_contracts_between_knots i j hlt).le

private lemma abs_affine_sub_le {a b z da db t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ha : |a - z| ≤ da) (hb : |b - z| ≤ db) :
    |(1 - t) * a + t * b - z| ≤ (1 - t) * da + t * db := by
  have hdecomp : (1 - t) * a + t * b - z =
      (1 - t) * (a - z) + t * (b - z) := by ring
  rw [hdecomp]
  calc
    |(1 - t) * (a - z) + t * (b - z)| ≤
        |(1 - t) * (a - z)| + |t * (b - z)| := abs_add_le _ _
    _ = (1 - t) * |a - z| + t * |b - z| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.2),
        abs_of_nonneg ht.1]
    _ ≤ (1 - t) * da + t * db := by
      have hla := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha)
      have hlb := mul_nonneg ht.1 (sub_nonneg.mpr hb)
      nlinarith

private lemma abs_affine_sub_lt_of_left {a b z da db t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (ht1 : t < 1)
    (ha : |a - z| < da) (hb : |b - z| ≤ db) :
    |(1 - t) * a + t * b - z| < (1 - t) * da + t * db := by
  refine lt_of_le_of_lt (abs_affine_sub_le ht le_rfl le_rfl) ?_
  have hla := mul_pos (sub_pos.mpr ht1) (sub_pos.mpr ha)
  have hlb := mul_nonneg ht.1 (sub_nonneg.mpr hb)
  nlinarith

private lemma abs_affine_sub_lt_of_right {a b z da db t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (ht0 : 0 < t)
    (ha : |a - z| ≤ da) (hb : |b - z| < db) :
    |(1 - t) * a + t * b - z| < (1 - t) * da + t * db := by
  refine lt_of_le_of_lt (abs_affine_sub_le ht le_rfl le_rfl) ?_
  have hla := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha)
  have hlb := mul_pos ht0 (sub_pos.mpr hb)
  nlinarith

lemma Chain.exists_half_delta_crossing {n : ℕ} (C : Chain n) :
    ∃ m : Fin (n + 1), ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧
      (1 - t) * C.heading m.castSucc + t * C.heading m.succ = C.delta / 2 := by
  let σ : ℝ := if 0 ≤ C.delta then 1 else -1
  let D : ℝ := |C.delta|
  let L : ℝ := D / 2
  have hσsq : σ * σ = 1 := by
    by_cases hd : 0 ≤ C.delta <;> simp [σ, hd]
  have hσδ : σ * C.delta = D := by
    by_cases hd : 0 ≤ C.delta
    · simp [σ, D, hd, abs_of_nonneg]
    · have hd' : C.delta < 0 := lt_of_not_ge hd
      simp [σ, D, hd, abs_of_neg hd']
  have hσD : σ * D = C.delta := by
    calc
      σ * D = σ * (σ * C.delta) := by rw [hσδ]
      _ = (σ * σ) * C.delta := by ring
      _ = C.delta := by rw [hσsq, one_mul]
  have hL0 : 0 ≤ L := div_nonneg (abs_nonneg _) (by norm_num)
  let P : ℕ → Prop := fun r =>
    ∃ hr : r < n + 2, L ≤ σ * C.heading ⟨r, hr⟩
  have hlast : P (n + 1) := by
    refine ⟨by omega, ?_⟩
    change L ≤ σ * C.delta
    rw [hσδ]
    dsimp [L, D]
    linarith [abs_nonneg C.delta]
  have hex : ∃ r, P r := ⟨n + 1, hlast⟩
  let r := Nat.find hex
  have hrP := Nat.find_spec hex
  rcases hrP with ⟨hrbound, hrlevel⟩
  by_cases hr0 : r = 0
  · let m : Fin (n + 1) := 0
    refine ⟨m, 0, by simp, ?_⟩
    have hzhead : C.heading (⟨r, hrbound⟩ : Fin (n + 2)) = 0 := by
      have hfin : (⟨r, hrbound⟩ : Fin (n + 2)) = 0 :=
        Fin.ext (by simp [hr0])
      rw [hfin, C.heading_zero]
    rw [hzhead] at hrlevel
    have hL : L = 0 := le_antisymm (by simpa using hrlevel) hL0
    have hD : D = 0 := by dsimp [L] at hL; linarith
    have hδ : C.delta = 0 := by rw [← hσD, hD, mul_zero]
    simp [m, C.heading_zero, hδ]
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    have hmBound : r - 1 < n + 1 := by omega
    let m : Fin (n + 1) := ⟨r - 1, hmBound⟩
    have hmCast : m.castSucc.val = r - 1 := rfl
    have hmSucc : m.succ.val = r := by dsimp [m]; omega
    have hprevNot : ¬P (r - 1) :=
      Nat.find_min hex (Nat.sub_lt hrpos Nat.zero_lt_one)
    have hprevBound : r - 1 < n + 2 := by omega
    have hprev : σ * C.heading m.castSucc < L := by
      have hnle : ¬ L ≤ σ * C.heading
          (⟨r - 1, hprevBound⟩ : Fin (n + 2)) := by
        intro hle
        exact hprevNot ⟨hprevBound, hle⟩
      have hfin : (⟨r - 1, hprevBound⟩ : Fin (n + 2)) = m.castSucc :=
        Fin.ext (by simp [m])
      rw [hfin] at hnle
      exact lt_of_not_ge hnle
    have hcurr : L ≤ σ * C.heading m.succ := by
      have hfin : (⟨r, hrbound⟩ : Fin (n + 2)) = m.succ :=
        Fin.ext (by simp [m]; omega)
      rw [← hfin]
      exact hrlevel
    let a := σ * C.heading m.castSucc
    let b := σ * C.heading m.succ
    let t := (L - a) / (b - a)
    have hab : 0 < b - a := by dsimp [a, b]; linarith
    have ht0 : 0 ≤ t := by
      dsimp [t]
      exact div_nonneg (by dsimp [a]; linarith) hab.le
    have ht1 : t ≤ 1 := by
      rw [show (1 : ℝ) = (b - a) / (b - a) by field_simp]
      exact div_le_div_of_nonneg_right (by dsimp [a, b]; linarith) hab.le
    have hinterp : (1 - t) * a + t * b = L := by
      dsimp [t]
      field_simp
      ring
    refine ⟨m, t, ⟨ht0, ht1⟩, ?_⟩
    have hσinterp : σ *
        ((1 - t) * C.heading m.castSucc + t * C.heading m.succ) = L := by
      calc
        _ = (1 - t) * a + t * b := by simp [a, b]; ring
        _ = L := hinterp
    have hscaled := congrArg (fun z : ℝ => σ * z) hσinterp
    rw [← mul_assoc, hσsq, one_mul] at hscaled
    calc
      (1 - t) * C.heading m.castSucc + t * C.heading m.succ = σ * L := hscaled
      _ = C.delta / 2 := by
        dsimp [L]
        rw [show σ * (D / 2) = (σ * D) / 2 by ring, hσD]

lemma Chain.crossing_direct_contract {n : ℕ} (C : Chain n)
    (m : Fin (n + 1)) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hmid : (1 - t) * C.heading m.castSucc + t * C.heading m.succ =
      C.delta / 2) (j : Fin (n + 1)) :
    |C.heading j.castSucc - C.delta / 2| ≤
      |C.sourcePos j.castSucc -
        ((1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ)| := by
  let α := (1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ
  rw [← hmid, abs_sub_comm]
  by_cases hj : j.castSucc ≤ m.castSucc
  · have ha := C.heading_contracts_between_knots_le j.castSucc m.castSucc hj
    have hjb : j.castSucc ≤ m.succ :=
      le_trans hj (Fin.le_iff_val_le_val.mpr (by simp))
    have hb := C.heading_contracts_between_knots_le j.castSucc m.succ hjb
    have h := abs_affine_sub_le ht ha hb
    have hsja : C.sourcePos j.castSucc ≤ α := by
      have hsm := C.sourcePos_strictMono.monotone hj
      have hms : C.sourcePos m.castSucc ≤ C.sourcePos m.succ :=
        C.sourcePos_strictMono.monotone (Fin.le_iff_val_le_val.mpr (by simp))
      have hp := mul_nonneg ht.1 (sub_nonneg.mpr hms)
      dsimp [α]
      nlinarith
    rw [abs_of_nonpos (sub_nonpos.mpr hsja)]
    dsimp [α]
    calc
      |(1 - t) * C.heading m.castSucc + t * C.heading m.succ -
          C.heading j.castSucc| ≤
        (1 - t) * (C.sourcePos m.castSucc - C.sourcePos j.castSucc) +
          t * (C.sourcePos m.succ - C.sourcePos j.castSucc) := h
      _ = - (C.sourcePos j.castSucc -
          ((1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ)) := by ring
  · have hmj : m.succ ≤ j.castSucc := by
      apply Fin.le_iff_val_le_val.mpr
      have hn := not_le.mp hj
      have hv := Fin.lt_iff_val_lt_val.mp hn
      simp at hv ⊢
      omega
    have hma : m.castSucc ≤ j.castSucc :=
      le_trans (Fin.le_iff_val_le_val.mpr (by simp)) hmj
    have ha0 := C.heading_contracts_between_knots_le m.castSucc j.castSucc hma
    have hb0 := C.heading_contracts_between_knots_le m.succ j.castSucc hmj
    have ha : |C.heading m.castSucc - C.heading j.castSucc| ≤
        C.sourcePos j.castSucc - C.sourcePos m.castSucc := by
      simpa [abs_sub_comm] using ha0
    have hb : |C.heading m.succ - C.heading j.castSucc| ≤
        C.sourcePos j.castSucc - C.sourcePos m.succ := by
      simpa [abs_sub_comm] using hb0
    have h := abs_affine_sub_le ht ha hb
    have hajs : α ≤ C.sourcePos j.castSucc := by
      have hms : C.sourcePos m.castSucc ≤ C.sourcePos m.succ :=
        C.sourcePos_strictMono.monotone (Fin.le_iff_val_le_val.mpr (by simp))
      have hsj := C.sourcePos_strictMono.monotone hmj
      have hp := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hms)
      dsimp [α]
      nlinarith
    rw [abs_of_nonneg (sub_nonneg.mpr hajs)]
    dsimp [α]
    calc
      |(1 - t) * C.heading m.castSucc + t * C.heading m.succ -
          C.heading j.castSucc| ≤
        (1 - t) * (C.sourcePos j.castSucc - C.sourcePos m.castSucc) +
          t * (C.sourcePos j.castSucc - C.sourcePos m.succ) := h
      _ = C.sourcePos j.castSucc -
          ((1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ) := by ring

lemma Chain.crossing_direct_contract_strict {n : ℕ} (C : Chain n)
    (m : Fin (n + 1)) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hmid : (1 - t) * C.heading m.castSucc + t * C.heading m.succ =
      C.delta / 2) (j : Fin (n + 1))
    (hne : C.sourcePos j.castSucc ≠
      (1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ) :
    |C.heading j.castSucc - C.delta / 2| <
      |C.sourcePos j.castSucc -
        ((1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ)| := by
  let α := (1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ
  rw [← hmid, abs_sub_comm]
  by_cases hj : j.castSucc ≤ m.castSucc
  · have ha := C.heading_contracts_between_knots_le j.castSucc m.castSucc hj
    have hjb : j.castSucc < m.succ :=
      lt_of_le_of_lt hj (Fin.lt_iff_val_lt_val.mpr (by simp))
    have hb := C.heading_contracts_between_knots j.castSucc m.succ hjb
    have hsja : C.sourcePos j.castSucc ≤ α := by
      have hsm := C.sourcePos_strictMono.monotone hj
      have hms : C.sourcePos m.castSucc ≤ C.sourcePos m.succ :=
        C.sourcePos_strictMono.monotone (Fin.le_iff_val_le_val.mpr (by simp))
      have hp := mul_nonneg ht.1 (sub_nonneg.mpr hms)
      dsimp [α]
      nlinarith
    have hstrict : |(1 - t) * C.heading m.castSucc + t * C.heading m.succ -
          C.heading j.castSucc| <
        (1 - t) * (C.sourcePos m.castSucc - C.sourcePos j.castSucc) +
          t * (C.sourcePos m.succ - C.sourcePos j.castSucc) := by
      by_cases ht0 : t = 0
      · have hji : j.castSucc < m.castSucc := by
          apply lt_of_le_of_ne hj
          intro heq
          apply hne
          rw [ht0]
          simp
          exact congrArg C.sourcePos heq
        have ha' := C.heading_contracts_between_knots j.castSucc m.castSucc hji
        exact abs_affine_sub_lt_of_left ht (by linarith) ha' hb.le
      · exact abs_affine_sub_lt_of_right ht (lt_of_le_of_ne ht.1 (Ne.symm ht0)) ha hb
    rw [abs_of_nonpos (sub_nonpos.mpr hsja)]
    dsimp [α]
    calc
      |(1 - t) * C.heading m.castSucc + t * C.heading m.succ -
          C.heading j.castSucc| <
        (1 - t) * (C.sourcePos m.castSucc - C.sourcePos j.castSucc) +
          t * (C.sourcePos m.succ - C.sourcePos j.castSucc) := hstrict
      _ = - (C.sourcePos j.castSucc -
          ((1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ)) := by ring
  · have hmj : m.succ ≤ j.castSucc := by
      apply Fin.le_iff_val_le_val.mpr
      have hn := not_le.mp hj
      have hv := Fin.lt_iff_val_lt_val.mp hn
      simp at hv ⊢
      omega
    have hma : m.castSucc < j.castSucc :=
      lt_of_lt_of_le (Fin.lt_iff_val_lt_val.mpr (by simp)) hmj
    have ha0 := C.heading_contracts_between_knots m.castSucc j.castSucc hma
    have hb0 := C.heading_contracts_between_knots_le m.succ j.castSucc hmj
    have ha : |C.heading m.castSucc - C.heading j.castSucc| <
        C.sourcePos j.castSucc - C.sourcePos m.castSucc := by
      simpa [abs_sub_comm] using ha0
    have hb : |C.heading m.succ - C.heading j.castSucc| ≤
        C.sourcePos j.castSucc - C.sourcePos m.succ := by
      simpa [abs_sub_comm] using hb0
    have hajs : α ≤ C.sourcePos j.castSucc := by
      have hms : C.sourcePos m.castSucc ≤ C.sourcePos m.succ :=
        C.sourcePos_strictMono.monotone (Fin.le_iff_val_le_val.mpr (by simp))
      have hsj := C.sourcePos_strictMono.monotone hmj
      have hp := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hms)
      dsimp [α]
      nlinarith
    have hstrict : |(1 - t) * C.heading m.castSucc + t * C.heading m.succ -
          C.heading j.castSucc| <
        (1 - t) * (C.sourcePos j.castSucc - C.sourcePos m.castSucc) +
          t * (C.sourcePos j.castSucc - C.sourcePos m.succ) := by
      by_cases ht1 : t = 1
      · have hsj : m.succ < j.castSucc := by
          apply lt_of_le_of_ne hmj
          intro heq
          apply hne
          rw [ht1]
          simp
          exact (congrArg C.sourcePos heq).symm
        have hb'0 := C.heading_contracts_between_knots m.succ j.castSucc hsj
        have hb' : |C.heading m.succ - C.heading j.castSucc| <
            C.sourcePos j.castSucc - C.sourcePos m.succ := by
          simpa [abs_sub_comm] using hb'0
        exact abs_affine_sub_lt_of_right ht (by linarith) ha.le hb'
      · exact abs_affine_sub_lt_of_left ht (lt_of_le_of_ne ht.2 ht1) ha hb
    rw [abs_of_nonneg (sub_nonneg.mpr hajs)]
    dsimp [α]
    calc
      |(1 - t) * C.heading m.castSucc + t * C.heading m.succ -
          C.heading j.castSucc| <
        (1 - t) * (C.sourcePos j.castSucc - C.sourcePos m.castSucc) +
          t * (C.sourcePos j.castSucc - C.sourcePos m.succ) := hstrict
      _ = C.sourcePos j.castSucc -
          ((1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ) := by ring

lemma Chain.sourcePos_mem_interval {n : ℕ} (C : Chain n)
    (j : Fin (n + 1)) :
    C.sourcePos j.castSucc ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
  have hm := C.sourcePos_strictMono.monotone
  constructor
  · rw [← C.source_zero]
    exact hm (Fin.zero_le _)
  · rw [← C.source_last]
    exact hm (Fin.le_last _)

lemma Chain.crossing_alpha_mem_interval {n : ℕ} (C : Chain n)
    (m : Fin (n + 1)) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ ∈
      Set.Icc (0 : ℝ) (2 * Real.pi) := by
  have hzero (i : Fin (n + 2)) : 0 ≤ C.sourcePos i := by
    calc
      0 = C.sourcePos 0 := C.source_zero.symm
      _ ≤ C.sourcePos i := C.sourcePos_strictMono.monotone (Fin.zero_le i)
  have hlast (i : Fin (n + 2)) : C.sourcePos i ≤ 2 * Real.pi := by
    calc
      C.sourcePos i ≤ C.sourcePos (Fin.last (n + 1)) :=
        C.sourcePos_strictMono.monotone (Fin.le_last i)
      _ = 2 * Real.pi := C.source_last
  have hm0 := hzero m.castSucc
  have hms0 := hzero m.succ
  have hm2 := hlast m.castSucc
  have hms2 := hlast m.succ
  constructor
  · have h1 := mul_nonneg (sub_nonneg.mpr ht.2) hm0
    have h2 := mul_nonneg ht.1 hms0
    linarith
  · have h1 := mul_nonneg (sub_nonneg.mpr ht.2)
      (sub_nonneg.mpr hm2)
    have h2 := mul_nonneg ht.1 (sub_nonneg.mpr hms2)
    nlinarith

lemma Chain.crossing_last_contract {n : ℕ} (C : Chain n)
    (m : Fin (n + 1)) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hmid : (1 - t) * C.heading m.castSucc + t * C.heading m.succ =
      C.delta / 2) :
    |C.delta - C.delta / 2| ≤
      2 * Real.pi -
        ((1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ) := by
  let last : Fin (n + 2) := Fin.last (n + 1)
  have hml : m.castSucc ≤ last := Fin.le_last _
  have hsl : m.succ ≤ last := Fin.le_last _
  have ha0 := C.heading_contracts_between_knots_le m.castSucc last hml
  have hb0 := C.heading_contracts_between_knots_le m.succ last hsl
  have ha : |C.heading m.castSucc - C.delta| ≤
      2 * Real.pi - C.sourcePos m.castSucc := by
    simpa [last, Chain.delta, C.source_last, abs_sub_comm] using ha0
  have hb : |C.heading m.succ - C.delta| ≤
      2 * Real.pi - C.sourcePos m.succ := by
    simpa [last, Chain.delta, C.source_last, abs_sub_comm] using hb0
  have h := abs_affine_sub_le ht ha hb
  rw [hmid] at h
  calc
    |C.delta - C.delta / 2| = |C.delta / 2 - C.delta| := abs_sub_comm _ _
    _ ≤ (1 - t) * (2 * Real.pi - C.sourcePos m.castSucc) +
        t * (2 * Real.pi - C.sourcePos m.succ) := h
    _ = 2 * Real.pi -
        ((1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ) := by ring

lemma Chain.crossing_last_contract_strict {n : ℕ} (C : Chain n)
    (m : Fin (n + 1)) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hmid : (1 - t) * C.heading m.castSucc + t * C.heading m.succ =
      C.delta / 2)
    (hne : (1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ ≠
      2 * Real.pi) :
    |C.delta - C.delta / 2| <
      2 * Real.pi -
        ((1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ) := by
  let last : Fin (n + 2) := Fin.last (n + 1)
  have hml : m.castSucc < last := Fin.castSucc_lt_last m
  have hsl : m.succ ≤ last := Fin.le_last _
  have ha0 := C.heading_contracts_between_knots m.castSucc last hml
  have hb0 := C.heading_contracts_between_knots_le m.succ last hsl
  have ha : |C.heading m.castSucc - C.delta| <
      2 * Real.pi - C.sourcePos m.castSucc := by
    simpa [last, Chain.delta, C.source_last, abs_sub_comm] using ha0
  have hb : |C.heading m.succ - C.delta| ≤
      2 * Real.pi - C.sourcePos m.succ := by
    simpa [last, Chain.delta, C.source_last, abs_sub_comm] using hb0
  have hstrict : |(1 - t) * C.heading m.castSucc + t * C.heading m.succ -
        C.delta| <
      (1 - t) * (2 * Real.pi - C.sourcePos m.castSucc) +
        t * (2 * Real.pi - C.sourcePos m.succ) := by
    by_cases ht1 : t = 1
    · have hsucc : m.succ < last := by
        apply lt_of_le_of_ne hsl
        intro heq
        apply hne
        rw [ht1]
        simp
        calc
          C.sourcePos m.succ = C.sourcePos last := congrArg C.sourcePos heq
          _ = 2 * Real.pi := C.source_last
      have hb'0 := C.heading_contracts_between_knots m.succ last hsucc
      have hb' : |C.heading m.succ - C.delta| <
          2 * Real.pi - C.sourcePos m.succ := by
        simpa [last, Chain.delta, C.source_last, abs_sub_comm] using hb'0
      exact abs_affine_sub_lt_of_right ht (by linarith) ha.le hb'
    · exact abs_affine_sub_lt_of_left ht (lt_of_le_of_ne ht.2 ht1) ha hb
  rw [hmid] at hstrict
  calc
    |C.delta - C.delta / 2| = |C.delta / 2 - C.delta| := abs_sub_comm _ _
    _ < (1 - t) * (2 * Real.pi - C.sourcePos m.castSucc) +
        t * (2 * Real.pi - C.sourcePos m.succ) := hstrict
    _ = 2 * Real.pi -
        ((1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ) := by ring

lemma Chain.crossing_complement_contract {n : ℕ} (C : Chain n)
    (m : Fin (n + 1)) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hmid : (1 - t) * C.heading m.castSucc + t * C.heading m.succ =
      C.delta / 2) (j : Fin (n + 1)) :
    |C.heading j.castSucc - C.delta / 2| ≤
      2 * Real.pi -
        |C.sourcePos j.castSucc -
          ((1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ)| := by
  let α := (1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ
  have hα := C.crossing_alpha_mem_interval m t ht
  by_cases hjα : C.sourcePos j.castSucc ≤ α
  · have hj0 := C.heading_contracts_between_knots_le
      (0 : Fin (n + 2)) j.castSucc (Fin.zero_le _)
    have hj0' : |C.heading j.castSucc| ≤ C.sourcePos j.castSucc := by
      simpa [C.heading_zero, C.source_zero, abs_sub_comm] using hj0
    have hlast := C.crossing_last_contract m t ht hmid
    have htri : |C.heading j.castSucc - C.delta / 2| ≤
        |C.heading j.castSucc| + |C.delta - C.delta / 2| := by
      have heq : C.heading j.castSucc - C.delta / 2 =
          C.heading j.castSucc - (C.delta - C.delta / 2) := by ring
      rw [heq]
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (C.heading j.castSucc) (-(C.delta - C.delta / 2))
    rw [abs_of_nonpos (sub_nonpos.mpr hjα)]
    dsimp [α] at hjα ⊢
    linarith
  · have hαj : α ≤ C.sourcePos j.castSucc := le_of_not_ge hjα
    let last : Fin (n + 2) := Fin.last (n + 1)
    have hjl := C.heading_contracts_between_knots_le j.castSucc last (Fin.le_last _)
    have hjl' : |C.delta - C.heading j.castSucc| ≤
        2 * Real.pi - C.sourcePos j.castSucc := by
      simpa [last, Chain.delta, C.source_last] using hjl
    have hzero := C.crossing_direct_contract m t ht hmid (0 : Fin (n + 1))
    have hzero' : |C.delta / 2| ≤ α := by
      calc
        |C.delta / 2| = |C.heading (0 : Fin (n + 2)) - C.delta / 2| := by
          rw [C.heading_zero, zero_sub, abs_neg]
        _ ≤ |C.sourcePos (0 : Fin (n + 2)) - α| := by
          exact hzero
        _ = α := by
          rw [C.source_zero, zero_sub, abs_neg, abs_of_nonneg hα.1]
    have htri : |C.heading j.castSucc - C.delta / 2| ≤
        |C.delta - C.heading j.castSucc| + |C.delta / 2| := by
      have heq : C.heading j.castSucc - C.delta / 2 =
          -(C.delta - C.heading j.castSucc) + C.delta / 2 := by ring
      rw [heq]
      exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    rw [abs_of_nonneg (sub_nonneg.mpr hαj)]
    dsimp [α] at hαj hzero' ⊢
    linarith

lemma Chain.crossing_complement_contract_strict {n : ℕ} (C : Chain n)
    (m : Fin (n + 1)) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hmid : (1 - t) * C.heading m.castSucc + t * C.heading m.succ =
      C.delta / 2) (j : Fin (n + 1))
    (hdir : Real.cos (C.sourcePos j.castSucc) ≠
        Real.cos ((1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ) ∨
      Real.sin (C.sourcePos j.castSucc) ≠
        Real.sin ((1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ)) :
    |C.heading j.castSucc - C.delta / 2| <
      2 * Real.pi -
        |C.sourcePos j.castSucc -
          ((1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ)| := by
  let α := (1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ
  have hα := C.crossing_alpha_mem_interval m t ht
  by_cases hjα : C.sourcePos j.castSucc ≤ α
  · have hj0le := C.heading_contracts_between_knots_le
      (0 : Fin (n + 2)) j.castSucc (Fin.zero_le _)
    have hj0le' : |C.heading j.castSucc| ≤ C.sourcePos j.castSucc := by
      simpa [C.heading_zero, C.source_zero, abs_sub_comm] using hj0le
    have hlastle := C.crossing_last_contract m t ht hmid
    have hsum : |C.heading j.castSucc| + |C.delta - C.delta / 2| <
        C.sourcePos j.castSucc + (2 * Real.pi - α) := by
      by_cases hj0 : j.castSucc = 0
      · have hαne : α ≠ 2 * Real.pi := by
          intro heq
          rcases hdir with hc | hs
          · apply hc
            rw [hj0, C.source_zero]
            dsimp [α] at heq
            rw [heq]
            simp
          · apply hs
            rw [hj0, C.source_zero]
            dsimp [α] at heq
            rw [heq]
            simp
        have hlast := C.crossing_last_contract_strict m t ht hmid (by
          simpa [α] using hαne)
        exact add_lt_add_of_le_of_lt hj0le' hlast
      · have hjpos : (0 : Fin (n + 2)) < j.castSucc :=
          lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hj0)
        have hj0s := C.heading_contracts_between_knots
          (0 : Fin (n + 2)) j.castSucc hjpos
        have hj0s' : |C.heading j.castSucc| < C.sourcePos j.castSucc := by
          simpa [C.heading_zero, C.source_zero, abs_sub_comm] using hj0s
        exact add_lt_add_of_lt_of_le hj0s' hlastle
    have htri : |C.heading j.castSucc - C.delta / 2| ≤
        |C.heading j.castSucc| + |C.delta - C.delta / 2| := by
      have heq : C.heading j.castSucc - C.delta / 2 =
          C.heading j.castSucc - (C.delta - C.delta / 2) := by ring
      rw [heq]
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (C.heading j.castSucc) (-(C.delta - C.delta / 2))
    rw [abs_of_nonpos (sub_nonpos.mpr hjα)]
    dsimp [α] at hjα hsum ⊢
    exact lt_of_le_of_lt htri (by linarith)
  · have hαj : α ≤ C.sourcePos j.castSucc := le_of_not_ge hjα
    let last : Fin (n + 2) := Fin.last (n + 1)
    have hjl := C.heading_contracts_between_knots j.castSucc last
      (Fin.castSucc_lt_last j)
    have hjl' : |C.delta - C.heading j.castSucc| <
        2 * Real.pi - C.sourcePos j.castSucc := by
      simpa [last, Chain.delta, C.source_last] using hjl
    have hzero := C.crossing_direct_contract m t ht hmid (0 : Fin (n + 1))
    have hzero' : |C.delta / 2| ≤ α := by
      calc
        |C.delta / 2| = |C.heading (0 : Fin (n + 2)) - C.delta / 2| := by
          rw [C.heading_zero, zero_sub, abs_neg]
        _ ≤ |C.sourcePos (0 : Fin (n + 2)) - α| := hzero
        _ = α := by
          rw [C.source_zero, zero_sub, abs_neg, abs_of_nonneg hα.1]
    have htri : |C.heading j.castSucc - C.delta / 2| ≤
        |C.delta - C.heading j.castSucc| + |C.delta / 2| := by
      have heq : C.heading j.castSucc - C.delta / 2 =
          -(C.delta - C.heading j.castSucc) + C.delta / 2 := by ring
      rw [heq]
      exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    rw [abs_of_nonneg (sub_nonneg.mpr hαj)]
    dsimp [α] at hαj hzero' ⊢
    exact lt_of_le_of_lt htri (by linarith)

lemma Chain.crossing_circular_contract {n : ℕ} (C : Chain n)
    (m : Fin (n + 1)) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hmid : (1 - t) * C.heading m.castSucc + t * C.heading m.succ =
      C.delta / 2) (j : Fin (n + 1)) :
    |C.heading j.castSucc - C.delta / 2| ≤
      circularDist (C.sourcePos j.castSucc)
        ((1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ) := by
  apply le_min
  · exact C.crossing_direct_contract m t ht hmid j
  · exact C.crossing_complement_contract m t ht hmid j

lemma Chain.crossing_circular_contract_strict {n : ℕ} (C : Chain n)
    (m : Fin (n + 1)) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hmid : (1 - t) * C.heading m.castSucc + t * C.heading m.succ =
      C.delta / 2) (j : Fin (n + 1))
    (hdir : Real.cos (C.sourcePos j.castSucc) ≠
        Real.cos ((1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ) ∨
      Real.sin (C.sourcePos j.castSucc) ≠
        Real.sin ((1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ)) :
    |C.heading j.castSucc - C.delta / 2| <
      circularDist (C.sourcePos j.castSucc)
        ((1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ) := by
  apply lt_min
  · apply C.crossing_direct_contract_strict m t ht hmid j
    intro heq
    rcases hdir with hc | hs
    · exact hc (congrArg Real.cos heq)
    · exact hs (congrArg Real.sin heq)
  · exact C.crossing_complement_contract_strict m t ht hmid j hdir

lemma Chain.exists_positive_weight_direction_ne {n : ℕ} (C : Chain n) (α : ℝ) :
    ∃ j : Fin (n + 1), 0 < C.weight j ∧
      (Real.cos (C.sourcePos j.castSucc) ≠ Real.cos α ∨
        Real.sin (C.sourcePos j.castSucc) ≠ Real.sin α) := by
  by_contra h
  push_neg at h
  have hcosTerm (j : Fin (n + 1)) :
      C.weight j * Real.cos (C.sourcePos j.castSucc) =
        C.weight j * Real.cos α := by
    by_cases hw : C.weight j = 0
    · simp [hw]
    · have hp : 0 < C.weight j :=
        lt_of_le_of_ne (C.weight_nonneg j) (Ne.symm hw)
      have he := h j hp
      rw [he.1]
  have hsinTerm (j : Fin (n + 1)) :
      C.weight j * Real.sin (C.sourcePos j.castSucc) =
        C.weight j * Real.sin α := by
    by_cases hw : C.weight j = 0
    · simp [hw]
    · have hp : 0 < C.weight j :=
        lt_of_le_of_ne (C.weight_nonneg j) (Ne.symm hw)
      have he := h j hp
      rw [he.2]
  have hcprod : (∑ j, C.weight j) * Real.cos α = 0 := by
    rw [Finset.sum_mul]
    calc
      (∑ j, C.weight j * Real.cos α) =
          ∑ j, C.weight j * Real.cos (C.sourcePos j.castSucc) := by
        apply Finset.sum_congr rfl
        intro j _
        exact (hcosTerm j).symm
      _ = 0 := C.closure_cos
  have hsprod : (∑ j, C.weight j) * Real.sin α = 0 := by
    rw [Finset.sum_mul]
    calc
      (∑ j, C.weight j * Real.sin α) =
          ∑ j, C.weight j * Real.sin (C.sourcePos j.castSucc) := by
        apply Finset.sum_congr rfl
        intro j _
        exact (hsinTerm j).symm
      _ = 0 := C.closure_sin
  have hc : Real.cos α = 0 :=
    (mul_eq_zero.mp hcprod).resolve_left C.weight_sum_pos.ne'
  have hs : Real.sin α = 0 :=
    (mul_eq_zero.mp hsprod).resolve_left C.weight_sum_pos.ne'
  have htrig := Real.sin_sq_add_cos_sq α
  rw [hc, hs] at htrig
  norm_num at htrig

lemma Chain.delta_eq_sum_turnValue {n : ℕ} (C : Chain n) :
    C.delta = ∑ i, C.turnValue i := by
  symm
  calc
    (∑ i, C.turnValue i) = ∑ i,
        (fun j : Fin (n + 1) =>
          C.heading j.succ - C.heading j.castSucc) i := by
      apply Finset.sum_congr rfl
      intro i _
      exact (C.heading_step i).symm
    _ = C.heading (Fin.last (n + 1)) - C.heading 0 :=
      sum_fin_steps C.heading
    _ = C.delta := by simp [Chain.delta, C.heading_zero]

lemma Chain.sum_abs_turnValue_lt_two_pi {n : ℕ} (C : Chain n) :
    (∑ i, |C.turnValue i|) < 2 * Real.pi := by
  rw [← C.sum_gap_eq_two_pi]
  exact Finset.sum_lt_sum
    (fun i _ => le_of_lt (C.turnValue_strict i))
    ⟨0, Finset.mem_univ 0, C.turnValue_strict 0⟩

lemma Chain.abs_delta_lt_two_pi {n : ℕ} (C : Chain n) :
    |C.delta| < 2 * Real.pi := by
  rw [C.delta_eq_sum_turnValue]
  exact lt_of_le_of_lt (Finset.abs_sum_le_sum_abs _ _)
    C.sum_abs_turnValue_lt_two_pi

lemma circularDist_nonneg_le_pi {s α : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) (2 * Real.pi))
    (hα : α ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    0 ≤ circularDist s α ∧ circularDist s α ≤ Real.pi := by
  rcases hs with ⟨hs0, hs2⟩
  rcases hα with ⟨hα0, hα2⟩
  have habs : |s - α| ≤ 2 * Real.pi := by
    rw [abs_le]
    constructor <;> linarith
  constructor
  · exact le_min (abs_nonneg _) (by linarith)
  · by_cases h : |s - α| ≤ Real.pi
    · exact le_trans (min_le_left _ _) h
    · exact le_trans (min_le_right _ _) (by linarith)

lemma cos_circularDist {s α : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) (2 * Real.pi))
    (hα : α ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    Real.cos (circularDist s α) = Real.cos (s - α) := by
  rcases hs with ⟨hs0, hs2⟩
  rcases hα with ⟨hα0, hα2⟩
  have habs : |s - α| ≤ 2 * Real.pi := by
    rw [abs_le]
    constructor <;> linarith
  by_cases h : |s - α| ≤ Real.pi
  · have hm : circularDist s α = |s - α| := by
      rw [circularDist, min_eq_left]
      linarith
    rw [hm, Real.cos_abs]
  · have hm : circularDist s α = 2 * Real.pi - |s - α| := by
      rw [circularDist, min_eq_right]
      linarith
    rw [hm, Real.cos_two_pi_sub, Real.cos_abs]

/-- The final closure-to-projection step.  It consumes only the explicit
cosine comparison produced by the folded interpolation; vector closure supplies
the zero baseline, and one positive strict term supplies strict positivity. -/
theorem projection_pos_of_cosine_comparison {n : ℕ} (C : Chain n) (α : ℝ)
    (hcos : ∀ j : Fin (n + 1),
      Real.cos (C.sourcePos j.castSucc - α) ≤
        Real.cos (C.heading j.castSucc - C.delta / 2))
    (hstrict : ∃ j : Fin (n + 1), 0 < C.weight j ∧
      Real.cos (C.sourcePos j.castSucc - α) <
        Real.cos (C.heading j.castSucc - C.delta / 2)) :
    0 < ∑ j : Fin (n + 1),
      C.weight j * Real.cos (C.heading j.castSucc - C.delta / 2) := by
  have hbase : (∑ j : Fin (n + 1),
      C.weight j * Real.cos (C.sourcePos j.castSucc - α)) = 0 := by
    calc
      _ = Real.cos α * (∑ j : Fin (n + 1),
            C.weight j * Real.cos (C.sourcePos j.castSucc)) +
          Real.sin α * (∑ j : Fin (n + 1),
            C.weight j * Real.sin (C.sourcePos j.castSucc)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [Real.cos_sub]
        ring
      _ = 0 := by rw [C.closure_cos, C.closure_sin]; ring
  have hlt :
      (∑ j : Fin (n + 1),
        C.weight j * Real.cos (C.sourcePos j.castSucc - α)) <
      ∑ j : Fin (n + 1),
        C.weight j * Real.cos (C.heading j.castSucc - C.delta / 2) := by
    apply Finset.sum_lt_sum
    · intro j _
      exact mul_le_mul_of_nonneg_left (hcos j) (C.weight_nonneg j)
    · obtain ⟨j, hw, hj⟩ := hstrict
      exact ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_left hj hw⟩
  rwa [hbase] at hlt

/-- Once the folded interpolation supplies its circular contraction point,
all trigonometric and strict-closure work is kernel checked here. -/
theorem projection_pos_of_circular_contraction {n : ℕ} (C : Chain n) (α : ℝ)
    (hα : α ∈ Set.Icc (0 : ℝ) (2 * Real.pi))
    (hfold : ∀ j : Fin (n + 1),
      |C.heading j.castSucc - C.delta / 2| ≤
        circularDist (C.sourcePos j.castSucc) α)
    (hstrict : ∃ j : Fin (n + 1), 0 < C.weight j ∧
      |C.heading j.castSucc - C.delta / 2| <
        circularDist (C.sourcePos j.castSucc) α) :
    0 < ∑ j : Fin (n + 1),
      C.weight j * Real.cos (C.heading j.castSucc - C.delta / 2) := by
  apply projection_pos_of_cosine_comparison C α
  · intro j
    have hd := circularDist_nonneg_le_pi (C.sourcePos_mem_interval j) hα
    calc
      Real.cos (C.sourcePos j.castSucc - α) =
          Real.cos (circularDist (C.sourcePos j.castSucc) α) :=
        (cos_circularDist (C.sourcePos_mem_interval j) hα).symm
      _ ≤ Real.cos |C.heading j.castSucc - C.delta / 2| :=
        Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hd.2 (hfold j)
      _ = Real.cos (C.heading j.castSucc - C.delta / 2) := Real.cos_abs _
  · obtain ⟨j, hw, hj⟩ := hstrict
    refine ⟨j, hw, ?_⟩
    have hd := circularDist_nonneg_le_pi (C.sourcePos_mem_interval j) hα
    calc
      Real.cos (C.sourcePos j.castSucc - α) =
          Real.cos (circularDist (C.sourcePos j.castSucc) α) :=
        (cos_circularDist (C.sourcePos_mem_interval j) hα).symm
      _ < Real.cos |C.heading j.castSucc - C.delta / 2| :=
        Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) hd.2 hj
      _ = Real.cos (C.heading j.castSucc - C.delta / 2) := Real.cos_abs _

/-- Premise-free folded-turn projection theorem.  The half-defect level is
located on the piecewise-affine folded heading, strict contraction is proved on
both circular arcs, and source closure supplies a positive-weight direction
away from the selected point. -/
theorem projection_pos {n : ℕ} (C : Chain n) :
    0 < ∑ j : Fin (n + 1),
      C.weight j * Real.cos (C.heading j.castSucc - C.delta / 2) := by
  obtain ⟨m, t, ht, hmid⟩ := C.exists_half_delta_crossing
  let α := (1 - t) * C.sourcePos m.castSucc + t * C.sourcePos m.succ
  apply projection_pos_of_circular_contraction C α
  · exact C.crossing_alpha_mem_interval m t ht
  · intro j
    exact C.crossing_circular_contract m t ht hmid j
  · obtain ⟨j, hjw, hjdir⟩ := C.exists_positive_weight_direction_ne α
    refine ⟨j, hjw, ?_⟩
    exact C.crossing_circular_contract_strict m t ht hmid j hjdir

/-- Exact zero-turnValue control: if every developed heading is zero, the requested
weighted projection is precisely the assumed positive total weight. -/
theorem projection_pos_of_heading_zero {n : ℕ} (C : Chain n)
    (hheading : ∀ j : Fin (n + 1), C.heading j.castSucc = 0)
    (hdelta : C.delta = 0) :
    0 < ∑ j : Fin (n + 1),
      C.weight j * Real.cos (C.heading j.castSucc - C.delta / 2) := by
  simpa [hheading, hdelta] using C.weight_sum_pos

end
end FoldedTurnProjection
