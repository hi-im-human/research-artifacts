import MixedTurnSafeCut

namespace MixedTurnSafeCutSanity
open MixedTurnSafeCut Set
noncomputable section

def pt (x y : ℝ) : Plane := WithLp.toLp 2 ![x,y]

/-- Two genuinely nonrectangular panels. The INTERNAL hinge x=1 is vertical;
bottom lengths are 1, upper lengths are 2. All internal increments vanish. -/
def specimen : DevelopedFamily 1 where
  q := fun _ => 0
  B := fun _ i => pt i 0
  e := fun _ _ => pt 1 0
  d := fun _ i => pt ((i : ℝ)-1) 1
  ratio := fun _ _ => 2
  heading := fun _ _ => 0
  length := fun _ _ => 1
  ratio_pos := by intros; norm_num
  length_pos := by intros; norm_num
  represents := by intros; ext c; fin_cases c <;> simp [pt, direction]
  orientation := by intro k; left; intros; simp [pt, det]
  lower_step := by intros; ext c; fin_cases c <;> simp [pt, Nat.cast_add]
  hinge_step := by intros; ext c; fin_cases c <;> simp [pt, Nat.cast_add] <;> ring
  internal_step := by intros; simp
  total_variation := by simp [positiveBudget, negativeBudget, Real.pi_pos]

theorem nonrectangular_rim_lengths : specimen.ratio 0 0 = 2 ∧ specimen.ratio 0 1 = 2 := ⟨rfl,rfl⟩

theorem internal_vertical_hinge : specimen.d 0 1 0 = 0 ∧ specimen.d 0 1 1 = 1 := by
  norm_num [specimen, pt]

theorem vertical_trace (t : ℝ) :
    panel (specimen.B 0 0) (specimen.e 0 0) (specimen.d 0 0) (specimen.ratio 0 0) 1 t = pt 1 t ∧
    panel (specimen.B 0 1) (specimen.e 0 1) (specimen.d 0 1) (specimen.ratio 0 1) 0 t = pt 1 t := by
  constructor <;> ext c <;> fin_cases c <;> simp [panel, rho, specimen, pt] <;> ring

/-- Actual global family application. No nonoverlap premise. -/
theorem specimen_safe_cut : ∃ k : Fin 2, ∀ i j : Fin 2, i ≠ j →
    Disjoint (interior (specimen.face k i)) (interior (specimen.face k j)) := by
  apply mixed_family_safe_cut specimen
  · exact ⟨0, by simp [specimen, positiveBudget, negativeBudget]⟩
  · exact ⟨0, by simp [specimen, positiveBudget, negativeBudget]⟩

/-- Safety of the specifically positioned pair, not only an existential witness. -/
theorem specimen_nonoverlap :
    Disjoint (interior (specimen.face 0 0)) (interior (specimen.face 0 1)) := by
  obtain ⟨k, hk⟩ := specimen_safe_cut
  exact hk 0 1 (by decide)

theorem boundary_identification (t : ℝ) :
    panel (specimen.B 0 0) (specimen.e 0 0) (specimen.d 0 0) 2 1 t =
      panel (specimen.B 0 1) (specimen.e 0 1) (specimen.d 0 1) 2 0 t :=
  (vertical_trace t).1.trans (vertical_trace t).2.symm

/-- P reaches the threshold, but T=0 still leaves strict retained budgets. -/
theorem zero_T_threshold :
    (1 : ℝ)-max (1/2) 0 < 1 ∧ (1/2 : ℝ)-max (-(1/2)) 0 < 1 := by
  exact zero_cut_budgets 1 (1/2) (1/2) 1 (by norm_num) (by norm_num)

/-- n=0 has no internal steps; the omitted cyclic hinge is the sole hinge. -/
theorem one_panel_omission (q : Fin 1 → ℝ) :
    (∑ i : Fin 0, q ((0 : Fin 1)+i.succ)) = (∑ j : Fin 1, q j)-q 0 :=
  cyclic_omission 0 q 0

/-- Exact orientation negative control supplied in the handoff. -/
theorem opposite_orientation :
    det (pt 1 0) (pt 0 1) = 1 ∧ det (pt 1 2) (pt 1 1) = -1 := by
  norm_num [det, pt]

theorem negative_control_collision :
    panel (pt 0 0) (pt 1 0) (pt 0 1) 2 (14/15) (1/2) = pt (7/5) (1/2) ∧
    panel (pt 1 0) (pt 1 2) (pt 1 1) 1 (1/10) (3/10) = pt (7/5) (1/2) := by
  constructor <;> ext c <;> fin_cases c <;> norm_num [panel, rho, pt]

theorem negative_control_actual_overlap :
    pt (7/5) (1/2) ∈ interior (hull (pt 0 0) (pt 1 0) (pt 0 1) 2) ∩
      interior (hull (pt 1 0) (pt 1 2) (pt 1 1) 1) := by
  constructor
  · rw [← negative_control_collision.1]
    exact strict_parameters_interior _ _ _ _ (by norm_num) (by norm_num [det, pt])
      (14/15) (1/2) (by norm_num) (by norm_num)
  · rw [← negative_control_collision.2]
    exact strict_parameters_interior _ _ _ _ (by norm_num) (by norm_num [det, pt])
      (1/10) (3/10) (by norm_num) (by norm_num)

/-- A second specimen has genuinely nonzero fixed-rim signs. The two cuts
retain opposite quarter turns; thus swapping omitted and retained q is detectable. -/
def turnSign (k : Fin 2) : ℝ := if k = 0 then -1 else 1

def mixedQ (k : Fin 2) : ℝ := -turnSign k * (Real.pi/2)

def mixedB (k : Fin 2) (i : ℕ) : Plane :=
  if i = 0 then pt 0 0 else if i = 1 then pt 1 0 else pt 1 (turnSign k)

def mixedE (k : Fin 2) (i : ℕ) : Plane :=
  if i = 0 then pt 1 0 else pt 0 (turnSign k)

def mixedD (k : Fin 2) (i : ℕ) : Plane :=
  if i = 0 then pt (-turnSign k) 1
  else if i = 1 then pt (-turnSign k+1/2) 1
  else pt (-turnSign k+1/2) (1+turnSign k/2)

def mixedHeading (k : Fin 2) (i : ℕ) : ℝ := if i = 0 then 0 else turnSign k*(Real.pi/2)

lemma mixedQ_budgets : positiveBudget mixedQ = Real.pi/2 ∧ negativeBudget mixedQ = Real.pi/2 := by
  have hp : 0 ≤ Real.pi/2 := (half_pos Real.pi_pos).le
  change (∑ k : Fin 2, max (mixedQ k) 0) = Real.pi/2 ∧
    (∑ k : Fin 2, max (-mixedQ k) 0) = Real.pi/2
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  norm_num [mixedQ, turnSign, max_eq_left hp, max_eq_right (neg_nonpos.mpr hp)]

def mixedSpecimen : DevelopedFamily 1 where
  q := mixedQ
  B := mixedB
  e := mixedE
  d := mixedD
  ratio := fun _ _ => 3/2
  heading := mixedHeading
  length := fun _ _ => 1
  ratio_pos := by intros; norm_num
  length_pos := by intros; norm_num
  represents := by
    intro k i hi
    fin_cases k <;> interval_cases i <;> ext c <;> fin_cases c <;>
      norm_num [mixedE, mixedHeading, turnSign, direction, pt]
  orientation := by
    intro k; left; intro i hi
    fin_cases k <;> interval_cases i <;> norm_num [mixedE, mixedD, turnSign, det, pt]
  lower_step := by
    intro k i hi
    fin_cases k <;> interval_cases i <;> ext c <;> fin_cases c <;>
      norm_num [mixedB, mixedE, turnSign, pt]
  hinge_step := by
    intro k i hi
    fin_cases k <;> interval_cases i <;> ext c <;> fin_cases c <;>
      norm_num [mixedD, mixedE, turnSign, pt]
  internal_step := by
    intro k i
    fin_cases k <;> fin_cases i <;> norm_num [mixedHeading, mixedQ, turnSign]
  total_variation := by rw [mixedQ_budgets.1, mixedQ_budgets.2]; linarith [Real.pi_pos]

theorem nonzero_cyclic_index_check :
    mixedSpecimen.heading 0 1 - mixedSpecimen.heading 0 0 = mixedSpecimen.q 1 ∧
    mixedSpecimen.heading 1 1 - mixedSpecimen.heading 1 0 = mixedSpecimen.q 0 ∧
    mixedSpecimen.q 0 ≠ mixedSpecimen.q 1 := by
  norm_num [mixedSpecimen, mixedHeading, mixedQ, turnSign]
  linarith [Real.pi_pos]

theorem genuinely_mixed_safe_cut : ∃ k : Fin 2, ∀ i j : Fin 2, i ≠ j →
    Disjoint (interior (mixedSpecimen.face k i)) (interior (mixedSpecimen.face k j)) := by
  apply mixed_family_safe_cut mixedSpecimen
  · refine ⟨1, ?_⟩
    change mixedQ 1-(positiveBudget mixedQ-negativeBudget mixedQ) ≤ 0
    rw [mixedQ_budgets.1, mixedQ_budgets.2]
    norm_num [mixedQ, turnSign]
    linarith [Real.pi_pos]
  · refine ⟨0, ?_⟩
    change 0 ≤ mixedQ 0-(positiveBudget mixedQ-negativeBudget mixedQ)
    rw [mixedQ_budgets.1, mixedQ_budgets.2]
    norm_num [mixedQ, turnSign]
    linarith [Real.pi_pos]

end
end MixedTurnSafeCutSanity

#print axioms MixedTurnSafeCutSanity.specimen_nonoverlap
#print axioms MixedTurnSafeCutSanity.specimen_safe_cut
#print axioms MixedTurnSafeCutSanity.vertical_trace
#print axioms MixedTurnSafeCutSanity.negative_control_actual_overlap
#print axioms MixedTurnSafeCutSanity.nonzero_cyclic_index_check
#print axioms MixedTurnSafeCutSanity.genuinely_mixed_safe_cut
