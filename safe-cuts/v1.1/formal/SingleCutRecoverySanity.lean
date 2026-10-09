import SingleCutRecovery

/-! Allowed-scope type specializations. `n = 2` is exactly three side faces,
the smallest chain admitted by the endpoint. `n = 3` is four side faces.
No one-face specialization is attempted or implied. -/

#check @SingleCutRecovery.exists_safe_glued_table_from_trimmed_unfoldings
  (S := Fin 1) (n := 2)

#check @SingleCutRecovery.exists_safe_glued_table_from_trimmed_unfoldings
  (S := Fin 3) (n := 3)

example : 2 ≤ (2 : ℕ) := by omega
example : 2 ≤ (3 : ℕ) := by omega
