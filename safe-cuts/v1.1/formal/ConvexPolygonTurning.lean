import PolygonSupportCompleteness
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

open scoped BigOperators NNReal
open MergedNormalPrismatoid PolygonSupportCompleteness
open PolygonSupportCompleteness.ReducedConvexPolygon
open InnerProductGeometry

namespace ConvexPolygonTurning
noncomputable section
set_option maxHeartbeats 2000000

variable {n : ℕ} [NeZero n]

def exteriorTurn (P : ReducedConvexPolygon n) (i : Fin n) : ℝ :=
  angle (edgeVector P.vertex (prev i)) (edgeVector P.vertex i)

lemma incoming_ne_zero (P : ReducedConvexPolygon n) (i : Fin n) :
    edgeVector P.vertex (prev i) ≠ 0 := by
  rw [edgeVector, next_prev]
  exact sub_ne_zero.mpr (by simpa only [next_prev] using P.edge_ne (prev i))

lemma outgoing_ne_zero (P : ReducedConvexPolygon n) (i : Fin n) :
    edgeVector P.vertex i ≠ 0 := sub_ne_zero.mpr (P.edge_ne i)

lemma exteriorTurn_ne_zero (P : ReducedConvexPolygon n) (i : Fin n) :
    exteriorTurn P i ≠ 0 := by
  intro hz
  obtain ⟨_, r, hr, he⟩ := angle_eq_zero_iff.mp hz
  have hdet := PolygonSupportCompleteness.ReducedConvexPolygon.corner_det_pos P i
  have hzero : det (edgeVector P.vertex (prev i)) (edgeVector P.vertex i) = 0 := by
    rw [he]
    simp [det]
    ring
  have hrel : det (edgeVector P.vertex (prev i)) (edgeVector P.vertex i) =
      -det (back P i) (ahead P i) := by
    simp [edgeVector, back, ahead, next_prev, det]
    ring
  rw [hzero] at hrel
  linarith

lemma exteriorTurn_pos (P : ReducedConvexPolygon n) (i : Fin n) :
    0 < exteriorTurn P i :=
  lt_of_le_of_ne (angle_nonneg _ _) (Ne.symm (exteriorTurn_ne_zero P i))

lemma exteriorTurn_ne_pi (P : ReducedConvexPolygon n) (i : Fin n) :
    exteriorTurn P i ≠ Real.pi := by
  intro hpi
  obtain ⟨_, r, hr, he⟩ := angle_eq_pi_iff.mp hpi
  have hdet := PolygonSupportCompleteness.ReducedConvexPolygon.corner_det_pos P i
  have hzero : det (edgeVector P.vertex (prev i)) (edgeVector P.vertex i) = 0 := by
    rw [he]
    simp [det]
    ring
  have hrel : det (edgeVector P.vertex (prev i)) (edgeVector P.vertex i) =
      -det (back P i) (ahead P i) := by
    simp [edgeVector, back, ahead, next_prev, det]
    ring
  rw [hzero] at hrel
  linarith

lemma exteriorTurn_lt_pi (P : ReducedConvexPolygon n) (i : Fin n) :
    exteriorTurn P i < Real.pi :=
  lt_of_le_of_ne (angle_le_pi _ _) (exteriorTurn_ne_pi P i)

def interiorAngle (P : ReducedConvexPolygon n) (i : Fin n) : ℝ :=
  angle (back P i) (ahead P i)

lemma exteriorTurn_eq_pi_sub_interiorAngle
    (P : ReducedConvexPolygon n) (i : Fin n) :
    exteriorTurn P i = Real.pi - interiorAngle P i := by
  rw [exteriorTurn, interiorAngle, edgeVector, edgeVector, next_prev]
  have hback : P.vertex i - P.vertex (prev i) = -(back P i) := by
    simp [back]
  have hahead : P.vertex (next i) - P.vertex i = ahead P i := rfl
  rw [hback, hahead, angle_neg_left]

lemma edgeRow_vertex_lt_of_not_endpoint (P : ReducedConvexPolygon n)
    (i j : Fin n) (hji : j ≠ i) (hjn : j ≠ next i) :
    P.edgeRow i (P.vertex j) < 0 := by
  have hle : P.edgeRow i (P.vertex j) ≤ 0 := by
    simpa [P.edgeRow_apply] using P.supports i j
  exact lt_of_le_of_ne hle (fun h => by
    rcases (P.vertex_edge_eq_iff i j).mp h with h | h
    · exact hji h
    · exact hjn h)

/-- The sum of the interior angles of a reduced convex polygon.  The proof is
by the fan from vertex zero.  Strict support rows order the fan diagonals, and
`local_tangent_coordinates` supplies every angle split. -/
theorem sum_interiorAngle_eq (P : ReducedConvexPolygon n) :
    (∑ i, interiorAngle P i) = (n - 2 : ℕ) * Real.pi := by
  obtain ⟨m, hm⟩ : ∃ m, n = m + 3 := by
    use n - 3
    have := P.three_le
    omega
  subst n
  let v : Fin (m + 3) → Plane := P.vertex
  let z : Fin (m + 3) := ⟨0, by omega⟩
  let ix (k : ℕ) (hk : k < m + 3) : Fin (m + 3) := ⟨k, hk⟩
  let ray (k : ℕ) : Plane :=
    v ⟨k % (m+3), Nat.mod_lt _ (by omega)⟩ - v z
  have ray_eq (k : ℕ) (hk : k < m+3) : ray k = v (ix k hk) - v z := by
    simp [ray, ix, Nat.mod_eq_of_lt hk]

  have hnext (k : ℕ) (hk : k + 1 < m + 3) :
      next (ix k (by omega : k < m + 3)) = ix (k+1) hk := by
    apply Fin.ext
    rw [next_val]
    simp [ix, hk]

  have hprev (k : ℕ) (hk0 : 0 < k) (hk : k < m + 3) :
      prev (ix k hk) = ix (k-1) (by omega) := by
    apply Fin.ext
    simp [prev, ix, Nat.ne_of_gt hk0]

  have hnext_last : next (ix (m+2) (by omega)) = z := by
    apply Fin.ext
    rw [next_val]
    simp [ix, z]

  have hprev_zero : prev z = ix (m+2) (by omega) := by
    apply Fin.ext
    simp [prev, ix, z]

  have hray_ne (k : ℕ) (hk0 : 0 < k) (hk : k < m + 3) : ray k ≠ 0 := by
    intro hz
    rw [ray_eq k hk] at hz
    have hv : v (ix k hk) = v z := sub_eq_zero.mp hz
    have htight : P.edgeRow z (P.vertex (ix k hk)) = 0 := by
      change P.edgeRow z (v (ix k hk)) = 0
      rw [hv]
      simp [v, z, P.edgeRow_apply]
    rcases (P.vertex_edge_eq_iff z (ix k hk)).mp htight with h | h
    · have heq : k = 0 := Fin.mk.inj h
      omega
    · apply P.edge_ne z
      rw [← h]
      exact hv

  have hfan_det (k : ℕ) (hk0 : 0 < k) (hk : k+1 < m+3) :
      det (ray k) (ray (k+1)) < 0 := by
    let i := ix k (by omega : k < m+3)
    have hz_ne_i : z ≠ i := by
      intro h
      have := congrArg Fin.val h
      simp [z, i, ix] at this
      omega
    have hz_ne_next : z ≠ next i := by
      rw [hnext k hk]
      intro h
      have := congrArg Fin.val h
      simp [z, ix] at this
    have hlt := edgeRow_vertex_lt_of_not_endpoint P i z hz_ne_i hz_ne_next
    rw [PolygonSupportCompleteness.ReducedConvexPolygon.edgeRow_det] at hlt
    change det (v (next i) - v i) (v z - v i) < 0 at hlt
    rw [show next i = ix (k+1) hk by exact hnext k hk] at hlt
    have heq : det (v (ix (k+1) hk) - v i) (v z - v i) =
        det (ray k) (ray (k+1)) := by
      rw [ray_eq k (by omega), ray_eq (k+1) hk]
      simp [i, det]
      ring
    rwa [heq] at hlt

  have hray_coords (k : ℕ) (hk : k < m+3) :
      ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧
        ray k = α • ray (m+2) + β • ray 1 := by
    obtain ⟨α, β, hα, hβ, he⟩ :=
      PolygonSupportCompleteness.ReducedConvexPolygon.local_tangent_coordinates
        P z (v (ix k hk))
        (by simpa [P.edgeRow_apply, v] using P.supports (prev z) (ix k hk))
        (by simpa [P.edgeRow_apply, v] using P.supports z (ix k hk))
    refine ⟨α, β, hα, hβ, ?_⟩
    rw [back, ahead, hprev_zero] at he
    change (v (ix k hk) - v z) = α • (v (ix (m+2) (by omega)) - v z) +
      β • (v (next z) - v z) at he
    have hn : next z = ix 1 (by omega) := by
      apply Fin.ext
      rw [next_val]
      simp [z, ix]
    rw [hn] at he
    rw [ray_eq k hk, ray_eq (m+2) (by omega), ray_eq 1 (by omega)]
    exact he

  have hray_between (k : ℕ) (hk0 : 0 < k) (hk : k+1 < m+3) :
      ray k ∈ Submodule.span ℝ≥0
        ({ray 1, ray (k+1)} : Set Plane) := by
    obtain ⟨α, β, hα, hβ, hx⟩ := hray_coords k (by omega)
    obtain ⟨γ, δ, hγ, hδ, hy⟩ := hray_coords (k+1) hk
    let a := ray (m+2)
    let b := ray 1
    let x := ray k
    let y := ray (k+1)
    have hD := PolygonSupportCompleteness.ReducedConvexPolygon.corner_det_pos P z
    have hab : det a b = det (back P z) (ahead P z) := by
      have hn : next z = ix 1 (by omega) := by
        apply Fin.ext
        rw [next_val]
        simp [z, ix]
      dsimp [a, b]
      rw [ray_eq (m+2) (by omega), ray_eq 1 (by omega), back, ahead,
        hprev_zero, hn]
    have hDab : 0 < det a b := hab.trans_gt hD
    have hxy : det x y < 0 := hfan_det k hk0 hk
    have hcoord : α * δ - β * γ < 0 := by
      dsimp [x, y] at hxy
      rw [hx, hy] at hxy
      simp only [det, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hxy ⊢
      have hDcoord := hDab
      simp only [det] at hDcoord
      nlinarith
    have hγpos : 0 < γ := by
      by_contra hnot
      have hγz : γ = 0 := le_antisymm (le_of_not_gt hnot) hγ
      rw [hγz] at hcoord
      nlinarith
    have hby : det b y < 0 := by
      dsimp [b, y]
      rw [hy]
      simp only [det, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      have hDcoord := hDab
      simp only [det] at hDcoord
      nlinarith
    have hrepr := det_reconstruct b y x hby.ne
    rw [Submodule.mem_span_pair]
    refine ⟨⟨det x y / det b y,
        div_nonneg_of_nonpos hxy.le hby.le⟩,
      ⟨det b x / det b y, ?_⟩, ?_⟩
    · have hbx : det b x ≤ 0 := by
        dsimp [b, x]
        rw [hx]
        simp only [det, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        have hDcoord := hDab
        simp only [det] at hDcoord
        nlinarith
      exact div_nonneg_of_nonpos hbx hby.le
    · change (det x y / det b y) • ray 1 +
        (det b x / det b y) • ray (k+1) = ray k
      dsimp [x, y, b] at hrepr
      exact hrepr.symm

  have horigin_prefix : ∀ r : ℕ, r ≤ m+1 →
      angle (ray 1) (ray (r+1)) =
        ∑ k ∈ Finset.range r,
          angle (ray (k+1)) (ray (k+2)) := by
    intro r hr
    induction r with
    | zero =>
        rw [Finset.sum_range_zero]
        exact angle_self (hray_ne 1 (by omega) (by omega))
    | succ r ih =>
        rw [Finset.sum_range_succ, ← ih (by omega)]
        apply angle_eq_angle_add_add_angle_add_of_mem_span
        · exact hray_ne (r+1) (by omega) (by omega)
        · exact hray_between (r+1) (by omega) (by omega)

  have horigin : interiorAngle P z =
      ∑ k : Fin (m+1),
        angle (ray (k.val+1)) (ray (k.val+2)) := by
    have hp := horigin_prefix (m+1) (by omega)
    rw [Fin.sum_univ_eq_sum_range (fun k =>
      angle (ray (k+1)) (ray (k+2))) (m+1)]
    change interiorAngle P z = _
    rw [interiorAngle]
    have hb : back P z = ray (m+2) := by
      rw [ray_eq (m+2) (by omega), back, hprev_zero]
    have ha : ahead P z = ray 1 := by
      rw [ahead]
      have hn : next z = ix 1 (by omega) := by
        apply Fin.ext
        rw [next_val]
        simp [z, ix]
      rw [ray_eq 1 (by omega), hn]
    rw [hb, ha, angle_comm]
    exact hp

  let leftA (k : Fin (m+1)) : ℝ :=
    angle (v z - v (ix (k.val+1) (by omega)))
      (v (ix (k.val+2) (by omega)) - v (ix (k.val+1) (by omega)))
  let rightA (k : Fin (m+1)) : ℝ :=
    angle (v (ix (k.val+1) (by omega)) - v (ix (k.val+2) (by omega)))
      (v z - v (ix (k.val+2) (by omega)))
  let centerA (k : Fin (m+1)) : ℝ :=
    angle (ray (k.val+1)) (ray (k.val+2))

  have htriangle (k : Fin (m+1)) : leftA k + rightA k + centerA k = Real.pi := by
    have hne : v z ≠ v (ix (k.val+1) (by omega)) := by
      intro he
      apply hray_ne (k.val+1) (by omega) (by omega)
      rw [ray_eq (k.val+1) (by omega)]
      exact sub_eq_zero.mpr he.symm
    have ht := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (v (ix (k.val+2) (by omega))) hne
    dsimp [leftA, rightA, centerA]
    rw [ray_eq (k.val+1) (by omega), ray_eq (k.val+2) (by omega)]
    change angle (v (ix (k.val+1) (by omega)) - v z)
        (v (ix (k.val+2) (by omega)) - v z) +
      angle (v z - v (ix (k.val+2) (by omega)))
        (v (ix (k.val+1) (by omega)) - v (ix (k.val+2) (by omega))) +
      angle (v (ix (k.val+2) (by omega)) - v (ix (k.val+1) (by omega)))
        (v z - v (ix (k.val+1) (by omega))) = Real.pi at ht
    rw [angle_comm (v z - v (ix (k.val+1) (by omega))),
      angle_comm (v (ix (k.val+1) (by omega)) - v (ix (k.val+2) (by omega)))]
    linarith

  have hinterior_first : interiorAngle P (ix 1 (by omega)) = leftA 0 := by
    have hp : prev (ix 1 (by omega)) = z := by
      apply Fin.ext
      simpa [z, ix] using congrArg Fin.val (hprev 1 (by omega) (by omega))
    have hn := hnext 1 (by omega : 1+1 < m+3)
    rw [interiorAngle, back, ahead, hp, hn]
    rfl

  have hinterior_last : interiorAngle P (ix (m+2) (by omega)) = rightA (Fin.last m) := by
    have hp := hprev (m+2) (by omega) (by omega)
    rw [interiorAngle, back, ahead, hp, hnext_last]
    rfl

  have hinterior_mid (k : Fin m) :
      interiorAngle P (ix (k.val+2) (by omega)) =
        rightA k.castSucc + leftA k.succ := by
    rw [interiorAngle]
    have hp := hprev (k.val+2) (by omega) (by omega)
    have hn := hnext (k.val+2) (by omega : k.val+2+1 < m+3)
    have hdiag_ne : v z - v (ix (k.val+2) (by omega)) ≠ 0 := by
      intro heq
      apply hray_ne (k.val+2) (by omega) (by omega)
      rw [ray_eq (k.val+2) (by omega)]
      exact sub_eq_zero.mpr (sub_eq_zero.mp heq).symm
    obtain ⟨α, β, hα, hβ, he⟩ :=
      PolygonSupportCompleteness.ReducedConvexPolygon.local_tangent_coordinates P
        (ix (k.val+2) (by omega)) (v z)
        (by simpa [P.edgeRow_apply, v] using
          P.supports (prev (ix (k.val+2) (by omega))) z)
        (by simpa [P.edgeRow_apply, v] using
          P.supports (ix (k.val+2) (by omega)) z)
    have hmem : v z - v (ix (k.val+2) (by omega)) ∈
        Submodule.span ℝ≥0
          ({back P (ix (k.val+2) (by omega)),
            ahead P (ix (k.val+2) (by omega))} : Set Plane) := by
      rw [Submodule.mem_span_pair]
      refine ⟨⟨α, hα⟩, ⟨β, hβ⟩, ?_⟩
      change α • back P (ix (k.val+2) (by omega)) +
        β • ahead P (ix (k.val+2) (by omega)) =
          v z - v (ix (k.val+2) (by omega))
      exact he.symm
    have hsplit := angle_eq_angle_add_add_angle_add_of_mem_span hdiag_ne hmem
    simpa [rightA, leftA, back, ahead, hp, hn, v, ix] using hsplit

  rw [Fin.sum_univ_succ]
  change interiorAngle P z + _ = _
  rw [Fin.sum_univ_succ]
  change interiorAngle P z + (interiorAngle P (ix 1 (by omega)) + _) = _
  rw [Fin.sum_univ_castSucc]
  have hmidSum :
      (∑ k : Fin m, interiorAngle P k.castSucc.succ.succ) =
        ∑ k : Fin m, interiorAngle P (ix (k.val+2) (by omega)) := by
    apply Finset.sum_congr rfl
    intro k _
    congr 2
  have hlastIndex : (Fin.last m).succ.succ = ix (m+2) (by omega) := by
    apply Fin.ext
    rfl
  rw [hmidSum, hlastIndex]
  change interiorAngle P z +
    (interiorAngle P (ix 1 (by omega)) +
      ((∑ k : Fin m, interiorAngle P (ix (k.val+2) (by omega))) +
        interiorAngle P (ix (m+2) (by omega)))) = _
  rw [horigin, hinterior_first, hinterior_last]
  simp_rw [hinterior_mid]
  have htriSum :
      (∑ k : Fin (m+1), (leftA k + rightA k + centerA k)) =
        (∑ _k : Fin (m+1), Real.pi) := by
    apply Finset.sum_congr rfl
    intro k _
    exact htriangle k
  simp only [Finset.sum_add_distrib] at htriSum
  have hcard : (∑ _k : Fin (m+1), Real.pi) = (m+1) * Real.pi := by simp
  rw [hcard] at htriSum
  rw [Fin.sum_univ_succ leftA] at htriSum
  rw [Fin.sum_univ_castSucc rightA] at htriSum
  rw [Finset.sum_add_distrib]
  change (∑ k : Fin (m+1), centerA k) +
      (leftA 0 + (((∑ k : Fin m, rightA k.castSucc) +
        ∑ k : Fin m, leftA k.succ) + rightA (Fin.last m))) = _
  change _ = (m+1) * Real.pi at htriSum
  have hnat : m + 3 - 2 = m + 1 := by omega
  rw [hnat]
  push_cast
  linarith

/-- The exterior turns of every reduced convex polygon make one full turn. -/
theorem sum_exteriorTurn_eq_two_pi (P : ReducedConvexPolygon n) :
    (∑ i, exteriorTurn P i) = 2 * Real.pi := by
  simp_rw [exteriorTurn_eq_pi_sub_interiorAngle]
  rw [Finset.sum_sub_distrib, sum_interiorAngle_eq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn := P.three_le
  push_cast
  rw [Nat.cast_sub (by omega : 2 ≤ n)]
  ring

#print axioms sum_exteriorTurn_eq_two_pi

end
end ConvexPolygonTurning
