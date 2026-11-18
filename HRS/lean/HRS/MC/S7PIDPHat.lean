import Mathlib

/-!
# Packet PI-D, sub-packet P (part 1): hat weights of the polygonal interpolation

Scalar and vector facts about `∑_{i ≤ N} max 0 (1 - |X - i|) • w i` (the hat-weighted sum used by `polyAt`):
the two-term formula for `X ∈ [0,N]`, the norm bound, and the refinement estimate for the dyadic
interpolation `polyAt (n+1) v` versus `polyAt n (v ∘ (2·))`.
-/

open Finset

noncomputable section

namespace HRS.MC.Sec7.S7PIDP

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- two-term formula, for an integer `j` with `j ≤ X < j+1` -/
theorem S7PIDP_hat_aux (N j : ℕ) (X : ℝ) (hjX : (j : ℝ) ≤ X) (hXj : X < (j : ℝ) + 1) (hjN : j ≤ N)
    (hXN : X ≤ (N : ℝ)) (w : ℕ → E) :
    ∑ i ∈ range (N + 1), max 0 (1 - |X - (i : ℝ)|) • w i =
      (1 - (X - (j : ℝ))) • w j + (X - (j : ℝ)) • w (j + 1) := by
  have hθ0 : (0 : ℝ) ≤ X - (j : ℝ) := by linarith
  have key : ∀ i ∈ range (N + 1), max 0 (1 - |X - (i : ℝ)|) • w i =
      ((if i = j then 1 - (X - (j : ℝ)) else 0) + (if i = j + 1 then X - (j : ℝ) else 0)) • w i := by
    intro i _
    congr 1
    rcases lt_trichotomy i j with h | h | h
    · have h1 : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast h
      rw [if_neg (by omega), if_neg (by omega), add_zero,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ X - (i : ℝ)), max_eq_left (by linarith)]
    · rw [h, if_pos rfl, if_neg (by omega), add_zero,
        abs_of_nonneg hθ0, max_eq_right (by linarith)]
    · by_cases h2 : i = j + 1
      · rw [h2, if_neg (by omega), if_pos rfl, zero_add]
        push_cast
        rw [abs_of_nonpos (by linarith : X - ((j : ℝ) + 1) ≤ 0), max_eq_right (by linarith)]
        ring
      · have h1 : (j : ℝ) + 2 ≤ (i : ℝ) := by
          have : j + 2 ≤ i := by omega
          exact_mod_cast this
        rw [if_neg (by omega), if_neg h2, add_zero,
          abs_of_nonpos (by linarith : X - (i : ℝ) ≤ 0), max_eq_left (by linarith)]
  rw [Finset.sum_congr rfl key]
  simp only [add_smul, Finset.sum_add_distrib, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq' (range (N + 1)) j, Finset.sum_ite_eq' (range (N + 1)) (j + 1)]
  by_cases hjN' : j < N
  · rw [if_pos (Finset.mem_range.2 (by omega)), if_pos (Finset.mem_range.2 (by omega))]
  · have hjeq : (j : ℝ) = N := by
      have : j = N := by omega
      exact_mod_cast this
    have hθ : X - (j : ℝ) = 0 := by linarith
    rw [if_pos (Finset.mem_range.2 (by omega)), if_neg (fun h => by have := Finset.mem_range.1 h; omega),
      hθ, zero_smul, add_zero]

/-- the floor of `X ∈ [0,N]` with a positive fractional part is `< N` -/
theorem S7PIDP_floor_lt (N : ℕ) (X : ℝ) (hX0 : 0 ≤ X) (hXN : X ≤ (N : ℝ))
    (hθ : 0 < X - (⌊X⌋₊ : ℝ)) : ⌊X⌋₊ < N := by
  by_contra h
  push_neg at h
  have : (N : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast h
  linarith [Nat.floor_le hX0]

/-- the two-term formula at the floor -/
theorem S7PIDP_hat_sum (N : ℕ) (X : ℝ) (hX0 : 0 ≤ X) (hXN : X ≤ (N : ℝ)) (w : ℕ → E) :
    ∑ i ∈ range (N + 1), max 0 (1 - |X - (i : ℝ)|) • w i =
      (1 - (X - (⌊X⌋₊ : ℝ))) • w ⌊X⌋₊ + (X - (⌊X⌋₊ : ℝ)) • w (⌊X⌋₊ + 1) := by
  have hjX : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le hX0
  have hXj : X < ((⌊X⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one X
  have hjN : ⌊X⌋₊ ≤ N := by
    have : ((⌊X⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) := hjX.trans hXN
    exact_mod_cast this
  exact S7PIDP_hat_aux N _ X hjX hXj hjN hXN w

/-- the norm of a hat-weighted sum is bounded by the largest node norm -/
theorem S7PIDP_hat_norm_le (N : ℕ) (X : ℝ) (hX0 : 0 ≤ X) (hXN : X ≤ (N : ℝ)) (w : ℕ → E) (b : ℝ)
    (hb0 : 0 ≤ b) (hw : ∀ i ≤ N, ‖w i‖ ≤ b) :
    ‖∑ i ∈ range (N + 1), max 0 (1 - |X - (i : ℝ)|) • w i‖ ≤ b := by
  rw [S7PIDP_hat_sum N X hX0 hXN w]
  have hθ0 : 0 ≤ X - (⌊X⌋₊ : ℝ) := by linarith [Nat.floor_le hX0]
  have hjN : ⌊X⌋₊ ≤ N := by
    have : ((⌊X⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) := (Nat.floor_le hX0).trans hXN
    exact_mod_cast this
  have h1 : ‖(1 - (X - (⌊X⌋₊ : ℝ))) • w ⌊X⌋₊‖ ≤ (1 - (X - (⌊X⌋₊ : ℝ))) * b := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [Nat.lt_floor_add_one X])]
    exact mul_le_mul_of_nonneg_left (hw _ hjN) (by linarith [Nat.lt_floor_add_one X])
  have h2 : ‖(X - (⌊X⌋₊ : ℝ)) • w (⌊X⌋₊ + 1)‖ ≤ (X - (⌊X⌋₊ : ℝ)) * b := by
    rcases eq_or_lt_of_le hθ0 with h | h
    · rw [← h, zero_smul, norm_zero, zero_mul]
    · have hj1 : ⌊X⌋₊ + 1 ≤ N := S7PIDP_floor_lt N X hX0 hXN h
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ0]
      exact mul_le_mul_of_nonneg_left (hw _ hj1) hθ0
  calc _ ≤ ‖(1 - (X - (⌊X⌋₊ : ℝ))) • w ⌊X⌋₊‖ + ‖(X - (⌊X⌋₊ : ℝ)) • w (⌊X⌋₊ + 1)‖ := norm_add_le _ _
    _ ≤ (1 - (X - (⌊X⌋₊ : ℝ))) * b + (X - (⌊X⌋₊ : ℝ)) * b := add_le_add h1 h2
    _ = b := by ring

/-- `‖a - b/2 - c/2‖ ≤ B` from the two increments -/
theorem S7PIDP_Y_le (a b c : E) (B : ℝ) (h1 : ‖a - b‖ ≤ B) (h2 : ‖c - a‖ ≤ B) :
    ‖a - (1 / 2 : ℝ) • b - (1 / 2 : ℝ) • c‖ ≤ B := by
  have e : a - (1 / 2 : ℝ) • b - (1 / 2 : ℝ) • c = (1 / 2 : ℝ) • (a - b) + (1 / 2 : ℝ) • (a - c) := by
    module
  rw [e]
  have h2' : ‖a - c‖ ≤ B := by rw [norm_sub_rev]; exact h2
  calc _ ≤ ‖(1 / 2 : ℝ) • (a - b)‖ + ‖(1 / 2 : ℝ) • (a - c)‖ := norm_add_le _ _
    _ = (1 / 2) * ‖a - b‖ + (1 / 2) * ‖a - c‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    _ ≤ B := by linarith

/-- the refinement estimate of the two-term formulas: level `2N` at position `2X` against level `N`
at position `X` with node values `v (2 i)` -/
theorem S7PIDP_diff_core (N : ℕ) (X : ℝ) (hX0 : 0 ≤ X) (hXN : X ≤ (N : ℝ)) (v : ℕ → E) (B : ℝ)
    (hB0 : 0 ≤ B) (hB : ∀ k < 2 * N, ‖v (k + 1) - v k‖ ≤ B) :
    ‖∑ i ∈ range (2 * N + 1), max 0 (1 - |2 * X - (i : ℝ)|) • v i -
        ∑ i ∈ range (N + 1), max 0 (1 - |X - (i : ℝ)|) • v (2 * i)‖ ≤ B := by
  have hjX : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le hX0
  have hXj : X < ((⌊X⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one X
  have hjN : ⌊X⌋₊ ≤ N := by
    have : ((⌊X⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) := hjX.trans hXN
    exact_mod_cast this
  have h1 := S7PIDP_hat_aux N ⌊X⌋₊ X hjX hXj hjN hXN (fun i => v (2 * i))
  rw [h1]
  rcases lt_or_ge (X - (⌊X⌋₊ : ℝ)) (1 / 2) with hθ | hθ
  · -- case A: the level-`2N` floor is `2j`
    have hA := S7PIDP_hat_aux (2 * N) (2 * ⌊X⌋₊) (2 * X) (by push_cast; linarith) (by push_cast; linarith)
      (by omega) (by push_cast; linarith) v
    rw [hA]
    push_cast
    have e : (1 - (2 * X - 2 * (⌊X⌋₊ : ℝ))) • v (2 * ⌊X⌋₊) + (2 * X - 2 * (⌊X⌋₊ : ℝ)) • v (2 * ⌊X⌋₊ + 1) -
        ((1 - (X - (⌊X⌋₊ : ℝ))) • v (2 * ⌊X⌋₊) + (X - (⌊X⌋₊ : ℝ)) • v (2 * (⌊X⌋₊ + 1))) =
        (2 * (X - (⌊X⌋₊ : ℝ))) • (v (2 * ⌊X⌋₊ + 1) - (1 / 2 : ℝ) • v (2 * ⌊X⌋₊) -
          (1 / 2 : ℝ) • v (2 * ⌊X⌋₊ + 1 + 1)) := by
      rw [show 2 * (⌊X⌋₊ + 1) = 2 * ⌊X⌋₊ + 1 + 1 by ring]
      module
    rw [e]
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ X - (⌊X⌋₊ : ℝ) by linarith) with h0 | h0
    · rw [← h0]; simp [hB0]
    · have hj1 : ⌊X⌋₊ < N := S7PIDP_floor_lt N X hX0 hXN h0
      have ha : ‖v (2 * ⌊X⌋₊ + 1) - v (2 * ⌊X⌋₊)‖ ≤ B := by
        have := hB (2 * ⌊X⌋₊) (by omega)
        simpa [two_mul] using this
      have hc : ‖v (2 * ⌊X⌋₊ + 1 + 1) - v (2 * ⌊X⌋₊ + 1)‖ ≤ B := hB (2 * ⌊X⌋₊ + 1) (by omega)
      have hY := S7PIDP_Y_le (v (2 * ⌊X⌋₊ + 1)) (v (2 * ⌊X⌋₊)) (v (2 * ⌊X⌋₊ + 1 + 1)) B ha hc
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * (X - (⌊X⌋₊ : ℝ)))]
      have hθ2 : 2 * (X - (⌊X⌋₊ : ℝ)) ≤ 1 := by linarith
      calc 2 * (X - (⌊X⌋₊ : ℝ)) * _ ≤ 1 * B := mul_le_mul hθ2 hY (norm_nonneg _) zero_le_one
        _ = B := one_mul B
  · -- case B: the level-`2N` floor is `2j+1`
    have hθ1 : X - (⌊X⌋₊ : ℝ) < 1 := by linarith [Nat.lt_floor_add_one X]
    have hj1 : ⌊X⌋₊ < N := S7PIDP_floor_lt N X hX0 hXN (by linarith)
    have hB' := S7PIDP_hat_aux (2 * N) (2 * ⌊X⌋₊ + 1) (2 * X) (by push_cast; linarith)
      (by push_cast; linarith) (by omega) (by push_cast; linarith) v
    rw [hB']
    push_cast
    have e : (1 - (2 * X - (2 * (⌊X⌋₊ : ℝ) + 1))) • v (2 * ⌊X⌋₊ + 1) +
        (2 * X - (2 * (⌊X⌋₊ : ℝ) + 1)) • v (2 * ⌊X⌋₊ + 1 + 1) -
        ((1 - (X - (⌊X⌋₊ : ℝ))) • v (2 * ⌊X⌋₊) + (X - (⌊X⌋₊ : ℝ)) • v (2 * (⌊X⌋₊ + 1))) =
        (2 * (1 - (X - (⌊X⌋₊ : ℝ)))) • (v (2 * ⌊X⌋₊ + 1) - (1 / 2 : ℝ) • v (2 * ⌊X⌋₊) -
          (1 / 2 : ℝ) • v (2 * ⌊X⌋₊ + 1 + 1)) := by
      rw [show 2 * (⌊X⌋₊ + 1) = 2 * ⌊X⌋₊ + 1 + 1 by ring]
      module
    rw [e]
    have ha : ‖v (2 * ⌊X⌋₊ + 1) - v (2 * ⌊X⌋₊)‖ ≤ B := by
      have := hB (2 * ⌊X⌋₊) (by omega)
      simpa [two_mul] using this
    have hc : ‖v (2 * ⌊X⌋₊ + 1 + 1) - v (2 * ⌊X⌋₊ + 1)‖ ≤ B := hB (2 * ⌊X⌋₊ + 1) (by omega)
    have hY := S7PIDP_Y_le (v (2 * ⌊X⌋₊ + 1)) (v (2 * ⌊X⌋₊)) (v (2 * ⌊X⌋₊ + 1 + 1)) B ha hc
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * (1 - (X - (⌊X⌋₊ : ℝ))))]
    have hθ2 : 2 * (1 - (X - (⌊X⌋₊ : ℝ))) ≤ 1 := by linarith
    calc 2 * (1 - (X - (⌊X⌋₊ : ℝ))) * _ ≤ 1 * B := mul_le_mul hθ2 hY (norm_nonneg _) zero_le_one
      _ = B := one_mul B

end HRS.MC.Sec7.S7PIDP

end
