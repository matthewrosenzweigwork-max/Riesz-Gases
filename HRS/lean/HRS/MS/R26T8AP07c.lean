import HRS.MS.R26T8AP07b

/-!
# S8.2 local Newton layer, packet T8A.P07 (part c): dyadic head sums for exponents `0` and `> 0`
-/

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace HRS.MS.R26T8A

theorem r26t8a_p07_head_zero (c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → s ≤ 1 →
      ∑' n : ℕ, (if s < ((1 : ℝ) / 2) ^ n then (((1 : ℝ) / 2) ^ n) ^ (0 : ℝ) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ c else 0) ≤
        C * (1 + |Real.log s|) ^ (c + 1) := by
  refine ⟨2 * 2 ^ (c + 1), by positivity, fun s hs hs1 => ?_⟩
  obtain ⟨N, hN1, hN2⟩ := r26t8a_p07_first s hs
  obtain ⟨hlN, -⟩ := r26t8a_p07_N_bound hs hs1 hN1 hN2
  rw [r26t8a_p07_head_support 0 c s hs hN2 hN1]
  have hl2 : (1 : ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlpos : 0 < 1 + |Real.log (((1 : ℝ) / 2) ^ N)| := by positivity
  have hNle : (N : ℝ) ≤ 2 * (1 + |Real.log (((1 : ℝ) / 2) ^ N)|) := by
    rw [r26t8a_p07_log_u, abs_of_nonpos (by nlinarith [Nat.cast_nonneg (α := ℝ) N, Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)])]
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have hterm : ∀ n ∈ Finset.range N, (((1 : ℝ) / 2) ^ n) ^ (0 : ℝ) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ c ≤
      (2 * (1 + |Real.log s|)) ^ c := fun n hn => by
    rw [Real.rpow_zero, one_mul]
    refine pow_le_pow_left₀ (by positivity) (le_trans ?_ hlN) c
    rw [r26t8a_p07_log_u, r26t8a_p07_log_u, abs_of_nonpos (by nlinarith [Nat.cast_nonneg (α := ℝ) N, Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]),
      abs_of_nonpos (by nlinarith [Nat.cast_nonneg (α := ℝ) n, Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)])]
    have : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.1 hn).le
    nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]
  calc ∑ n ∈ Finset.range N, (((1 : ℝ) / 2) ^ n) ^ (0 : ℝ) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ c
      ≤ ∑ n ∈ Finset.range N, (2 * (1 + |Real.log s|)) ^ c := Finset.sum_le_sum hterm
    _ = (N : ℝ) * (2 * (1 + |Real.log s|)) ^ c := by simp
    _ ≤ (2 * (2 * (1 + |Real.log s|))) * (2 * (1 + |Real.log s|)) ^ c := by
        refine mul_le_mul_of_nonneg_right (le_trans hNle (by linarith)) (by positivity)
    _ = 2 * 2 ^ (c + 1) * (1 + |Real.log s|) ^ (c + 1) := by rw [pow_succ, pow_succ, mul_pow]; ring

theorem r26t8a_p07_head_pos (a : ℝ) (ha : 0 < a) (c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → s ≤ 1 →
      ∑' n : ℕ, (if s < ((1 : ℝ) / 2) ^ n then (((1 : ℝ) / 2) ^ n) ^ a * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ c else 0) ≤ C := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_p07_tail a ha c
  refine ⟨C, hC0, fun s hs hs1 => ?_⟩
  obtain ⟨hsm, hle⟩ := hC 1 one_pos le_rfl
  simp only [Real.log_one, abs_zero, add_zero, one_pow, mul_one, Real.one_rpow, pow_zero] at hle
  have hall : ∀ n : ℕ, ((1 : ℝ) / 2) ^ n ≤ 1 := fun n => pow_le_one₀ (by norm_num) (by norm_num)
  have e : ∀ n : ℕ, (if ((1 : ℝ) / 2) ^ n ≤ 1 then (((1 : ℝ) / 2) ^ n) ^ a * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ c else 0) =
      (((1 : ℝ) / 2) ^ n) ^ a * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ c := fun n => by rw [if_pos (hall n)]
  simp only [e] at hsm hle
  refine le_trans ?_ hle
  have hsm2 : Summable (fun n : ℕ => if s < ((1 : ℝ) / 2) ^ n then (((1 : ℝ) / 2) ^ n) ^ a *
      (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ c else 0) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      (fun n => by split_ifs <;> first | exact le_rfl | positivity) hsm
  refine Summable.tsum_le_tsum (fun n => ?_) hsm2 hsm
  split_ifs <;> first | exact le_rfl | positivity

end HRS.MS.R26T8A
