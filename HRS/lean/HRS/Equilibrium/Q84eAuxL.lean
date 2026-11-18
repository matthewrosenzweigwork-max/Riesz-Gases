/-
# HRS.Equilibrium.Q84eAuxL — packet Q84e: elementary arithmetic of the final constants
-/
import HRS.Equilibrium.Q84eAuxK

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84e

theorem q84e_logEN_eq {N : ℕ} (hN : 1 ≤ N) : logEN N = 1 + Real.log N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  unfold logEN
  rw [Real.log_mul (Real.exp_pos 1).ne' hNp.ne', Real.log_exp]

theorem q84e_logEN_le {N : ℕ} (hN : 1 ≤ N) : logEN N ≤ N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [q84e_logEN_eq hN]
  have := Real.log_le_sub_one_of_pos hNp
  linarith

theorem q84e_logEN_le_sqrt {N : ℕ} (hN : 1 ≤ N) : logEN N ≤ 2 * Real.sqrt N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
  rw [q84e_logEN_eq hN]
  have h1 := Real.log_le_sub_one_of_pos hr
  have h2 : Real.log (Real.sqrt N) = Real.log N / 2 := Real.log_sqrt hNp.le
  linarith

theorem q84e_logEN_pos {N : ℕ} (hN : 1 ≤ N) : 0 < logEN N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [q84e_logEN_eq hN]
  have : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  linarith

theorem q84e_rpow_neg_half {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.rpow_neg hNp.le, ← Real.sqrt_eq_rpow]
  simp

/-- The final arithmetic: all error contributions are `≤ C (K₁ + D) N^{-1/2}`. -/
theorem q84e_arith {N : ℕ} (hN : 1 ≤ N) {c K cu D z : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K) (hcu : 0 ≤ cu)
    (hD : 0 ≤ D) (hz : 0 ≤ z) :
    Real.sqrt (c ^ 2 * K ^ 2 / N) + Real.sqrt (c ^ 2 * K ^ 2 / N) +
      (|2 / (N : ℝ)| * Real.sqrt (c ^ 2 * K ^ 2 * logEN N / N) +
        Real.sqrt (c ^ 2 * (cu * K) ^ 2 * logEN N ^ 2 / (N : ℝ) ^ 2) +
        Real.sqrt (c ^ 2 * (cu * K) ^ 2 / N)) + z * D * (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      (4 * c + 3 * c * cu + z) * (K + D) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
  have hrr : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNp.le
  have hL := q84e_logEN_le hN
  have hL2 := q84e_logEN_le_sqrt hN
  have hL0 := q84e_logEN_pos hN
  rw [q84e_rpow_neg_half hN]
  set r := Real.sqrt N with hrdef
  set L := logEN N with hLdef
  have hr1 : 1 ≤ r := by
    rw [hrdef]; exact Real.one_le_sqrt.2 (by exact_mod_cast hN)
  have hsq : ∀ x : ℝ, (x / r) ^ 2 = x ^ 2 / N := by
    intro x; rw [div_pow, hrdef, Real.sq_sqrt hNp.le]
  -- s1
  have s1 : Real.sqrt (c ^ 2 * K ^ 2 / N) = c * K / r := by
    rw [show c ^ 2 * K ^ 2 / (N : ℝ) = (c * K / r) ^ 2 by rw [hsq, mul_pow]]
    exact Real.sqrt_sq (by positivity)
  -- s4
  have s4 : Real.sqrt (c ^ 2 * (cu * K) ^ 2 / N) = c * cu * K / r := by
    rw [show c ^ 2 * (cu * K) ^ 2 / (N : ℝ) = (c * cu * K / r) ^ 2 by
      rw [hsq]; ring]
    exact Real.sqrt_sq (by positivity)
  -- s2
  have s2 : Real.sqrt (c ^ 2 * K ^ 2 * L / N) ≤ c * K := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hNp]
    have : c ^ 2 * K ^ 2 * L ≤ c ^ 2 * K ^ 2 * N := mul_le_mul_of_nonneg_left hL (by positivity)
    nlinarith
  -- s3
  have s3 : Real.sqrt (c ^ 2 * (cu * K) ^ 2 * L ^ 2 / (N : ℝ) ^ 2) ≤ 2 * c * cu * K / r := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have hL4 : L ^ 2 ≤ 4 * N := by nlinarith
    have h5 : 0 ≤ c ^ 2 * (cu * K) ^ 2 := by positivity
    rw [hsq, div_le_div_iff₀ (by positivity) hNp]
    have h6 := mul_le_mul_of_nonneg_left hL4 h5
    nlinarith [mul_nonneg h5 hNp.le]
  have hrinv : 0 < 1 / r := by positivity
  have h2N : |2 / (N : ℝ)| ≤ 2 / r := by
    rw [abs_of_pos (by positivity)]
    refine div_le_div_of_nonneg_left (by norm_num) hr ?_
    nlinarith
  rw [s1, s4]
  have hb2 : |2 / (N : ℝ)| * Real.sqrt (c ^ 2 * K ^ 2 * L / N) ≤ 2 / r * (c * K) :=
    mul_le_mul h2N s2 (Real.sqrt_nonneg _) (by positivity)
  have hz2 : 0 ≤ z * D / r := by positivity
  have e1 : 2 / r * (c * K) = 2 * c * K / r := by ring
  have key : c * K / r + c * K / r + (2 * c * K / r + 2 * c * cu * K / r + c * cu * K / r) +
      z * D / r ≤ (4 * c + 3 * c * cu + z) * (K + D) / r := by
    rw [← sub_nonneg]
    have : (4 * c + 3 * c * cu + z) * (K + D) / r -
        (c * K / r + c * K / r + (2 * c * K / r + 2 * c * cu * K / r + c * cu * K / r) + z * D / r) =
        (z * K + 4 * c * D + 3 * c * cu * D) / r := by ring
    rw [this]; positivity
  calc _ ≤ c * K / r + c * K / r + (2 * c * K / r + 2 * c * cu * K / r + c * cu * K / r) +
        z * D / r := by
        rw [show z * D * (1 / r) = z * D / r by ring]
        have := hb2
        rw [e1] at this
        linarith
    _ ≤ (4 * c + 3 * c * cu + z) * (K + D) / r := key
    _ = _ := by ring

end HRS.Q84e

end
