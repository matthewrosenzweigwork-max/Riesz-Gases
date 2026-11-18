import HRS.MS.S82WR2

/-!
# S8.2 A05 (S82W), part 10: `L²` bound of the centered error statistic
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82W
open HRS HRS.Whole HRS.MS.Phase2S82

lemma w_sqrt_le {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y ^ 2) : Real.sqrt x ≤ y :=
  Real.sqrt_le_iff.2 ⟨hy, h⟩

/-- the three real numerical inequalities used for the error statistic -/
lemma w_err_numbers {N : ℕ} (hN : 2 ≤ N) {C6 C7 CA B : ℝ} (hC6 : 0 ≤ C6) (hC7 : 0 ≤ C7) (hCA : 0 ≤ CA)
    (hB : 0 ≤ B) :
    (2 / (N : ℝ)) * Real.sqrt (C6 * B ^ 2 * logN N / N) + Real.sqrt (C7 * (CA * B) ^ 2 * logN N ^ 2 / (N : ℝ) ^ 2) +
      Real.sqrt (C6 * B ^ 2 / N) ≤ ((3 * Real.sqrt C6 + 2 * Real.sqrt C7 * CA) * B) / Real.sqrt N := by
  have hN1 : 1 ≤ N := by omega
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hpos
  have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hpos.le
  have hL : logN N ≤ 2 * Real.sqrt N := w_logN_le N hN1
  have hL0 : 0 ≤ logN N := by
    unfold logN
    rw [Real.log_mul (Real.exp_pos 1).ne' hpos.ne', Real.log_exp]
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have := Real.log_nonneg this
    linarith
  have hsN : Real.sqrt N ≤ N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    nlinarith
  have h6 := Real.sq_sqrt hC6
  have h7 := Real.sq_sqrt hC7
  have h6' := Real.sqrt_nonneg C6
  have h7' := Real.sqrt_nonneg C7
  -- term 1
  have t1 : Real.sqrt (C6 * B ^ 2 * logN N / N) ≤ Real.sqrt C6 * B * Real.sqrt N := by
    refine w_sqrt_le (by positivity) ?_
    have : logN N ≤ (N : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith
    have e : (Real.sqrt C6 * B * Real.sqrt N) ^ 2 = C6 * B ^ 2 * N := by
      rw [mul_pow, mul_pow, h6, Real.sq_sqrt hpos.le]
    rw [e, div_le_iff₀ hpos]
    have : C6 * B ^ 2 * logN N ≤ C6 * B ^ 2 * (N * N) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
    nlinarith
  -- term 2
  have t2 : Real.sqrt (C7 * (CA * B) ^ 2 * logN N ^ 2 / (N : ℝ) ^ 2) ≤
      2 * Real.sqrt C7 * CA * B / Real.sqrt N := by
    refine w_sqrt_le (by positivity) ?_
    have e : (2 * Real.sqrt C7 * CA * B / Real.sqrt N) ^ 2 = 4 * C7 * (CA * B) ^ 2 / N := by
      rw [div_pow, mul_pow, mul_pow, mul_pow, h7, Real.sq_sqrt hpos.le]; ring
    rw [e, div_le_div_iff₀ (by positivity) hpos]
    have : logN N ^ 2 ≤ 4 * N := by nlinarith [Real.sqrt_nonneg (N : ℝ), mul_self_le_mul_self hL0 hL]
    have h4 : 0 ≤ C7 * (CA * B) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this h4]
  have t3 : Real.sqrt (C6 * B ^ 2 / N) = Real.sqrt C6 * B / Real.sqrt N := by
    rw [Real.sqrt_div' _ hpos.le, Real.sqrt_mul hC6, Real.sqrt_sq hB]
  have e1 : (2 / (N : ℝ)) * (Real.sqrt C6 * B * Real.sqrt N) = 2 * Real.sqrt C6 * B / Real.sqrt N := by
    generalize Real.sqrt N = r at hss hs ⊢
    rw [← hss]; field_simp
  calc (2 / (N : ℝ)) * Real.sqrt (C6 * B ^ 2 * logN N / N) + _ + _
      ≤ (2 / (N : ℝ)) * (Real.sqrt C6 * B * Real.sqrt N) + 2 * Real.sqrt C7 * CA * B / Real.sqrt N +
        Real.sqrt C6 * B / Real.sqrt N := by
        rw [t3]
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left t1 (by positivity)) t2) le_rfl
    _ = _ := by rw [e1]; ring

end HRS.MS.S82W
