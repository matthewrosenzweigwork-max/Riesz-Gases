import HRS.MS.Fp81S21WeightedGen4

/-! Weight monotonicity needed to assemble the B3 weighted generator estimate. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21

open HRS HRS.Whole

/-- Increasing the polynomial decay exponent decreases the weighted Sobolev norm. -/
theorem fp81s21_weightedSobolevE_mono_weight {d r : ℕ} {P P' : ℝ}
    (hPP' : P ≤ P') (f : Euc d → ℝ) :
    weightedSobolevE r P' f ≤ weightedSobolevE r P f := by
  unfold weightedSobolevE
  apply ENNReal.rpow_le_rpow ?_ (by norm_num)
  apply Finset.sum_le_sum
  intro j hj
  apply Finset.sum_le_sum
  intro i hi
  apply lintegral_mono
  intro x
  apply ENNReal.ofReal_le_ofReal
  have hweight : jbracket x ^ (-2 * P') ≤ jbracket x ^ (-2 * P) :=
    Real.rpow_le_rpow_of_exponent_le (HRS.MS.Who.who_one_le_jb x) (by nlinarith)
  exact mul_le_mul_of_nonneg_right hweight (sq_nonneg (partialDeriv i f x))

/-- A finite-norm weighted test remains a test after increasing the decay exponent. -/
theorem fp81s21_isR2WeightedTest_mono_weight {d r : ℕ} {P P' : ℝ}
    (hPP' : P ≤ P') {f : Euc d → ℝ}
    (hf : IsR2WeightedTest r P f) : IsR2WeightedTest r P' f := by
  refine ⟨hf.1, ?_⟩
  exact (fp81s21_weightedSobolevE_mono_weight hPP' f).trans_lt hf.2

#print axioms fp81s21_weightedSobolevE_mono_weight
#print axioms fp81s21_isR2WeightedTest_mono_weight

end HRS.Fp81.S21
