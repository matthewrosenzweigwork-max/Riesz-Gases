import HRS.MS.Fp81S21WeightedRellich17
import HRS.MS.Fp81S21EmbedField

/-! The strong weighted test norm controls the weaker weighted test norm. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.FixEq

/-- Lowering the derivative order by two and raising the weight parameter by
two does not increase the weighted Sobolev norm. This is the identity-on-tests
bound needed for the primal inclusion. -/
theorem fp81s21_embedField_weightedTestNorm_le
    {d q : ℕ} {Pw : ℝ} (f : Euc d → ℝ) :
    weightedSobolevE q (Pw + 2) f ≤ weightedSobolevE (q + 2) Pw f := by
  rw [s57p_E_eq, s57p_E_eq]
  apply ENNReal.rpow_le_rpow
  · unfold s57pS
    have hsum :
      (∑ j ∈ Finset.range (q + 1), ∑ i : Fin j → Fin d,
        ∫⁻ x, ENNReal.ofReal
          (jbracket x ^ (-2 * (Pw + 2)) * (partialDeriv i f x) ^ 2)) ≤
      ∑ j ∈ Finset.range (q + 3), ∑ i : Fin j → Fin d,
        ∫⁻ x, ENNReal.ofReal
          (jbracket x ^ (-2 * Pw) * (partialDeriv i f x) ^ 2) := by
      calc
        _ ≤ ∑ j ∈ Finset.range (q + 1), ∑ i : Fin j → Fin d,
            ∫⁻ x, ENNReal.ofReal
              (jbracket x ^ (-2 * Pw) * (partialDeriv i f x) ^ 2) := by
          refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun i hi => ?_
          apply lintegral_mono
          intro x
          have hjb : 1 ≤ jbracket x := by
            unfold jbracket
            calc
              1 = Real.sqrt 1 := by simp
              _ ≤ Real.sqrt (1 + ‖x‖ ^ 2) :=
                Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖x‖])
          have hweight := fp81s21_weightedRellich_tail_weight
            (d := d) (Pw := Pw) (ρ := 1) (x := x) (by norm_num) hjb
          have hweight' : jbracket x ^ (-2 * (Pw + 2)) ≤
              jbracket x ^ (-2 * Pw) := by
            simpa using hweight
          exact ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right hweight' (sq_nonneg (partialDeriv i f x)))
        _ ≤ ∑ j ∈ Finset.range (q + 3), ∑ i : Fin j → Fin d,
            ∫⁻ x, ENNReal.ofReal
              (jbracket x ^ (-2 * Pw) * (partialDeriv i f x) ^ 2) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.2 (by omega)) ?_
          intro j hj hj'
          exact Finset.sum_nonneg fun i hi => bot_le
    exact hsum
  · norm_num

#print axioms HRS.Fp81.S21.fp81s21_embedField_weightedTestNorm_le

end HRS.Fp81.S21
