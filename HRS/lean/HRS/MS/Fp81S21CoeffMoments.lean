import HRS.MS.Fp81S21HigherMoments
import HRS.MS.Fp81S21NoisePath6
import HRS.MS.Fp81S21WeightedNorm2
import HRS.MS.Fp81S21WeightedMoments7

/-! Sixth moments of chart representatives, transferred from the weighted
negative Sobolev norm without identifying the two norm definitions. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6

/-- Transfer a sixth negative-Sobolev moment through an exact chart Riesz
representative. The constant `C` is the explicit comparison factor from
`dualNormE` to `r2NegSobNorm`. -/
theorem fp81s21_rep_sixthMoment
    {d r : ℕ} {Pw : ℝ} {S : Type*} [MeasurableSpace S]
    (E : r26t6_WeightedChart d r Pw) (P : Measure S)
    (T : S → (Euc d → ℝ) → ℝ) (z : S → r26t6_Coeff)
    (hz : Measurable z)
    (hrep : ∀ a, fp81s21_TestRep E (T a) (z a))
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ a, dualNormE r Pw (T a) ≤
      ENNReal.ofReal C * r2NegSobNorm r Pw (T a))
    (hL : (∫⁻ a, r2NegSobNorm r Pw (T a) ^ (6 : ℝ) ∂P) ≤ ENNReal.ofReal D) :
    fp81s21_Moment6 P z (C ^ 6 * D) := by
  have hpoint (a : S) :
      ENNReal.ofReal (‖z a‖ ^ 6) ≤
        ENNReal.ofReal (C ^ 6) * r2NegSobNorm r Pw (T a) ^ (6 : ℝ) := by
    have hdual : ENNReal.ofReal ‖z a‖ ≤
        ENNReal.ofReal C * r2NegSobNorm r Pw (T a) := by
      rw [← (hrep a).2.2]
      exact hb a
    have hpow := ENNReal.rpow_le_rpow hdual (by norm_num : (0 : ℝ) ≤ 6)
    have hleft : (ENNReal.ofReal ‖z a‖) ^ (6 : ℝ) =
        ENNReal.ofReal (‖z a‖ ^ 6) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
      exact congrArg ENNReal.ofReal (Real.rpow_natCast _ 6)
    have hCpow : (ENNReal.ofReal C) ^ (6 : ℝ) = ENNReal.ofReal (C ^ 6) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hC (by norm_num)]
      exact congrArg ENNReal.ofReal (Real.rpow_natCast C 6)
    have hright : (ENNReal.ofReal C * r2NegSobNorm r Pw (T a)) ^ (6 : ℝ) =
        ENNReal.ofReal (C ^ 6) * r2NegSobNorm r Pw (T a) ^ (6 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal C)
        (r2NegSobNorm r Pw (T a)) (by norm_num : (0 : ℝ) ≤ 6), hCpow]
    rw [hleft, hright] at hpow
    exact hpow
  have hnonneg : ∀ a, 0 ≤ ‖z a‖ ^ 6 := fun a => by positivity
  have hmeas : Measurable (fun a => ‖z a‖ ^ 6) :=
    (measurable_norm.comp hz).pow_const 6
  have hlin :
      (∫⁻ a, ENNReal.ofReal (‖z a‖ ^ 6) ∂P) ≤
        ENNReal.ofReal (C ^ 6 * D) := by
    calc
      _ ≤ ∫⁻ a, ENNReal.ofReal (C ^ 6) *
          r2NegSobNorm r Pw (T a) ^ (6 : ℝ) ∂P := lintegral_mono hpoint
      _ = ENNReal.ofReal (C ^ 6) *
          (∫⁻ a, r2NegSobNorm r Pw (T a) ^ (6 : ℝ) ∂P) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (C ^ 6) * ENNReal.ofReal D :=
        mul_le_mul_right hL _
      _ = ENNReal.ofReal (C ^ 6 * D) := by
        rw [ENNReal.ofReal_mul (by positivity)]
  have hi : Integrable (fun a => ‖z a‖ ^ 6) P := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnonneg)]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  have hIntegralENN :
      (∫⁻ a, ENNReal.ofReal (‖z a‖ ^ 6) ∂P) =
        ENNReal.ofReal (∫ a, ‖z a‖ ^ 6 ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall hnonneg)).symm
  have hreal : ENNReal.ofReal (∫ a, ‖z a‖ ^ 6 ∂P) ≤
      ENNReal.ofReal (C ^ 6 * D) := by
    rw [← hIntegralENN]
    exact hlin
  refine ⟨hz.aemeasurable, hi, ?_⟩
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hreal

#print axioms HRS.Fp81.S21.fp81s21_rep_sixthMoment

end HRS.Fp81.S21

end
