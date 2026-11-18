import HRS.MS.S82VS1
import HRS.MS.S82VS2
import HRS.MS.S82VL1

/-!
# S8.2 A02 (S82V), part 8: stationarity of the mean-field generator against a row of `Q`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82V
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

lemma s82v_wd_integrable_iff {rho : Euc d → ℝ} (hρ : Measurable rho) (hρ0 : ∀ x, 0 ≤ rho x)
    (g : Euc d → ℝ) :
    Integrable g (HRS.Whole.withDensityReal rho) ↔ Integrable (fun x => rho x * g x) := by
  unfold HRS.Whole.withDensityReal
  rw [integrable_withDensity_iff_integrable_smul' (f := fun x => ENNReal.ofReal (rho x)) (ENNReal.measurable_ofReal.comp hρ : Measurable fun x => ENNReal.ofReal (rho x))
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integrable_congr (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (hρ0 x)]

lemma s82v_wd_integral {rho : Euc d → ℝ} (hρ : Measurable rho) (hρ0 : ∀ x, 0 ≤ rho x)
    (g : Euc d → ℝ) :
    ∫ x, g x ∂(HRS.Whole.withDensityReal rho) = ∫ x, rho x * g x := by
  unfold HRS.Whole.withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul (f := fun x => ENNReal.ofReal (rho x)) (ENNReal.measurable_ofReal.comp hρ : Measurable fun x => ENNReal.ofReal (rho x))
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (hρ0 x)]

end HRS.MS.S82V

end
