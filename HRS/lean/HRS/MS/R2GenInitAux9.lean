import HRS.MS.R2GenInitAux8
import HRS.MS.WsStatAux2
import HRS.MP.SelfSimP4Gibbs

/-!
# S10.5 input `hmom` for the stationary trajectory

* `s105_exp_moment_gauss`: a probability density with `ρ ≤ C e^{-c|x|²}` has `∫ e^{(c/2)|x|²} ρ dx ≤ max 1 (C ∫ e^{-(c/2)|x|²})`.
* `s105_hmom_stat`: the uniform second-moment bound `C_m (1 + B_N/N)` along the stationary dynamics (clause `S105Moment`), from
  `s105_hent_stat`, `s105_kl_product` and `s105_second_moment_of_kl`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal

namespace HRS.MS.R2GenInit

open HRS.Whole HRS.MS.Wr

variable {d : ℕ}

theorem s105_exp_moment_gauss {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {C c : ℝ} (hC : 0 ≤ C)
    (hc : 0 < c) (hb : ∀ x, ρ x ≤ C * Real.exp (-(c * ‖x‖ ^ 2))) :
    ∫⁻ x, ENNReal.ofReal (Real.exp ((c / 2) * ‖x‖ ^ 2)) ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal (max 1 (C * ∫ x : Euc d, Real.exp (-((c / 2) * ‖x‖ ^ 2)))) := by
  unfold HRS.Whole.withDensityReal
  rw [lintegral_withDensity_eq_lintegral_mul volume (f := fun x => ENNReal.ofReal (ρ x))
    (ENNReal.measurable_ofReal.comp hρ.measurable) (by fun_prop)]
  have hg := HRS.MP.SelfSimP4Impl.p4g_integrable_gauss d (b := c / 2) (by positivity)
  calc ∫⁻ x : Euc d, ((fun x : Euc d => ENNReal.ofReal (ρ x)) *
          fun x : Euc d => ENNReal.ofReal (Real.exp ((c / 2) * ‖x‖ ^ 2))) x
      ≤ ∫⁻ x : Euc d, ENNReal.ofReal (C * Real.exp (-((c / 2) * ‖x‖ ^ 2))) := by
        refine lintegral_mono fun x => ?_
        simp only [Pi.mul_apply]
        rw [← ENNReal.ofReal_mul (hρ.nonneg x)]
        refine ENNReal.ofReal_le_ofReal ?_
        calc ρ x * Real.exp ((c / 2) * ‖x‖ ^ 2)
            ≤ C * Real.exp (-(c * ‖x‖ ^ 2)) * Real.exp ((c / 2) * ‖x‖ ^ 2) :=
              mul_le_mul_of_nonneg_right (hb x) (Real.exp_pos _).le
          _ = C * Real.exp (-((c / 2) * ‖x‖ ^ 2)) := by
              rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ = ENNReal.ofReal (C * ∫ x : Euc d, Real.exp (-((c / 2) * ‖x‖ ^ 2))) := by
        rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hg.const_mul C)
          (Filter.Eventually.of_forall fun x => mul_nonneg hC (Real.exp_pos _).le)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (le_max_right _ _)

end HRS.MS.R2GenInit
