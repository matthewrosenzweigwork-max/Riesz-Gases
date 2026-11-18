import HRS.MS.R2InterpAux72
import HRS.MS.R2S11Aux1
import HRS.MS.R2ChaosAux52

/-!
# S10.2 (worker S102), part 73: the frozen statement from the particle-side inputs

`r2_path_interpolation_of_part`: the conclusion of `HRS.Whole.r2_path_interpolation`, from the frozen hypotheses and the particle-side packet `S102Part`
(Itô representation F5, drift/covariance structure M1/M2, path facts M3), which is quantified over the filtration of `hreal.filtered`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ}

/-- Polynomial moments of a density in the form used by the rate bound. -/
theorem s102_mom_conv {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {a : ℝ}
    {C₀ c₀ : ℝ} (hG : HasR2GaussianUpper C₀ c₀ ρ) (ha : 0 ≤ a) :
    ∃ Mρ : ℝ, Integrable (fun x => ρ x * jbracket x ^ a) ∧ ∫ x, ρ x * jbracket x ^ a ≤ Mρ := by
  obtain ⟨C, hC⟩ := HRS.MS.R2Chaos.s94_moment_rpow hρ hG ha
  have hg0 : ∀ x : Euc d, 0 ≤ jbracket x ^ a := fun x =>
    Real.rpow_nonneg (Real.sqrt_nonneg _) a
  have hgm : Measurable (fun x : Euc d => jbracket x ^ a) := by
    unfold jbracket
    fun_prop
  have h1 : ∫⁻ y, ENNReal.ofReal (jbracket y ^ a) ∂(HRS.Whole.withDensityReal ρ) =
      ∫⁻ x, ENNReal.ofReal (ρ x * jbracket x ^ a) := by
    unfold HRS.Whole.withDensityReal
    have hf : Measurable (fun x => ENNReal.ofReal (ρ x)) := ENNReal.measurable_ofReal.comp hρ.measurable
    have hg : Measurable (fun y => ENNReal.ofReal (jbracket y ^ a)) := ENNReal.measurable_ofReal.comp hgm
    rw [lintegral_withDensity_eq_lintegral_mul (f := fun x => ENNReal.ofReal (ρ x))
      (g := fun y => ENNReal.ofReal (jbracket y ^ a)) volume hf hg]
    refine lintegral_congr fun x => ?_
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (hρ.nonneg x)]
  rw [h1] at hC
  have hint : Integrable (fun x => ρ x * jbracket x ^ a) := by
    refine ⟨(hρ.measurable.mul hgm).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ x, ‖ρ x * jbracket x ^ a‖ₑ = ∫⁻ x, ENNReal.ofReal (ρ x * jbracket x ^ a) := by
          refine lintegral_congr fun x => ?_
          rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ.nonneg x) (hg0 x))]
      _ ≤ ENNReal.ofReal C := hC
      _ < ⊤ := ENNReal.ofReal_lt_top
  refine ⟨max C 0, hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => mul_nonneg (hρ.nonneg x) (hg0 x))
    (hρ.measurable.mul hgm).aestronglyMeasurable]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hC
  rwa [ENNReal.toReal_ofReal'] at this

end HRS.MS.R2Interp

end
