import HRS.MS.S21T4ProdY
import HRS.MS.R2ChaosAux56

/-! Turning L²-kernel convergence into real second-moment convergence. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos

theorem s21t4_integral_sq_of_eLpNorm {α : Type*} [MeasurableSpace α]
    {ν : Measure α} (f : α → ℝ) (hf : MemLp f 2 ν) :
    (∫ x, f x ^ 2 ∂ν) = (eLpNorm f 2 ν).toReal ^ 2 := by
  have hi : Integrable (fun x => f x ^ 2) ν := hf.integrable_sq
  have h1 := s94_lintegral_sq_eq hf.aestronglyMeasurable
  have h2 : ENNReal.ofReal (∫ x, f x ^ 2 ∂ν) =
      ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => sq_nonneg _)]
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
      Real.norm_eq_abs, sq_abs]
  have h3 : ENNReal.ofReal (∫ x, f x ^ 2 ∂ν) = eLpNorm f 2 ν ^ 2 := h2.trans h1
  rw [← ENNReal.toReal_pow, ← h3,
    ENNReal.toReal_ofReal (integral_nonneg fun x => sq_nonneg _)]

theorem s21t4_integral_sq_tendsto_zero {α : Type*} [MeasurableSpace α]
    {ν : Measure α} (f : ℕ → α → ℝ)
    (hf : ∀ j, MemLp (f j) 2 ν)
    (hT : Tendsto (fun j => eLpNorm (f j) 2 ν) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, (f j x) ^ 2 ∂ν) atTop (𝓝 0) := by
  have hreal := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hT).pow 2
  simp_rw [s21t4_integral_sq_of_eLpNorm (f := f _) (hf _)]
  simpa [Function.comp_def] using hreal

end HRS.MS.R26T3
