import HRS.MS.S21T4ProdAI
import HRS.MS.S21T4ProdAB

/-! S13: exact L² norm of a pair-valued error whose first coordinate vanishes. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos

theorem s21t4_pair_second_lintegral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} (v : Ω → ℝ) (hv : MemLp v 2 P) :
    (∫⁻ ω, ‖(((0 : Fin n → ℝ), v ω))‖ₑ ^ 2 ∂P) =
      ENNReal.ofReal (∫ ω, v ω ^ 2 ∂P) := by
  have he : ∀ ω, ‖(((0 : Fin n → ℝ), v ω))‖ₑ = ‖v ω‖ₑ := by
    intro ω
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
    simp [Prod.norm_def]
  simp_rw [he]
  rw [ofReal_integral_eq_lintegral_ofReal hv.integrable_sq
    (Filter.Eventually.of_forall fun ω => sq_nonneg (v ω))]
  apply lintegral_congr
  intro ω
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  simp only [Real.norm_eq_abs, sq_abs]

end HRS.MS.R26T3
