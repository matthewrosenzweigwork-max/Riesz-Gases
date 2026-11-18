import HRS.MS.S111K4G
import HRS.Whole.Round2

/-!
# S11.1 / T01 (S11K4), part H: `TendstoL2` as convergence of second moments; Bessel for an `L²` kernel
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace HRS.MS.S111K4

theorem k4_integral_sq_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f P) :
    ∫ ω, f ω ^ 2 ∂P = (∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂P).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => sq_nonneg _) (hf.pow 2)]
  congr 1
  refine lintegral_congr fun ω => ?_
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- `TendstoL2` together with `L²` membership gives convergence of the second moments of the differences. -/
theorem k4_tendsto_int {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Qn : ℕ → Ω → ℝ) (Q : Ω → ℝ) (hQn : ∀ n, MemLp (Qn n) 2 P) (hQ : MemLp Q 2 P)
    (h : HRS.TendstoL2 P Qn Q) :
    Tendsto (fun n => ∫ ω, (Qn n ω - Q ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have h2 : Tendsto (fun n => (∫⁻ ω, ‖Qn n ω - Q ω‖ₑ ^ 2 ∂P).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h.2
    simpa [Function.comp_def] using this
  refine h2.congr fun n => ?_
  exact (k4_integral_sq_eq P (fun ω => Qn n ω - Q ω) ((hQn n).sub hQ).aestronglyMeasurable).symm

end HRS.MS.S111K4
