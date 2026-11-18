import HRS.MS.PROS13CrossRankAdd
import HRS.MS.S21T4ProdBI

/-!
# Generic S13: actual squared-integral convergence is L² convergence

The precise bridge allows the existing Gaussian L² sum theorem to be applied
to distinct finite-rank approximations before their kernels are combined.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem pro_s13_tendstoL2_of_integral_sq
    (F : ℕ → Ω → ℝ) (Q : Ω → ℝ)
    (hF : ∀ j, MemLp (F j) 2 P) (hQ : MemLp Q 2 P)
    (hlim : Tendsto (fun j => ∫ ω, (F j ω - Q ω) ^ 2 ∂P)
      atTop (𝓝 0)) :
    TendstoL2 P F Q := by
  refine ⟨hQ.aestronglyMeasurable, ?_⟩
  have heq : ∀ j, (∫⁻ ω, ‖F j ω - Q ω‖ₑ ^ 2 ∂P) =
      ENNReal.ofReal (∫ ω, (F j ω - Q ω) ^ 2 ∂P) := by
    intro j
    have hi : Integrable (fun ω => (F j ω - Q ω) ^ 2) P :=
      ((hF j).sub hQ).integrable_sq
    rw [ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
    refine lintegral_congr fun ω => ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      Real.norm_eq_abs, sq_abs]
  simp_rw [heq]
  simpa using ENNReal.tendsto_ofReal hlim

end HRS.MS.R26T3
