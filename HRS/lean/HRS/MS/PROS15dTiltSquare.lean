import HRS.MS.PROS15dActualSpectral
import HRS.MS.S21H2_S15c

/-!
# R26-T3.S15d: square integrability of the unnormalized Gaussian tilt

The canonical second-chaos Hilbert–Schmidt quadratic is independent (up to
almost-sure equality) of the nonnegative tilt parameter. Apply the previously
proved Gaussian tilt theorem at twice the parameter and identify its random
variable with that at the original parameter using uniqueness of L2 limits.
This yields the second exponential moment needed for Hölder estimates under
the tilted probability law.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

theorem s15d_actual_tilt_square_integrable
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → ℝ) (hξ : HRS.IsStdGaussianSeq P ξ)
    (lam : ℕ → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (hlam2 : Summable (fun j => lam j ^ 2))
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ Q : Ω → ℝ,
      HRS.TendstoL2 P (fun n ω =>
        (1 / 2 : ℝ) * ∑ j ∈ Finset.range n, lam j * (ξ j ω ^ 2 - 1)) Q ∧
      Integrable (fun ω => Real.exp (-γ * Q ω)) P ∧
      Integrable (fun ω => Real.exp (-(2 * γ) * Q ω)) P := by
  obtain ⟨Q, hT, hI, _, _⟩ :=
    r26t3_hs_gaussian_tilt P ξ hξ lam hlam hlam2 γ hγ
  have h2γ : 0 ≤ 2 * γ := by positivity
  obtain ⟨Q2, hT2, hI2, _, _⟩ :=
    r26t3_hs_gaussian_tilt P ξ hξ lam hlam hlam2 (2 * γ) h2γ
  have hmeas : ∀ n, AEStronglyMeasurable (s21h2_s15c_Qn ξ lam n) P :=
    fun n => (s21h2_s15c_aemeas_Qn hξ lam n).aestronglyMeasurable
  have hQeq : Q =ᵐ[P] Q2 := by
    exact HRS.TendstoL2.ae_unique hmeas hT hT2
  have hI2' : Integrable (fun ω => Real.exp (-(2 * γ) * Q ω)) P := by
    apply hI2.congr
    filter_upwards [hQeq.symm] with ω hw
    simp only [hw]
  exact ⟨Q, hT, hI, hI2'⟩

end HRS.MS.R26T3
