import HRS.MS.PROS15EChaosHS

/-!
Independent nonauthor consumer for the five S15e Hilbert--Schmidt
second-chaos source declarations, pinned to author revision a2e363a59.
The final theorem is restated with its full hypothesis and conclusion;
this file is not a new assumption or a substitute for reviewing the proof.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS.MC.E213U13

theorem s15e_nonauthor_hs_consumer
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → ℝ) (hξ : IsStdGaussianSeq P ξ)
    (lam : ℕ → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (hlam2 : Summable (fun j => lam j ^ 2))
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ Q : Ω → ℝ,
      HRS.TendstoL2 P (s21h2_s15c_Qn ξ lam) Q ∧
      InQ2 hξ Q ∧
      Integrable (fun ω => Real.exp (-γ * Q ω)) P ∧
      Integrable (fun ω => Real.exp (-(2 * γ) * Q ω)) P ∧
      Tendsto (fun n => ∫ ω,
        (s21h2_s15c_Qn ξ lam n ω - Q ω) ^ 2
        ∂(r26t3_tilt P (fun ω => γ * Q ω))) atTop (𝓝 0) := by
  exact s15e_hs_spectral_tilted_sections_L2
    P ξ hξ lam hlam hlam2 γ hγ

#print axioms s15e_diagonal_sections_second_chaos
#print axioms s15e_second_chaos_tilted_second_bound
#print axioms s15e_second_chaos_tilted_second_convergence
#print axioms s15e_second_chaos_tilted_of_tendstoL2
#print axioms s15e_hs_spectral_tilted_sections_L2
#print axioms s15e_nonauthor_hs_consumer
end HRS.MS.R26T3
