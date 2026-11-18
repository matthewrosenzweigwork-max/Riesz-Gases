import HRS.MS.PROS15EChaosSections
import HRS.MS.PROS15EChaosTendstoL2
import HRS.MS.PROS15dTiltSquare

/-!
# Actual Hilbert--Schmidt spectral quadratic converges in tilted L²

The source and all approximants belong to the same second Gaussian chaos.
The nonnegative Hilbert--Schmidt spectral sequence supplies a square-integrable
exponential likelihood. Thus the actual diagonal quadratic has an L² limit
under its own normalized tilt, with no additional moment hypothesis.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS.MC.E213U13

theorem s15e_hs_spectral_tilted_sections_L2
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
  obtain ⟨Q, hT, hE1, hE2⟩ :=
    s15d_actual_tilt_square_integrable P ξ hξ lam hlam hlam2 γ hγ
  have hSections : ∀ n, InQ2 hξ (s21h2_s15c_Qn ξ lam n) :=
    s15e_diagonal_sections_second_chaos ξ hξ lam
  have hQ : InQ2 hξ Q := by
    apply InQ2.of_tendsto (l := atTop) (hξ := hξ) hSections hT.1
    have hp : ∀ x : ℝ≥0∞, x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
      intro x
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    simpa only [s21h2_s15c_Qn, hp] using hT.2
  have hV : AEMeasurable (fun ω => γ * Q ω) P :=
    hT.1.aemeasurable.const_mul γ
  have hE2' : Integrable (fun ω =>
      Real.exp (-(2 * (γ * Q ω)))) P := by
    convert hE2 using 1
    funext ω
    congr 1
    ring
  have hC := s15e_second_chaos_tilted_of_tendstoL2 P hV hE2'
      (s21h2_s15c_Qn ξ lam) Q hSections hQ hT
  exact ⟨Q, hT, hQ, hE1, hE2, hC⟩

#print axioms s15e_hs_spectral_tilted_sections_L2
end HRS.MS.R26T3
