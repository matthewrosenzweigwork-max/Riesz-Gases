import HRS.MS.S111X2Aux24
import HRS.MS.S111X1G2

/-!
# S11.1 X2: pair-level decay for oscillator test functions (existence discharged by `S111X1.exist_of_thermal`)
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set

namespace HRS.MS.S111X2

open HRS (Euc)
open HRS.Whole

variable {d : ℕ}

/-- **Pair-level sharp decay of the window-covariance difference for oscillator tests.** -/
theorem s111x2_pair_diff_osc (hd : 2 ≤ d) (s a β γ lam : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hβ : 0 < β) (hγ : 0 ≤ γ) (hlam : 0 < lam) :
    ∃ η : ℝ, 0 < η ∧ ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ →
      IsR2Poincare (HRS.Whole.withDensityReal ρ) lam →
      ∀ u : ℝ, 0 ≤ u → ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → ∀ (φ ψ : Euc d → ℝ),
        IsOscTest (wholeSpaceIndex d : ℝ) φ → IsOscTest (wholeSpaceIndex d : ℝ) ψ →
        |linearGaussianCov ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹
            (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ)
            (u + t₁) (u + t₂) φ ψ -
          linearGaussianCov ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹
            (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β)
            t₁ t₂ φ ψ| ≤
        2 * η⁻¹ * Real.exp (-2 * (lam / β) * u) *
          (Real.sqrt (s111x2_centeredSquare (HRS.Whole.withDensityReal ρ) φ) *
            Real.sqrt (s111x2_centeredSquare (HRS.Whole.withDensityReal ρ) ψ)) := by
  obtain ⟨η, hη, h⟩ := s111x2_pair_diff hd s a β γ lam hs0 hs ha hβ hγ hlam
  refine ⟨η, hη, fun ρ hρ hP u hu t₁ t₂ ht₁ ht₁₂ φ ψ hφ hψ => ?_⟩
  have hex := HRS.MS.S111X1.exist_of_thermal hd hs0 hs ha hβ hρ
  obtain ⟨f, hf⟩ := hex (u + t₁) (by linarith) φ hφ
  obtain ⟨g, hg⟩ := hex (u + t₂) (by linarith) ψ hψ
  exact h ρ hρ hP u hu t₁ t₂ ht₁ ht₁₂ φ ψ f g hf hg

end HRS.MS.S111X2
