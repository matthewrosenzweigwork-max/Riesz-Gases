import HRS.MS.S111X2Aux46

/-!
# S11.1 X2: packet H02 (`S11X2H02`) and clause (a) of `r2_tensor_relaxation`

The thermal reference is unique (`Mov0.mv0_rho_eq`), so the constant of `s111x2_H02_fixed` can be chosen before it.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace HRS.MS.S111X2

open HRS HRS.Whole

variable {d : ℕ}

/-- **H02.** -/
theorem s111x2_H02 (hd : 2 ≤ d) (s a β γ T lam : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a)
    (hβ : 0 < β) (hγ : 0 ≤ γ) (hT : 0 < T) (hlam : 0 < lam) : S11X2H02 d s a β γ T lam hT := by
  classical
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  by_cases hex : ∃ ρ₀ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ₀ ∧
      IsR2Poincare (HRS.Whole.withDensityReal ρ₀) lam
  · obtain ⟨ρ₀, h0, hP0⟩ := hex
    obtain ⟨B, hB, hfix⟩ := s111x2_H02_fixed hd s a β γ T lam hs0 hs ha hβ hγ hT hlam h0 hP0
    refine ⟨B, hB, fun ρ hρ hP Ω₁ Ω₂ _ _ P₁ P₂ _ _ Z₁ Z₂ hZ₁ hZ₂ u hu n M hM => ?_⟩
    have hρeq : ρ = ρ₀ :=
      (HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ).trans (HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ h0).symm
    subst hρeq
    exact hfix P₁ P₂ Z₁ Z₂ hZ₁ hZ₂ u hu n M hM
  · exact ⟨0, le_rfl, fun ρ hρ hP => absurd ⟨ρ, hρ, hP⟩ hex⟩

/-- **Clause (a) of `r2_tensor_relaxation`.** -/
theorem s111x2_clauseA (hd : 2 ≤ d) (s a β γ T lam : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a)
    (hβ : 0 < β) (hγ : 0 ≤ γ) (hT : 0 < T) (hlam : 0 < lam) :
    ∃ C : ℝ, ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ →
      IsR2Poincare (HRS.Whole.withDensityReal ρβ) lam → S11X2ClauseA d s a β γ T lam C ρβ :=
  s111x2_clauseA_of_H02 d s a β γ T lam hT (s111x2_H02 hd s a β γ T lam hs0 hs ha hβ hγ hT hlam)

end HRS.MS.S111X2
