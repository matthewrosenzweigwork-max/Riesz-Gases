import HRS.MS.S11Q2B3

/-!
# S11.3 / S11.4 (worker S11Q2), B4: `r2_moving_Lp` and `r2_moving_moment_transfer` from the cores `S113XLiouville` and `S11Q2QReg`

Copy of S113X2C13 with the weak core `S11Q2QReg` (the moving reference only of class `C^{1,2}`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S11Q2

open HRS HRS.Whole HRS.MS.S113BD HRS.MS.S113X2C

variable {d : ℕ}

theorem s11q2_cores_tuple (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀)
    (hLiou : S113XLiouville d s q β)
    (hQReg : ∀ (j m : ℕ) (εstar r c₀ c C₁ : ℝ), S11Q2QReg d s q β ρ₀ j m εstar r c₀ c C₁) :
    ∃ j m : ℕ, 1 ≤ j ∧ (d : ℝ) / 2 + j + 6 < m ∧
      ∃ εstar r c₀ c C₁ : ℝ, S113XTupleOK d s q β ρ₀ j m εstar r c₀ c C₁ ∧
        S113XLocalizedI d s q β ρ₀ j m εstar r c₀ := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  set m : ℕ := ⌊(d : ℝ) / 2⌋₊ + 8 with hm
  have hmm : (d : ℝ) / 2 + (1 : ℕ) + 6 < m := by
    have := Nat.lt_floor_add_one ((d : ℝ) / 2)
    simp only [hm]; push_cast; linarith
  obtain ⟨εstar, r, c₀, c, C₁, hOK⟩ := s113x_tupleOK_exists hd hs0 hsd β q hβ hq 1 m le_rfl hmm ρ₀ hρ
  refine ⟨1, m, le_rfl, hmm, εstar, r, c₀, c, C₁, hOK, ?_⟩
  obtain ⟨-, -, hc₀, -, hC₁, hNL, -⟩ := hOK
  exact s11q2_localized_of_cores hd hs0 hs hβ hq hρ hC₁ hc₀ hNL hLiou (hQReg _ _ _ _ _ _ _)

theorem s11q2_r2_moving_Lp_of_cores (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (β q : ℝ)
    (hβ : 0 < β) (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) (γ : ℝ) (hγ : 0 ≤ γ)
    (hγs : 0 < s → 0 < γ) (hLiou : S113XLiouville d s q β)
    (hQReg : ∀ (j m : ℕ) (εstar r c₀ c C₁ : ℝ), S11Q2QReg d s q β ρ₀ j m εstar r c₀ c C₁) :
    type_of% (HRS.Whole.r2_moving_Lp hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs) :=
  s113c_r2_moving_Lp_of_X2 hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs
    (s11q2_cores_tuple hd s hs0 hs β q hβ hq ρ₀ hρ hLiou hQReg)

theorem s11q2_r2_moving_moment_transfer_of_cores (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (β q : ℝ) (hβ : 0 < β) (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) (γ : ℝ)
    (hγ : 0 ≤ γ) (hγs : 0 < s → 0 < γ) (hLiou : S113XLiouville d s q β)
    (hQReg : ∀ (j m : ℕ) (εstar r c₀ c C₁ : ℝ), S11Q2QReg d s q β ρ₀ j m εstar r c₀ c C₁) :
    type_of% (HRS.Whole.r2_moving_moment_transfer hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs) :=
  s113c_r2_moving_moment_transfer_of_X2 hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs
    (s11q2_cores_tuple hd s hs0 hs β q hβ hq ρ₀ hρ hLiou hQReg)

end HRS.MS.S11Q2

end
