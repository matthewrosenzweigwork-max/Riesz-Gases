import HRS.MS.S113X2C12

/-!
# S11.3 / S11.4 X2 wiring (worker S11W), C13: `r2_moving_Lp` and `r2_moving_moment_transfer` from the two remaining cores

The remaining analytic cores of S11.3 are
* `S113XQReg` (time regularity and extension of the moving reference `q_N^t`, jointly `C²`, near compact collision-free sets) and
* `S113XLiouville` (Pro D03: the pathwise flow/Jacobian bound propagating `ν_0 ≤ C₀ dx` to `ν_t ≤ B dx`).
With them `r2_moving_Lp` and `r2_moving_moment_transfer` hold with their frozen types.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S113X2C

open HRS HRS.Whole HRS.MS.S113BD

variable {d : ℕ}

theorem s113c_cores_tuple (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀)
    (hLiou : S113XLiouville d s q β)
    (hQReg : ∀ (j m : ℕ) (εstar r c₀ : ℝ), S113XQReg d s q β ρ₀ j m εstar r c₀) :
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
  exact s113c_localized_of_cores hd hs0 hs hβ hq hρ hC₁ hc₀ hNL hLiou (hQReg _ _ _ _ _)

theorem s113c_r2_moving_Lp_of_cores (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (β q : ℝ)
    (hβ : 0 < β) (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) (γ : ℝ) (hγ : 0 ≤ γ)
    (hγs : 0 < s → 0 < γ) (hLiou : S113XLiouville d s q β)
    (hQReg : ∀ (j m : ℕ) (εstar r c₀ : ℝ), S113XQReg d s q β ρ₀ j m εstar r c₀) :
    type_of% (HRS.Whole.r2_moving_Lp hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs) :=
  s113c_r2_moving_Lp_of_X2 hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs
    (s113c_cores_tuple hd s hs0 hs β q hβ hq ρ₀ hρ hLiou hQReg)

theorem s113c_r2_moving_moment_transfer_of_cores (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (β q : ℝ) (hβ : 0 < β) (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) (γ : ℝ)
    (hγ : 0 ≤ γ) (hγs : 0 < s → 0 < γ) (hLiou : S113XLiouville d s q β)
    (hQReg : ∀ (j m : ℕ) (εstar r c₀ : ℝ), S113XQReg d s q β ρ₀ j m εstar r c₀) :
    type_of% (HRS.Whole.r2_moving_moment_transfer hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs) :=
  s113c_r2_moving_moment_transfer_of_X2 hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs
    (s113c_cores_tuple hd s hs0 hs β q hβ hq ρ₀ hρ hLiou hQReg)

end HRS.MS.S113X2C

end
