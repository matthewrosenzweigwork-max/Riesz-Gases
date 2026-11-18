import HRS.MS.S11Q2C7
import HRS.MS.S11Q2B4
import HRS.MS.S11Q2C3

/-!
# S11.3 / S11.4 (worker S11Q2), C8: the core `S113XLiouville` (Pro D03) and the ties to the frozen statements

`s11q2_liouville`: `S113XLiouville d s q β` for all `d, s, q, β`.
`s11q2_r2_moving_Lp_of_QReg`, `s11q2_r2_moving_moment_transfer_of_QReg`: the frozen types of `r2_moving_Lp` and `r2_moving_moment_transfer`
from the single remaining core `S11Q2QReg` (weak time regularity of the moving reference).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S11Q2

open HRS HRS.Whole HRS.MS.S113X2 HRS.MS.S113X2C

theorem s11q2_liouville (d : ℕ) (s q β : ℝ) : S113XLiouville d s q β := by
  intro hβ N hN Ω _ P _ X₀ W X hX D hD hDc hDfree chi hchim hchi0 hchi1 C0 hC0 T hT
  obtain ⟨bt, L, M, hL0, hM0, hL, hM, hbc, hbD⟩ := s11q2_cutoff_drift d N s q β hDc hDfree
  set n := Module.finrank ℝ (EucConfig d N)
  refine ⟨max C0 0 * (Real.exp (2 * L * T)) ^ n, by positivity, fun t ht => ?_⟩
  refine (s11q2_killed_le hX hD hL0 hM0 hL hM hbc hbD hchim hC0 ht).trans ?_
  refine Measure.le_iff.2 fun A hA => ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  have he : Real.exp (2 * L * t) ≤ Real.exp (2 * L * T) := Real.exp_le_exp.2 (by nlinarith [ht.2, hL0])
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Real.exp_pos _).le he n) (le_max_right _ _))) le_rfl

theorem s11q2_r2_moving_Lp_of_QReg {d : ℕ} (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (β q : ℝ)
    (hβ : 0 < β) (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) (γ : ℝ) (hγ : 0 ≤ γ)
    (hγs : 0 < s → 0 < γ)
    (hQReg : ∀ (j m : ℕ) (εstar r c₀ c C₁ : ℝ), S11Q2QReg d s q β ρ₀ j m εstar r c₀ c C₁) :
    type_of% (HRS.Whole.r2_moving_Lp hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs) :=
  s11q2_r2_moving_Lp_of_cores hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs (s11q2_liouville d s q β) hQReg

theorem s11q2_r2_moving_moment_transfer_of_QReg {d : ℕ} (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (β q : ℝ) (hβ : 0 < β) (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) (γ : ℝ)
    (hγ : 0 ≤ γ) (hγs : 0 < s → 0 < γ)
    (hQReg : ∀ (j m : ℕ) (εstar r c₀ c C₁ : ℝ), S11Q2QReg d s q β ρ₀ j m εstar r c₀ c C₁) :
    type_of% (HRS.Whole.r2_moving_moment_transfer hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs) :=
  s11q2_r2_moving_moment_transfer_of_cores hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs (s11q2_liouville d s q β) hQReg

end HRS.MS.S11Q2

end
