import HRS.Commutator.Whole.INHOMAux8

/-!
# CMX-INHOM auxiliary 9: Plancherel bounds for the pieces of the splitting
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

/-- The Sobolev quantity of a Schwartz function, directly on `𝓕 φ`. -/
def inhom_Sob (t : ℝ) (φ : SchwartzMap (Euc d) ℂ) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ t) * ‖𝓕 (⇑φ) ξ‖ₑ ^ 2

lemma inhom_sobSqE_eq {a : Euc d → ℝ} {φ : SchwartzMap (Euc d) ℂ}
    (hφ : ∀ x, φ x = ((a x : ℝ) : ℂ)) (t : ℝ) :
    sobSqE t (HRS.PDE.ToolboxRd.fourierL2 a) = inhom_Sob t φ := by
  unfold sobSqE inhom_Sob
  refine lintegral_congr_ae ?_
  filter_upwards [HRS.Commutator.Whole.XNRS.xfourierL2_eq hφ] with ξ hξ
  rw [hξ]
  have : (𝓕 φ : SchwartzMap (Euc d) ℂ) ξ = 𝓕 (⇑φ) ξ := by rw [SchwartzMap.fourier_coe]
  rw [this]

lemma inhom_homSqE_eq {a : Euc d → ℝ} {φ : SchwartzMap (Euc d) ℂ}
    (hφ : ∀ x, φ x = ((a x : ℝ) : ℂ)) (t : ℝ) :
    homSqE t (HRS.PDE.ToolboxRd.fourierL2 a) =
      ∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ (2 * t)) * ‖𝓕 (⇑φ) ξ‖ₑ ^ 2 := by
  unfold homSqE
  refine lintegral_congr_ae ?_
  filter_upwards [HRS.Commutator.Whole.XNRS.xfourierL2_eq hφ] with ξ hξ
  rw [hξ]
  have : (𝓕 φ : SchwartzMap (Euc d) ℂ) ξ = 𝓕 (⇑φ) ξ := by rw [SchwartzMap.fourier_coe]
  rw [this]

/-- Plancherel for Schwartz functions with the `ℕ`-exponent. -/
lemma inhom_plancherel (ψ : SchwartzMap (Euc d) ℂ) :
    ∫⁻ x, ‖ψ x‖ₑ ^ 2 = ∫⁻ ξ, ‖𝓕 (⇑ψ) ξ‖ₑ ^ 2 := by
  have h := SAMP2.lintegral_sq_fourier ψ
  simp only [ENNReal.rpow_two] at h
  exact h.symm

/-- `L²` bound of `ψ` with `𝓕ψ = m 𝓕φ` and `|m|² ≤ c W^{-α}`. -/
lemma inhom_sq_le_of_symbol {ψ φ : SchwartzMap (Euc d) ℂ} {m : Euc d → ℂ} {α c : ℝ}
    (hm : ∀ ξ, 𝓕 (⇑ψ) ξ = m ξ * 𝓕 (⇑φ) ξ)
    (hc : ∀ ξ, ‖m ξ‖ ^ 2 ≤ c * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-α)) :
    ∫⁻ x, ‖ψ x‖ₑ ^ 2 ≤ ENNReal.ofReal c * inhom_Sob (-α) φ := by
  rw [inhom_plancherel]
  unfold inhom_Sob
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ξ => ?_
  rw [hm ξ, enorm_mul, mul_pow, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  calc ENNReal.ofReal (‖m ξ‖ ^ 2) * ‖𝓕 (⇑φ) ξ‖ₑ ^ 2
      ≤ ENNReal.ofReal (c * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-α)) * ‖𝓕 (⇑φ) ξ‖ₑ ^ 2 := by
        gcongr; exact hc ξ
    _ = ENNReal.ofReal c * (ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-α)) *
          ‖𝓕 (⇑φ) ξ‖ₑ ^ 2) := by
        rcases le_or_gt 0 c with h0 | h0
        · rw [ENNReal.ofReal_mul h0]; ring
        · have : ENNReal.ofReal c = 0 := ENNReal.ofReal_of_nonpos h0.le
          have h2 : c * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-α) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg h0.le (Real.rpow_nonneg (by positivity) _)
          rw [this, ENNReal.ofReal_of_nonpos h2]; simp

/-- low-frequency part `φ₀`: `|gL|² ≤ c₀ W^{-α}`. -/
lemma inhom_gL_sq {α : ℝ} (hα : 0 < α) (ξ : Euc d) :
    ‖(cmxFB_gL d (1 / 16) ξ)‖ ^ 2 ≤
      (1 + Real.pi ^ 2 / 16) ^ α * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-α) := by
  have hchi0 := cmxFB_chi_nonneg ((1 / 16 : ℝ)⁻¹ • ξ)
  have hchi1 := cmxFB_chi_le_one ((1 / 16 : ℝ)⁻¹ • ξ)
  have hnorm : ‖cmxFB_gL d (1 / 16) ξ‖ = chi ((1 / 16 : ℝ)⁻¹ • ξ) := by
    unfold cmxFB_gL
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hchi0]
  rw [hnorm]
  by_cases hξ : ‖ξ‖ ≤ 1 / 8
  · have := inhom_w2 hα ξ hξ
    calc chi ((1 / 16 : ℝ)⁻¹ • ξ) ^ 2 ≤ 1 := by nlinarith
      _ ≤ _ := this
  · push Not at hξ
    have : chi ((1 / 16 : ℝ)⁻¹ • ξ) = 0 := by
      apply cmxFB_chi_zero
      rw [norm_smul, norm_inv, Real.norm_of_nonneg (by norm_num)]
      linarith
    rw [this]
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 by positivity) (-α)
    have h2 : (0 : ℝ) ≤ (1 + Real.pi ^ 2 / 16) ^ α :=
      Real.rpow_nonneg (by positivity) _
    nlinarith [mul_nonneg h2 this]

end HRS.Commutator.Whole
