import HRS.Commutator.Whole.INHOMAux9

/-!
# CMX-INHOM auxiliary 10: `Ḣ^{-α}` and `H^{-α}` norms of the high-frequency part `a₁`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

lemma inhom_one_sub_gL (ξ : Euc d) :
    ‖1 - cmxFB_gL d (1 / 16) ξ‖ ≤ 1 ∧ (‖ξ‖ ≤ 1 / 16 → 1 - cmxFB_gL d (1 / 16) ξ = 0) := by
  have hchi0 := cmxFB_chi_nonneg ((1 / 16 : ℝ)⁻¹ • ξ)
  have hchi1 := cmxFB_chi_le_one ((1 / 16 : ℝ)⁻¹ • ξ)
  have e : 1 - cmxFB_gL d (1 / 16) ξ = ((1 - chi ((1 / 16 : ℝ)⁻¹ • ξ) : ℝ) : ℂ) := by
    unfold cmxFB_gL; push_cast; ring
  rw [e]
  refine ⟨?_, fun h => ?_⟩
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  · have : chi ((1 / 16 : ℝ)⁻¹ • ξ) = 1 := by
      apply cmxFB_chi_one
      rw [norm_smul, norm_inv, Real.norm_of_nonneg (by norm_num)]
      linarith
    rw [this]; simp

lemma inhom_hom_le {α : ℝ} (hα : 0 < α) {φ : SchwartzMap (Euc d) ℂ} (G : Euc d → ℂ)
    (hG : ∀ ξ, ‖G ξ‖ ≤ ‖1 - cmxFB_gL d (1 / 16) ξ‖ * ‖𝓕 (⇑φ) ξ‖) :
    homSqE (-α) G ≤ ENNReal.ofReal ((1 + 64 / Real.pi ^ 2) ^ α) * inhom_Sob (-α) φ := by
  unfold homSqE inhom_Sob
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ξ => ?_
  obtain ⟨h1, h2⟩ := inhom_one_sub_gL (d := d) ξ
  by_cases hξ : ‖ξ‖ ≤ 1 / 16
  · have : G ξ = 0 := by
      have := hG ξ
      rw [h2 hξ, norm_zero, zero_mul] at this
      exact norm_le_zero_iff.1 this
    rw [this]; simp
  · push Not at hξ
    have hw := inhom_w1 hα ξ hξ.le
    have hn : ‖G ξ‖ ≤ ‖𝓕 (⇑φ) ξ‖ := (hG ξ).trans (by
      calc ‖1 - cmxFB_gL d (1 / 16) ξ‖ * ‖𝓕 (⇑φ) ξ‖ ≤ 1 * ‖𝓕 (⇑φ) ξ‖ := by gcongr
        _ = _ := one_mul _)
    calc ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ (2 * (-α))) * ‖G ξ‖ₑ ^ 2
        ≤ ENNReal.ofReal ((1 + 64 / Real.pi ^ 2) ^ α * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-α)) *
            ‖𝓕 (⇑φ) ξ‖ₑ ^ 2 := by
          gcongr
          exact enorm_le_iff_norm_le.2 hn
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity)]; ring

lemma inhom_sob_le {φ φ₁ : SchwartzMap (Euc d) ℂ} (t : ℝ)
    (h : ∀ ξ, 𝓕 (⇑φ₁) ξ = (1 - cmxFB_gL d (1 / 16) ξ) * 𝓕 (⇑φ) ξ) :
    inhom_Sob t φ₁ ≤ inhom_Sob t φ := by
  unfold inhom_Sob
  refine lintegral_mono fun ξ => ?_
  gcongr
  rw [enorm_le_iff_norm_le, h ξ, norm_mul]
  calc ‖1 - cmxFB_gL d (1 / 16) ξ‖ * ‖𝓕 (⇑φ) ξ‖ ≤ 1 * ‖𝓕 (⇑φ) ξ‖ := by
        gcongr; exact (inhom_one_sub_gL ξ).1
    _ = _ := one_mul _

end HRS.Commutator.Whole
