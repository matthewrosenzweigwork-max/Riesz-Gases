import HRS.Commutator.Whole.XNRSAux30

/-!
# Packet X-NRS, part 31: the bound for a Schwartz `a` and smooth `v`
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

lemma xfourierL2_eq {a : Euc d → ℝ} {φ : 𝓢(Euc d, ℂ)} (ha : ∀ x, φ x = (a x : ℂ)) :
    HRS.PDE.ToolboxRd.fourierL2 a =ᵐ[volume] fun ξ => 𝓕 φ ξ := by
  set u : SchwartzMap (Euc d) ℝ := φ.postcompCLM (𝕜 := ℝ) Complex.reCLM with hu
  have hua : ∀ x, u x = a x := fun x => by
    simp only [hu, SchwartzMap.postcompCLM_apply, Complex.reCLM_apply, ha, Complex.ofReal_re]
  have h1 : (⇑u : Euc d → ℝ) = a := funext hua
  have h2 : (fun x : Euc d => ((a x : ℝ) : ℂ)) = ⇑φ := by
    funext x; rw [ha]
  have := HRS.PDE.ToolboxRd.FourierAux.fourierL2_schwartz u
  rw [h1, h2] at this
  filter_upwards [this] with ξ hξ
  rw [hξ]; rfl

lemma xinteg_neg {ρ : Euc d → ℝ} (hρ : XGoodCut ρ) {h : 𝓢(Euc d, ℂ)} (hh : XInD ρ h) {β : ℝ}
    (hβ : β ≤ 0) :
    Integrable (fun ξ : Euc d => (2 * Real.pi * ‖ξ‖) ^ (2 * β) * ‖𝓕 h ξ‖ ^ 2) := by
  obtain ⟨ε, hε, hz⟩ := xInD_fourier_zero_near hρ hh
  have hint : Integrable (fun ξ : Euc d => (2 * Real.pi * ε) ^ (2 * β) * ‖𝓕 h ξ‖ ^ 2) :=
    (integrable_fourier_norm_sq h).const_mul _
  refine hint.mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · exact (((measurable_const.mul measurable_norm).pow_const _).mul
      ((𝓕 h).continuous.norm.measurable.pow_const 2)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    by_cases hξ : ‖ξ‖ < ε
    · rw [hz ξ hξ]; simp
    · push Not at hξ
      have hpos : 0 < 2 * Real.pi * ε := by positivity
      have : (2 * Real.pi * ‖ξ‖) ^ (2 * β) ≤ (2 * Real.pi * ε) ^ (2 * β) :=
        Real.rpow_le_rpow_of_nonpos hpos (by gcongr) (by linarith)
      exact mul_le_mul_of_nonneg_right this (by positivity)

lemma xhom_ofReal_le {ρ : Euc d → ℝ} (hρ : XGoodCut ρ) {h φ : 𝓢(Euc d, ℂ)} (hh : XInD ρ h) {β : ℝ}
    (hβ : β ≤ 0) (hle : ∀ ξ, ‖𝓕 h ξ‖ ≤ ‖𝓕 φ ξ‖) {a : Euc d → ℝ} (ha : ∀ x, φ x = (a x : ℂ)) :
    ENNReal.ofReal (xhom β h) ≤ HRS.Commutator.Whole.homSqE β (HRS.PDE.ToolboxRd.fourierL2 a) := by
  unfold xhom
  rw [ofReal_integral_eq_lintegral_ofReal (xinteg_neg hρ hh hβ)
    (Eventually.of_forall fun ξ => by positivity)]
  unfold HRS.Commutator.Whole.homSqE
  refine lintegral_mono_ae ?_
  filter_upwards [xfourierL2_eq ha] with ξ hξ
  rw [hξ, ENNReal.ofReal_mul (by positivity)]
  gcongr
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hle ξ) 2)

end HRS.Commutator.Whole.XNRS
