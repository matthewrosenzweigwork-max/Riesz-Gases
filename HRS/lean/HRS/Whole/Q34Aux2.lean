import HRS.Whole.Q34Aux1

/-!
# Packet Q34, helper file 2: convolution against a bounded probability density
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace HRS.Whole.Q34

variable {d : ℕ}

theorem rieszKernel_eq {s : ℝ} (hs : s ≠ 0) (z : Euc d) : rieszKernel d s z = ‖z‖ ^ (-s) := by
  simp [rieszKernel, hs]

theorem measurable_rieszKernel {s : ℝ} (hs : s ≠ 0) : Measurable (rieszKernel d s) := by
  have : rieszKernel d s = fun z : Euc d => ‖z‖ ^ (-s) := funext (rieszKernel_eq hs)
  rw [this]
  exact measurable_norm.pow_const _

theorem sphereArea_nonneg (hd : 1 ≤ d) : 0 ≤ sphereArea d := by
  unfold sphereArea
  have : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity)
  positivity

theorem integrable_of_isProbDensity {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ) : Integrable ρ := by
  by_contra h
  have := hρ.integral_one
  rw [integral_undef h] at this
  exact zero_ne_one this

theorem isProbabilityMeasure_nu {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ) :
    IsProbabilityMeasure (withDensityReal ρ) := by
  refine ⟨?_⟩
  unfold withDensityReal
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have := ofReal_integral_eq_lintegral_ofReal (integrable_of_isProbDensity hρ)
    (Filter.Eventually.of_forall hρ.nonneg)
  rw [← this, hρ.integral_one]
  simp

theorem lintegral_nu {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ) (H : Euc d → ℝ≥0∞)
    (hH : Measurable H) :
    ∫⁻ z, H z ∂(withDensityReal ρ) = ∫⁻ z, ENNReal.ofReal (ρ z) * H z := by
  unfold withDensityReal
  rw [lintegral_withDensity_eq_lintegral_mul₀]
  · rfl
  · exact (hρ.measurable.ennreal_ofReal).aemeasurable
  · exact hH.aemeasurable

/-- The convolution of a nonnegative function with a bounded density is bounded by
`M` times its integral. -/
theorem lintegral_conv_le {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ) {M : ℝ}
    (hM : ∀ x, ρ x ≤ M) (H : Euc d → ℝ≥0∞) (hH : Measurable H) (y : Euc d) :
    ∫⁻ z, H (y - z) ∂(withDensityReal ρ) ≤ ENNReal.ofReal M * ∫⁻ w, H w := by
  have hm : Measurable (fun z => H (y - z)) := hH.comp (measurable_const.sub measurable_id)
  rw [lintegral_nu hρ (fun z => H (y - z)) hm]
  calc ∫⁻ z, ENNReal.ofReal (ρ z) * H (y - z)
      ≤ ∫⁻ z, ENNReal.ofReal M * H (y - z) := by
        refine lintegral_mono fun z => ?_
        gcongr
        exact hM z
    _ = ENNReal.ofReal M * ∫⁻ z, H (y - z) := lintegral_const_mul _ hm
    _ = ENNReal.ofReal M * ∫⁻ w, H w := by
        rw [lintegral_sub_left_eq_self (fun w => H w) y]


theorem lintegral_kernel_le (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) (y : Euc d) :
    ∫⁻ z, ENNReal.ofReal (‖y - z‖ ^ (-s)) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal (M * sphereArea d / ((d : ℝ) - s) + 1) := by
  have := isProbabilityMeasure_nu hρ
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  have hdm : 0 < (d : ℝ) - s := by linarith
  set H : Euc d → ℝ≥0∞ := (ball (0 : Euc d) 1).indicator (fun w => ENNReal.ofReal (‖w‖ ^ (-s)))
    with hH
  have hHm : Measurable H :=
    (Measurable.ennreal_ofReal (measurable_norm.pow_const _)).indicator measurableSet_ball
  have hpt : ∀ w : Euc d, ENNReal.ofReal (‖w‖ ^ (-s)) ≤ H w + 1 := by
    intro w
    by_cases hw : w ∈ ball (0 : Euc d) 1
    · simp [hH, hw]
    · have h1 : 1 ≤ ‖w‖ := by simpa using hw
      have : ‖w‖ ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
      calc ENNReal.ofReal (‖w‖ ^ (-s)) ≤ 1 := by
            simpa using ENNReal.ofReal_le_ofReal this
        _ ≤ H w + 1 := le_add_self
  calc ∫⁻ z, ENNReal.ofReal (‖y - z‖ ^ (-s)) ∂(withDensityReal ρ)
      ≤ ∫⁻ z, (H (y - z) + 1) ∂(withDensityReal ρ) := lintegral_mono fun z => hpt _
    _ = ∫⁻ z, H (y - z) ∂(withDensityReal ρ) + 1 := by
        rw [lintegral_add_right _ measurable_const]
        simp
    _ ≤ ENNReal.ofReal M * (∫⁻ w, H w) + 1 := by
        exact add_le_add (lintegral_conv_le hρ hM H hHm y) le_rfl
    _ = ENNReal.ofReal (M * sphereArea d / ((d : ℝ) - s) + 1) := by
        have h1 : ∫⁻ w, H w = ENNReal.ofReal (sphereArea d * (1 / ((d : ℝ) - s))) := by
          rw [hH, lintegral_indicator measurableSet_ball,
            lintegral_ball_rpow hd one_pos (by linarith)]
          simp
        rw [h1, ← ENNReal.ofReal_mul hM0, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add (by have := sphereArea_nonneg hd; positivity) zero_le_one]
        congr 2
        ring


theorem integrable_of_lintegral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : Measurable f) (h0 : ∀ z, 0 ≤ f z) {c : ℝ} (hc : 0 ≤ c)
    (h : ∫⁻ z, ENNReal.ofReal (f z) ∂μ ≤ ENNReal.ofReal c) :
    Integrable f μ ∧ ∫ z, f z ∂μ ≤ c := by
  have hlt : ∫⁻ z, ENNReal.ofReal (f z) ∂μ < ∞ := h.trans_lt ENNReal.ofReal_lt_top
  refine ⟨⟨hf.aestronglyMeasurable, ?_⟩, ?_⟩
  · have : ∀ z, ‖f z‖ₑ = ENNReal.ofReal (f z) := fun z => Real.enorm_eq_ofReal (h0 z)
    simp only [HasFiniteIntegral, this]
    exact hlt
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0) hf.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hc h

end HRS.Whole.Q34
