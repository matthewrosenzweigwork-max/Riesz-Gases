import Mathlib

/-!
# S11.1 / all-tests boundary (S111K4AT), piece B: convergence of integrals under a pointwise envelope

If `‖F_n - F‖ₑ ≤ N · e_n` a.e. with `N` measurable, `∫⁻ N < ∞`, `e_n → 0`, and `‖F‖ₑ ≤ N · c` (`c < ∞`), then `F` is integrable
and `∫ F_n → ∫ F`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S111K4AT

theorem k4at_int_limit {μ : Measure ℝ} {Fn : ℕ → ℝ → ℝ} {F : ℝ → ℝ} {N : ℝ → ℝ≥0∞} {e : ℕ → ℝ≥0∞}
    {c : ℝ≥0∞} (hNm : Measurable N) (hN : ∫⁻ r, N r ∂μ < ⊤) (hc : c ≠ ⊤) (he : Tendsto e atTop (𝓝 0))
    (hFn : ∀ n, AEStronglyMeasurable (Fn n) μ)
    (hdiff : ∀ᶠ n in atTop, ∀ᵐ r ∂μ, ‖Fn n r - F r‖ₑ ≤ N r * e n)
    (hFb : ∀ᵐ r ∂μ, ‖F r‖ₑ ≤ N r * c) :
    Integrable F μ ∧ Tendsto (fun n => ∫ r, Fn n r ∂μ) atTop (𝓝 (∫ r, F r ∂μ)) := by
  have hNfin : ∀ᵐ r ∂μ, N r < ⊤ := ae_lt_top hNm hN.ne
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 hdiff
  have hall : ∀ᵐ r ∂μ, ∀ n, n0 ≤ n → ‖Fn n r - F r‖ₑ ≤ N r * e n := by
    refine ae_all_iff.2 fun n => ?_
    by_cases hn : n0 ≤ n
    · filter_upwards [hn0 n hn] with r hr _ using hr
    · exact Eventually.of_forall fun r h => absurd h hn
  have hlim : ∀ᵐ r ∂μ, Tendsto (fun n => Fn n r) atTop (𝓝 (F r)) := by
    filter_upwards [hNfin, hall] with r hNr hr
    have h0 : Tendsto (fun n => N r * e n) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul he (Or.inr hNr.ne)
    have h1 : Tendsto (fun n => edist (Fn n r) (F r)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0 (Eventually.of_forall fun _ => bot_le)
        (eventually_atTop.2 ⟨n0, fun n hn => by rw [edist_eq_enorm_sub]; exact hr n hn⟩)
    exact tendsto_iff_edist_tendsto_0.2 h1
  have hFm : AEStronglyMeasurable F μ := aestronglyMeasurable_of_tendsto_ae atTop hFn hlim
  have hNc : ∫⁻ r, N r * c ∂μ < ⊤ := by
    rw [lintegral_mul_const _ hNm]; exact ENNReal.mul_lt_top hN hc.lt_top
  have hFi : Integrable F μ :=
    ⟨hFm, lt_of_le_of_lt (lintegral_mono_ae hFb) hNc⟩
  refine ⟨hFi, ?_⟩
  obtain ⟨n1, hn1⟩ := eventually_atTop.1 (he.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < ⊤ from by simp)))
  have hdi : ∀ n, max n0 n1 ≤ n → Integrable (fun r => Fn n r - F r) μ := by
    intro n hn
    refine ⟨(hFn n).sub hFm, lt_of_le_of_lt (lintegral_mono_ae ?_) (b := ∫⁻ r, N r * e n ∂μ) ?_⟩
    · filter_upwards [hall] with r hr using hr n ((le_max_left _ _).trans hn)
    · rw [lintegral_mul_const _ hNm]
      exact ENNReal.mul_lt_top hN (hn1 n ((le_max_right _ _).trans hn))
  have hb : ∀ n, max n0 n1 ≤ n → ‖∫ r, Fn n r ∂μ - ∫ r, F r ∂μ‖ ≤ ((∫⁻ r, N r ∂μ) * e n).toReal := by
    intro n hn
    have hi := hdi n hn
    have hFni : Integrable (fun r => Fn n r) μ :=
      (hi.add hFi).congr (Eventually.of_forall fun r => by simp)
    have h1 : ∫ r, Fn n r ∂μ - ∫ r, F r ∂μ = ∫ r, (Fn n r - F r) ∂μ := (integral_sub hFni hFi).symm
    rw [h1]
    refine (norm_integral_le_integral_norm _).trans ?_
    have h2 : ENNReal.ofReal (∫ r, ‖Fn n r - F r‖ ∂μ) ≤ (∫⁻ r, N r ∂μ) * e n := by
      rw [ofReal_integral_norm_eq_lintegral_enorm hi, ← lintegral_mul_const _ hNm]
      exact lintegral_mono_ae (by filter_upwards [hall] with r hr using hr n ((le_max_left _ _).trans hn))
    have h3 : (∫⁻ r, N r ∂μ) * e n ≠ ⊤ := (ENNReal.mul_lt_top hN (hn1 n ((le_max_right _ _).trans hn))).ne
    have := ENNReal.toReal_mono h3 h2
    rwa [ENNReal.toReal_ofReal (integral_nonneg fun r => norm_nonneg _)] at this
  have hz : Tendsto (fun n => ((∫⁻ r, N r ∂μ) * e n).toReal) atTop (𝓝 0) := by
    have h5 : Tendsto (fun n => (∫⁻ r, N r ∂μ) * e n) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul he (Or.inr hN.ne)
    have h6 : Tendsto (fun n => ((∫⁻ r, N r ∂μ) * e n).toReal) atTop (𝓝 (ENNReal.toReal 0)) :=
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h5
    rwa [ENNReal.toReal_zero] at h6
  have h4 : Tendsto (fun n => ∫ r, Fn n r ∂μ - ∫ r, F r ∂μ) atTop (𝓝 0) :=
    squeeze_zero_norm' (eventually_atTop.2 ⟨max n0 n1, hb⟩) hz
  simpa using h4.add_const (∫ r, F r ∂μ)

end HRS.MS.S111K4AT
