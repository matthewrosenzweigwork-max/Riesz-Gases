import HRS.Energy.Modulated

/-!
# Uniform-integrability tail bound from a relative-entropy bound

For probability measures `ν Q` with `relEntropy ν Q ≤ ofReal H₀` and `1 < L`:
`ν ≪ Q`, and `ν {ν.rnDeriv Q > L} ≤ ofReal ((H₀ + e⁻¹) / log L)`.

Proof sketch: `h = dν/dQ`, `A = {h > L}`. Since `log h = llr ν Q` is `ν`-integrable with
`∫ log h dν = H(ν|Q) ≤ H₀`, and `log L · 1_A ≤ log h - 1_{Aᶜ} log h` pointwise,
`log L · ν(A) ≤ H₀ - ∫_{Aᶜ} log h dν`. Finally `∫_{Aᶜ} log h dν = ∫_{Aᶜ} h log h dQ ≥ -e⁻¹`
because `t log t ≥ -e⁻¹` for `t ≥ 0`. The degenerate case `klDiv ν Q = 0` forces `ν = Q`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HRS.ME.UIEntropy

/-- `t log t ≥ -e⁻¹` for `t ≥ 0`. -/
lemma mul_log_ge_neg_exp_inv {t : ℝ} (ht : 0 ≤ t) :
    -Real.exp (-1) ≤ t * Real.log t := by
  rcases ht.eq_or_lt with rfl | ht
  · simp only [zero_mul]
    linarith [Real.exp_pos (-1)]
  · have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 / (Real.exp 1 * t) by positivity)
    rw [one_div, Real.log_inv, Real.log_mul (Real.exp_pos 1).ne' ht.ne', Real.log_exp] at h1
    have h3 : -Real.log t ≤ (Real.exp 1 * t)⁻¹ := by linarith
    have h4 := mul_le_mul_of_nonneg_left h3 ht.le
    have h5 : t * (Real.exp 1 * t)⁻¹ = Real.exp (-1) := by
      rw [Real.exp_neg]
      field_simp
    nlinarith [h4, h5]

theorem ui_tail_of_relEntropy {α : Type*} [MeasurableSpace α]
    (ν Q : Measure α) [IsProbabilityMeasure ν] [IsProbabilityMeasure Q]
    (H₀ L : ℝ) (hL : 1 < L) (hH : HRS.relEntropy ν Q ≤ ENNReal.ofReal H₀) :
    ν ≪ Q ∧
      ν {x | ENNReal.ofReal L < ν.rnDeriv Q x} ≤
        ENNReal.ofReal ((H₀ + Real.exp (-1)) / Real.log L) := by
  have hH' : InformationTheory.klDiv ν Q ≤ ENNReal.ofReal H₀ := hH
  have hne : InformationTheory.klDiv ν Q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH'
  obtain ⟨hac, hint⟩ := InformationTheory.klDiv_ne_top_iff.mp hne
  refine ⟨hac, ?_⟩
  have hL0 : 0 < L := by linarith
  have hlogL : 0 < Real.log L := Real.log_pos hL
  by_cases h0 : InformationTheory.klDiv ν Q = 0
  · -- degenerate case: `ν = Q`, so the density is `1` a.e. and `L > 1`
    have hνQ : ν = Q := InformationTheory.klDiv_eq_zero_iff.mp h0
    have hzero : ν {x | ENNReal.ofReal L < ν.rnDeriv Q x} = 0 := by
      rw [hνQ]
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [Measure.rnDeriv_self Q] with x hx
      intro hmem
      have h2 : ENNReal.ofReal L < Q.rnDeriv Q x := hmem
      rw [hx] at h2
      have h3 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal L := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hL.le
      exact absurd h2 (not_lt.2 h3)
    rw [hzero]
    simp
  have hH₀ : 0 ≤ H₀ := by
    by_contra hneg
    push Not at hneg
    rw [ENNReal.ofReal_eq_zero.2 hneg.le] at hH'
    exact h0 (le_zero_iff.1 hH')
  have hHle : (InformationTheory.klDiv ν Q).toReal ≤ H₀ :=
    ENNReal.toReal_le_of_le_ofReal hH₀ hH'
  have hHint : (InformationTheory.klDiv ν Q).toReal = ∫ x, MeasureTheory.llr ν Q x ∂ν :=
    InformationTheory.toReal_klDiv_of_measure_eq hac (by simp)
  have hfin : ∀ᵐ x ∂ν, ν.rnDeriv Q x < ⊤ := hac.ae_le (Measure.rnDeriv_lt_top ν Q)
  have hAm : MeasurableSet {x | L < (ν.rnDeriv Q x).toReal} :=
    measurableSet_lt measurable_const (Measure.measurable_rnDeriv ν Q).ennreal_toReal
  set A : Set α := {x | L < (ν.rnDeriv Q x).toReal} with hA
  have hset : {x | ENNReal.ofReal L < ν.rnDeriv Q x} =ᵐ[ν] A := by
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [hfin] with x hx
    show ENNReal.ofReal L < ν.rnDeriv Q x ↔ L < (ν.rnDeriv Q x).toReal
    exact ENNReal.ofReal_lt_iff_lt_toReal hL0.le hx.ne
  rw [measure_congr hset]
  have hintI : Integrable (A.indicator fun _ => Real.log L) ν :=
    (integrable_const _).indicator hAm
  have hIntAc : Integrable (Aᶜ.indicator (MeasureTheory.llr ν Q)) ν :=
    hint.indicator hAm.compl
  have hpt : ∀ x, A.indicator (fun _ => Real.log L) x ≤
      MeasureTheory.llr ν Q x - Aᶜ.indicator (MeasureTheory.llr ν Q) x := by
    intro x
    by_cases hx : x ∈ A
    · have hlt : L < (ν.rnDeriv Q x).toReal := hx
      have hlog : Real.log L < MeasureTheory.llr ν Q x :=
        Real.log_lt_log hL0 hlt
      rw [Set.indicator_of_mem hx, Set.indicator_of_notMem (by simp [hx])]
      linarith
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem hx]
      simp
  have h1 : ∫ x, A.indicator (fun _ => Real.log L) x ∂ν ≤
      ∫ x, (MeasureTheory.llr ν Q x - Aᶜ.indicator (MeasureTheory.llr ν Q) x) ∂ν :=
    integral_mono hintI (hint.sub hIntAc) hpt
  rw [integral_sub hint hIntAc, integral_indicator_const (Real.log L) hAm, smul_eq_mul] at h1
  -- the `Q`-side lower bound on `∫_{Aᶜ} log h dν`
  have hK : -Real.exp (-1) ≤ ∫ x, Aᶜ.indicator (MeasureTheory.llr ν Q) x ∂ν := by
    have hsm := integral_rnDeriv_smul (μ := ν) (ν := Q) (f := Aᶜ.indicator
      (MeasureTheory.llr ν Q)) hac
    rw [← hsm]
    have hQint : Integrable (fun x => (ν.rnDeriv Q x).toReal • Aᶜ.indicator
        (MeasureTheory.llr ν Q) x) Q :=
      (integrable_rnDeriv_smul_iff hac).2 hIntAc
    have hc : ∫ _x, -Real.exp (-1) ∂Q = -Real.exp (-1) := by simp
    rw [← hc]
    refine integral_mono (integrable_const _) hQint ?_
    intro x
    simp only [smul_eq_mul]
    rw [Set.indicator_apply]
    split_ifs with hx
    · exact mul_log_ge_neg_exp_inv ENNReal.toReal_nonneg
    · simp only [mul_zero]
      linarith [Real.exp_pos (-1)]
  have hmain : (ν.real A) * Real.log L ≤ H₀ + Real.exp (-1) := by
    rw [← hHint] at h1
    linarith
  have hc0 : 0 ≤ (H₀ + Real.exp (-1)) / Real.log L :=
    div_nonneg (by linarith [Real.exp_pos (-1)]) hlogL.le
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top ν A) hc0, le_div_iff₀ hlogL]
  exact hmain

end HRS.ME.UIEntropy
