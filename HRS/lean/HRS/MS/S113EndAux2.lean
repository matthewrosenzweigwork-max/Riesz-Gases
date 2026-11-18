import HRS.MS.S113EndAux1

/-!
# S11.3 endpoint (worker S113X), part 2: Gronwall for the logarithmic power mass with a variable exponent

`Ψ' ≤ (p'/p)(Ψ - C₀)` a.e. with `Ψ, p` absolutely continuous and `p > 1` gives `(Ψ - C₀)/p` nonincreasing; hence
`Ψ(T) ≤ C₀ + (Ψ(0) - C₀) p(T)/p(0)`; and the exponentiated form `M(T) ≤ max(M(0), e^{C₀})` when `0 < p(T) ≤ p(0)`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S113BD

theorem s113x_inv_lipschitz : LipschitzOnWith 1 (fun x : ℝ => x⁻¹) (Set.Ici 1) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hx1 : 1 ≤ x := hx
  have hy1 : 1 ≤ y := hy
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rw [inv_sub_inv hx0.ne' hy0.ne', abs_div, abs_of_pos (mul_pos hx0 hy0)]
  rw [div_le_iff₀ (mul_pos hx0 hy0), abs_sub_comm y x]
  have : 1 ≤ x * y := by nlinarith
  calc |x - y| = |x - y| * 1 := by ring
    _ ≤ |x - y| * (x * y) := mul_le_mul_of_nonneg_left this (abs_nonneg _)

theorem s113x_gronwall {Ψ p : ℝ → ℝ} {C₀ T : ℝ} (hT : 0 ≤ T)
    (hΨ : AbsolutelyContinuousOnInterval Ψ 0 T) (hp : AbsolutelyContinuousOnInterval p 0 T)
    (hp1 : ∀ t ∈ Set.Icc (0 : ℝ) T, 1 < p t)
    (hder : ∀ᵐ t : ℝ, t ∈ Set.Ioo 0 T → deriv Ψ t ≤ deriv p t / p t * (Ψ t - C₀)) :
    (Ψ T - C₀) / p T ≤ (Ψ 0 - C₀) / p 0 := by
  have hpinv : AbsolutelyContinuousOnInterval (fun t => (p t)⁻¹) 0 T := by
    have := s113x_inv_lipschitz.comp_absolutelyContinuousOnInterval (a := 0) (b := T) (g := p)
      (fun t ht => by rw [Set.uIcc_of_le hT] at ht; exact (hp1 t ht).le) hp
    exact this
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => C₀) 0 T :=
    (LipschitzWith.const C₀).lipschitzOnWith.absolutelyContinuousOnInterval
  have hw : AbsolutelyContinuousOnInterval (fun t => Ψ t - C₀) 0 T := hΨ.sub hc
  have hg : AbsolutelyContinuousOnInterval (fun t => (Ψ t - C₀) * (p t)⁻¹) 0 T := hw.mul hpinv
  have hint := hg.integral_deriv_eq_sub
  have hae : ∀ᵐ t : ℝ, t ∈ Set.Ioc 0 T → deriv (fun t => (Ψ t - C₀) * (p t)⁻¹) t ≤ 0 := by
    filter_upwards [hΨ.ae_differentiableAt, hp.ae_differentiableAt, hder,
      (show ∀ᵐ t : ℝ, t ≠ T by simp [ae_iff, measure_singleton])] with t h1 h2 h3 hTt ht
    have ht' : t ∈ Set.Ioo 0 T := ⟨ht.1, lt_of_le_of_ne ht.2 hTt⟩
    have huI : t ∈ Set.uIcc (0 : ℝ) T := by rw [Set.uIcc_of_le hT]; exact ⟨ht.1.le, ht.2⟩
    have hpt : 1 < p t := hp1 t ⟨ht.1.le, ht.2⟩
    have hp0 : 0 < p t := by linarith
    have hdΨ := (h1 huI).hasDerivAt
    have hdp := (h2 huI).hasDerivAt
    have hd : HasDerivAt (fun t => (Ψ t - C₀) * (p t)⁻¹)
        (deriv Ψ t * (p t)⁻¹ + (Ψ t - C₀) * (-(deriv p t) / (p t) ^ 2)) t :=
      (hdΨ.sub_const C₀).mul (hdp.inv hp0.ne')
    rw [hd.deriv]
    have h3' := h3 ht'
    rw [div_mul_eq_mul_div, le_div_iff₀ hp0] at h3'
    have e : deriv Ψ t * (p t)⁻¹ + (Ψ t - C₀) * (-(deriv p t) / (p t) ^ 2) =
        (deriv Ψ t * p t - deriv p t * (Ψ t - C₀)) / (p t) ^ 2 := by
      field_simp
      ring
    rw [e]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hnn : 0 ≤ ∫ t in (0 : ℝ)..T, -deriv (fun t => (Ψ t - C₀) * (p t)⁻¹) t := by
    refine intervalIntegral.integral_nonneg_of_ae_restrict hT ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    have h0 : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff, measure_singleton]
    filter_upwards [hae, h0] with t ht ht0 htI
    have := ht ⟨lt_of_le_of_ne htI.1 (Ne.symm ht0), htI.2⟩
    simpa using this
  rw [intervalIntegral.integral_neg, hint] at hnn
  simp only [div_eq_mul_inv]
  linarith

theorem s113x_exp_bound {Ψ0 ΨT C₀ pT p0 : ℝ} (hpT : 0 < pT) (hle : pT ≤ p0)
    (h : (ΨT - C₀) / pT ≤ (Ψ0 - C₀) / p0) :
    ΨT ≤ max Ψ0 C₀ := by
  have hp0 : 0 < p0 := lt_of_lt_of_le hpT hle
  have h1 : ΨT - C₀ ≤ (Ψ0 - C₀) * (pT / p0) := by
    rw [div_le_iff₀ hpT] at h
    calc ΨT - C₀ ≤ (Ψ0 - C₀) / p0 * pT := h
      _ = (Ψ0 - C₀) * (pT / p0) := by ring
  have hθ0 : 0 ≤ pT / p0 := by positivity
  have hθ1 : pT / p0 ≤ 1 := (div_le_one hp0).2 hle
  rcases le_total Ψ0 C₀ with h0 | h0
  · have : (Ψ0 - C₀) * (pT / p0) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hθ0
    calc ΨT ≤ C₀ := by linarith
      _ ≤ max Ψ0 C₀ := le_max_right _ _
  · have : (Ψ0 - C₀) * (pT / p0) ≤ Ψ0 - C₀ := by nlinarith
    calc ΨT ≤ Ψ0 := by linarith
      _ ≤ max Ψ0 C₀ := le_max_left _ _

end HRS.MS.S113BD
