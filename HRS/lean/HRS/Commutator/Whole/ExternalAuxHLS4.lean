import HRS.Commutator.Whole.RieszAux

/-!
# The Riesz identity for integrable Fourier data (packet X-HLS, part 4)

`Γ(γ/2) ∫ |x|^{-γ} 𝓕H(x) dx = π^{γ-d/2} Γ((d-γ)/2) ∫ |ξ|^{γ-d} H(ξ) dξ` for an *integrable* `H` such that
both integrals converge absolutely (the Schwartz case is `riesz_potential_aux`; the proof is the same,
by Gaussian subordination and two Fubini exchanges).
-/

open MeasureTheory Filter Topology Metric Real Set
open scoped ENNReal NNReal FourierTransform ContDiff

noncomputable section

namespace HRS.Commutator.Whole

variable {d : ℕ}

/-- Integrability of `(x,t) ↦ t^{γ/2-1} e^{-t|x|²} Ψ(x)` (Tonelli in the order `x` outer). -/
lemma cmxHLS_integrable_left (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : γ < d)
    (Ψ : Euc d → ℂ) (hΨm : Measurable Ψ)
    (hΨ : Integrable (fun x : Euc d => ‖x‖ ^ (-γ) * ‖Ψ x‖)) :
    Integrable (Function.uncurry fun (x : Euc d) (t : ℝ) =>
      ((t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2)) : ℝ) : ℂ) * Ψ x)
      ((volume : Measure (Euc d)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (x : Euc d) (t : ℝ) =>
      ((t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2)) : ℝ) : ℂ) * Ψ x)
      ((volume : Measure (Euc d)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    apply Measurable.aestronglyMeasurable
    refine Measurable.mul ?_ ?_
    · refine Complex.measurable_ofReal.comp (Measurable.mul ?_ ?_)
      · exact (measurable_snd.pow_const _)
      · exact Real.continuous_exp.measurable.comp
          ((measurable_snd.mul (measurable_fst.norm.pow_const 2)).neg)
    · exact hΨm.comp measurable_fst
  refine ⟨hmeas, ?_⟩
  unfold HasFiniteIntegral
  rw [lintegral_prod _ hmeas.enorm]
  have hpoint : ∀ x : Euc d, x ≠ 0 → ∫⁻ t in Ioi (0 : ℝ),
      ‖((t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2)) : ℝ) : ℂ) * Ψ x‖ₑ
        = ENNReal.ofReal (Real.Gamma (γ / 2)) * ENNReal.ofReal (‖x‖ ^ (-γ) * ‖Ψ x‖) := by
    intro x hx
    have hr : 0 < ‖x‖ ^ 2 := by
      have : 0 < ‖x‖ := norm_pos_iff.2 hx
      positivity
    have hnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2)) :=
      fun t ht => mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le
    rw [setLIntegral_congr_fun measurableSet_Ioi (fun t ht => enorm_real_mul_eq (hnn t ht) _)]
    have hint : IntegrableOn (fun t : ℝ => (t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2))) * ‖Ψ x‖)
        (Ioi 0) :=
      (integrableOn_gamma_kernel' (by linarith) hr).mul_const _
    have hnn' : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun t : ℝ => (t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2))) * ‖Ψ x‖) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (hnn t ht) (norm_nonneg _)
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn']
    rw [integral_mul_const, integral_gauss_subordination hγ x hx]
    rw [← ENNReal.ofReal_mul (Real.Gamma_pos_of_pos (by linarith)).le]
    congr 1
    ring
  have hint := hΨ
  have hfin : ∫⁻ x : Euc d, ENNReal.ofReal (‖x‖ ^ (-γ) * ‖Ψ x‖) < ⊤ := by
    have h := hint.hasFiniteIntegral
    unfold HasFiniteIntegral at h
    refine lt_of_le_of_lt (le_of_eq ?_) h
    apply lintegral_congr
    intro x
    rw [← ofReal_norm, Real.norm_of_nonneg (by positivity)]
  refine lt_of_eq_of_lt (b := ∫⁻ x : Euc d, ENNReal.ofReal (Real.Gamma (γ / 2))
      * ENNReal.ofReal (‖x‖ ^ (-γ) * ‖Ψ x‖)) (lintegral_congr_ae ?_) ?_
  · filter_upwards [ae_ne_zero_euc hd] with x hx
    exact hpoint x hx
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-- Integrability of `(t,ξ) ↦ t^{γ/2-1}(π/t)^{d/2} e^{-π²|ξ|²/t} H(ξ)` (Tonelli, `ξ` outer). -/
lemma cmxHLS_integrable_right (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : γ < d)
    (H : Euc d → ℂ) (hHm : Measurable H)
    (hH : Integrable (fun ξ : Euc d => ‖ξ‖ ^ (γ - (d : ℝ)) * ‖H ξ‖)) :
    Integrable (Function.uncurry fun (t : ℝ) (ξ : Euc d) =>
      ((t ^ (γ / 2 - 1) : ℝ) : ℂ) * ((((π / t) ^ ((d : ℝ) / 2)) : ℝ) : ℂ)
        * ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ) * H ξ)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (t : ℝ) (ξ : Euc d) =>
      ((t ^ (γ / 2 - 1) : ℝ) : ℂ) * ((((π / t) ^ ((d : ℝ) / 2)) : ℝ) : ℂ)
        * ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ) * H ξ)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    apply Measurable.aestronglyMeasurable
    refine Measurable.mul (Measurable.mul (Measurable.mul ?_ ?_) ?_) ?_
    · exact Complex.measurable_ofReal.comp (measurable_fst.pow_const _)
    · exact Complex.measurable_ofReal.comp ((measurable_const.div measurable_fst).pow_const _)
    · exact Complex.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
        ((measurable_const.mul (measurable_snd.norm.pow_const 2)).div measurable_fst).neg)
    · exact hHm.comp measurable_snd
  refine ⟨hmeas, ?_⟩
  unfold HasFiniteIntegral
  rw [lintegral_prod_symm _ hmeas.enorm]
  have hβ : 0 < ((d : ℝ) - γ) / 2 := by linarith
  have hlin : ∀ ξ : Euc d, ξ ≠ 0 → ∫⁻ t in Ioi (0 : ℝ),
      ‖((t ^ (γ / 2 - 1) : ℝ) : ℂ) * ((((π / t) ^ ((d : ℝ) / 2)) : ℝ) : ℂ)
        * ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ) * H ξ‖ₑ
        = ENNReal.ofReal ((π ^ (γ - (d : ℝ) / 2) * ‖ξ‖ ^ (γ - (d : ℝ)) * Real.Gamma (((d : ℝ) - γ) / 2))
            * ‖H ξ‖) := by
    intro ξ hξ
    have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    have hc : 0 < π ^ 2 * ‖ξ‖ ^ 2 := by positivity
    have hpt : ∀ t ∈ Ioi (0 : ℝ), ‖((t ^ (γ / 2 - 1) : ℝ) : ℂ) * ((((π / t) ^ ((d : ℝ) / 2)) : ℝ) : ℂ)
        * ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ) * H ξ‖ₑ
          = ENNReal.ofReal ((π ^ ((d : ℝ) / 2) * (t ^ (-(((d : ℝ) - γ) / 2) - 1)
              * Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)))) * ‖H ξ‖) := by
      intro t ht
      have ht' : (0 : ℝ) < t := ht
      have h2 : ((t ^ (γ / 2 - 1) : ℝ) : ℂ) * ((((π / t) ^ ((d : ℝ) / 2)) : ℝ) : ℂ)
          * ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ)
          = ((t ^ (γ / 2 - 1) * (π / t) ^ ((d : ℝ) / 2) * Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [h2, riesz_kernel_pointwise hγd ht' ξ, mul_assoc]
      rw [enorm_real_mul_eq (by positivity) (H ξ)]
      congr 1
      ring
    rw [setLIntegral_congr_fun measurableSet_Ioi (fun t ht => hpt t ht)]
    have hint : IntegrableOn (fun t : ℝ => (π ^ ((d : ℝ) / 2) * (t ^ (-(((d : ℝ) - γ) / 2) - 1)
        * Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)))) * ‖H ξ‖) (Ioi 0) :=
      ((integrableOn_and_integral_inv_kernel hβ hc).1.const_mul (π ^ ((d : ℝ) / 2))).mul_const _
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun t : ℝ =>
        (π ^ ((d : ℝ) / 2) * (t ^ (-(((d : ℝ) - γ) / 2) - 1)
          * Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)))) * ‖H ξ‖) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht' : (0 : ℝ) < t := ht
      have : 0 ≤ t ^ (-(((d : ℝ) - γ) / 2) - 1) * Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) :=
        mul_nonneg (Real.rpow_nonneg ht'.le _) (Real.exp_pos _).le
      exact mul_nonneg (mul_nonneg (by positivity) this) (norm_nonneg _)
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_mul_const, riesz_t_integral hγd hξ]
  have hint2 := hH
  have hfin2 : ∫⁻ ξ : Euc d, ENNReal.ofReal (‖ξ‖ ^ (γ - (d : ℝ)) * ‖H ξ‖) < ⊤ := by
    have h := hint2.hasFiniteIntegral
    unfold HasFiniteIntegral at h
    refine lt_of_le_of_lt (le_of_eq ?_) h
    apply lintegral_congr
    intro ξ
    rw [← ofReal_norm, Real.norm_of_nonneg (by positivity)]
  have hC : 0 ≤ π ^ (γ - (d : ℝ) / 2) * Real.Gamma (((d : ℝ) - γ) / 2) := by
    have := Real.Gamma_pos_of_pos hβ
    positivity
  refine lt_of_eq_of_lt (b := ∫⁻ ξ : Euc d, ENNReal.ofReal (π ^ (γ - (d : ℝ) / 2)
      * Real.Gamma (((d : ℝ) - γ) / 2)) * ENNReal.ofReal (‖ξ‖ ^ (γ - (d : ℝ)) * ‖H ξ‖))
    (lintegral_congr_ae ?_) ?_
  · filter_upwards [ae_ne_zero_euc hd] with ξ hξ
    refine (hlin ξ hξ).trans ?_
    rw [← ENNReal.ofReal_mul hC]
    congr 1
    ring
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin2

/-- The inner `x`-integral, after the multiplication formula. -/
lemma cmxHLS_gauss_inner {γ t : ℝ} (ht : 0 < t) (H : Euc d → ℂ) (hH : Integrable H) :
    ∫ x, ((t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2)) : ℝ) : ℂ) * (𝓕 H) x
      = ((t ^ (γ / 2 - 1) : ℝ) : ℂ) * ∫ ξ, (((π / t) ^ ((d : ℝ) / 2) : ℝ) : ℂ)
          * ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ) * H ξ := by
  have h1 : ∀ x : Euc d, ((t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2)) : ℝ) : ℂ) * (𝓕 H) x
      = ((t ^ (γ / 2 - 1) : ℝ) : ℂ) * (((Real.exp (-(t * ‖x‖ ^ 2)) : ℝ) : ℂ) * (𝓕 H) x) := by
    intro x
    push_cast
    ring
  have hm : ∫ x : Euc d, ((Real.exp (-(t * ‖x‖ ^ 2)) : ℝ) : ℂ) * (𝓕 H) x
      = ∫ ξ : Euc d, 𝓕 (fun v : Euc d => ((Real.exp (-(t * ‖v‖ ^ 2)) : ℝ) : ℂ)) ξ * H ξ :=
    integral_mul_fourier_eq _ _ (integrable_gauss_real ht) hH
  simp_rw [h1]
  rw [integral_const_mul, hm]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards with ξ
  rw [gauss_fourier_real ht ξ]

/-- The `t`-integral of the second kernel, for `ξ ≠ 0` and any constant `z`. -/
lemma cmxHLS_t_integral_kernel {γ : ℝ} (hγd : γ < d) {ξ : Euc d} (hξ : ξ ≠ 0) (z : ℂ) :
    ∫ t in Ioi (0 : ℝ), ((t ^ (γ / 2 - 1) : ℝ) : ℂ) * ((((π / t) ^ ((d : ℝ) / 2)) : ℝ) : ℂ)
        * ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ) * z
      = (((π ^ (γ - (d : ℝ) / 2) * Real.Gamma (((d : ℝ) - γ) / 2)) * ‖ξ‖ ^ (γ - (d : ℝ)) : ℝ) : ℂ)
        * z := by
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ((t ^ (γ / 2 - 1) : ℝ) : ℂ) * ((((π / t) ^ ((d : ℝ) / 2)) : ℝ) : ℂ)
      * ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ) * z
        = ((π ^ ((d : ℝ) / 2) * (t ^ (-(((d : ℝ) - γ) / 2) - 1)
            * Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t))) : ℝ) : ℂ) * z := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have h2 : ((t ^ (γ / 2 - 1) : ℝ) : ℂ) * ((((π / t) ^ ((d : ℝ) / 2)) : ℝ) : ℂ)
        * ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ)
        = ((t ^ (γ / 2 - 1) * (π / t) ^ ((d : ℝ) / 2) * Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h2, riesz_kernel_pointwise hγd ht' ξ]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hpt t ht)]
  have hβ : 0 < ((d : ℝ) - γ) / 2 := by linarith
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hc : 0 < π ^ 2 * ‖ξ‖ ^ 2 := by positivity
  rw [integral_mul_const, integral_complex_ofReal, riesz_t_integral hγd hξ]
  congr 1
  congr 1
  ring

/-- The Riesz identity for integrable `H` with absolutely convergent integrals. -/
theorem cmxHLS_riesz_general (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : γ < d) (H : Euc d → ℂ)
    (hH1 : Integrable H) (hHm : Measurable H)
    (hL : Integrable (fun x : Euc d => ‖x‖ ^ (-γ) * ‖𝓕 H x‖))
    (hR : Integrable (fun ξ : Euc d => ‖ξ‖ ^ (γ - (d : ℝ)) * ‖H ξ‖)) :
    ((Real.Gamma (γ / 2) : ℝ) : ℂ) * ∫ x : Euc d, ((‖x‖ ^ (-γ) : ℝ) : ℂ) * 𝓕 H x
      = (((Real.pi ^ (γ - (d : ℝ) / 2) * Real.Gamma (((d : ℝ) - γ) / 2)) : ℝ) : ℂ)
        * ∫ ξ : Euc d, ((‖ξ‖ ^ (γ - (d : ℝ)) : ℝ) : ℂ) * H ξ := by
  have hβ : 0 < ((d : ℝ) - γ) / 2 := by linarith
  have hcont : Continuous (𝓕 H) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hH1
  have e1 : ((Real.Gamma (γ / 2) : ℝ) : ℂ) * ∫ x : Euc d, ((‖x‖ ^ (-γ) : ℝ) : ℂ) * 𝓕 H x
      = ∫ x : Euc d, ∫ t in Ioi (0 : ℝ),
          ((t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2)) : ℝ) : ℂ) * 𝓕 H x := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_zero_euc hd] with x hx
    rw [riesz_gamma_pointwise hγ x hx]
    push_cast
    ring
  have hsw : ∫ x : Euc d, ∫ t in Ioi (0 : ℝ),
        ((t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2)) : ℝ) : ℂ) * 𝓕 H x
      = ∫ t in Ioi (0 : ℝ), ∫ x : Euc d,
        ((t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2)) : ℝ) : ℂ) * 𝓕 H x :=
    integral_integral_swap (cmxHLS_integrable_left hd hγ hγd (𝓕 H) hcont.measurable hL)
  rw [e1, hsw]
  have e2 : ∫ t in Ioi (0 : ℝ), ∫ x : Euc d,
        ((t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2)) : ℝ) : ℂ) * 𝓕 H x
      = ∫ t in Ioi (0 : ℝ), ∫ ξ : Euc d, ((t ^ (γ / 2 - 1) : ℝ) : ℂ)
          * ((((π / t) ^ ((d : ℝ) / 2)) : ℝ) : ℂ) * ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ)
          * H ξ := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [cmxHLS_gauss_inner ht H hH1, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ : Euc d => ?_))
    ring
  rw [e2, integral_integral_swap (cmxHLS_integrable_right hd hγ hγd H hHm hR)]
  have e3 : ∫ ξ : Euc d, ∫ t in Ioi (0 : ℝ), ((t ^ (γ / 2 - 1) : ℝ) : ℂ)
          * ((((π / t) ^ ((d : ℝ) / 2)) : ℝ) : ℂ) * ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ)
          * H ξ
      = ∫ ξ : Euc d, (((Real.pi ^ (γ - (d : ℝ) / 2) * Real.Gamma (((d : ℝ) - γ) / 2)) : ℝ) : ℂ)
          * ((((‖ξ‖ ^ (γ - (d : ℝ))) : ℝ) : ℂ) * H ξ) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_zero_euc hd] with ξ hξ
    rw [cmxHLS_t_integral_kernel hγd hξ (H ξ)]
    push_cast
    ring
  rw [e3, integral_const_mul]

end HRS.Commutator.Whole
