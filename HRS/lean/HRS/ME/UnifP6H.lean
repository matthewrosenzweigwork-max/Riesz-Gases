import HRS.ME.UnifP6G

/-!
# Uniform Proposition 4.8, part H (packet P6): the conditional expectation

`conditional_singular_observation_unif`: the uniform form of `HRS.conditional_singular_observation`
(Proposition 4.8, `M:R:prop:conditional-expectation`).  The constant `C` is chosen after
`d, s, c, βm, βp, c₀, Λ` (and the uniform Lemma 4.6 clauses `CavRespUnif`) and before `β ∈ [βm, βp]` and
`ρ ∈ UFam d c₀ Λ`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.ME.Unif

open HRS HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp HRS.L48

variable {d : ℕ} {s : ℝ}

/-- **Proposition 4.8 (`conditional_singular_observation`), uniform form.** -/
theorem conditional_singular_observation_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (c₀ Λ : ℝ) (hc₀ : 0 < c₀) (hΛ : 1 ≤ Λ) (hCR : CavRespUnif d s c βm βp c₀ Λ) :
    ∃ C : ℝ, ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ i : Fin (N - 1),
      Integrable (fun Y : Config d (N - 1) => gPlus d s c (x - Y i)) (critPole d s c β ρ N x t) ∧
      eLpNorm (fun Y =>
          (critPole d s c β ρ N x t)[fun Y' => gPlus d s c (x - Y' i) | othersSigma i] Y -
            (∫ y, gPlus d s c (x - y) * Real.exp (-(t * (β / N)) * gPlus d s c (x - y))
                ∂(withDensityReal ρ)) /
              (∫ y, Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) ∂(withDensityReal ρ)))
          2 (critPole d s c β ρ N x t) ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      evariance ((critPole d s c β ρ N x t)[fun Y' => gPlus d s c (x - Y' i) | othersSigma i])
          (critPole d s c β ρ N x t) ≤ ENNReal.ofReal (C / N) ∧
      ∫⁻ Y, ‖(critPole d s c β ρ N x t)[fun Y' => gPlus d s c (x - Y' i) | othersSigma i] Y‖ₑ ^ 2
          ∂(critPole d s c β ρ N x t) ≤ ENNReal.ofReal C := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨Cg, hCg0, hCg_all⟩ := conv_gPlus_unif_fam hd hs0 hsd c hc c₀ Λ
  obtain ⟨C2, hC20, hL2_all⟩ := l48_T_L2_unif hd hcrit c hc βm βp hβm hββ c₀ Λ hc₀ hΛ hCR
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  set Tmax : ℝ := Real.exp (βp * Cg) * Cg * Real.exp (3 * (βp * Cg)) with hTmax
  have hTmax0 : 0 ≤ Tmax := by positivity
  refine ⟨max (max C2 (C2 ^ 2)) (Tmax ^ 2), fun β hβI ρ hF N hN x t ht i => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hρ := hF.smooth
  have hμ := isProbabilityMeasure_mu hρ
  have hCg := hCg_all ρ hF
  have hL2 := hL2_all β hβI ρ hF

  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hr0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hlam : 0 ≤ β / N := by positivity
  have hPprob : IsProbabilityMeasure (critPole d s c β ρ N x t) := by
    rw [critPole_eq_poleLaw (c := c) hd hs0 hsd β hβ hρ hN x t]
    exact pole_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam x t ht'.1
  have hae := l48_condExp_eq hd hcrit hβ hρ hc hN x ht' i
  have hTm := l48_meas_T hd hcrit hβ hρ hc (N := N) x t i
  have hbd : ∀ Y : Config d (N - 1), |l48_T d s c β ρ N x t i Y| ≤ Tmax := fun Y => by
    obtain ⟨h1, h2⟩ := l48_T_bound hd hcrit hβ hρ hc hCg hN x ht' i Y
    rw [abs_of_nonneg h1]
    refine h2.trans ?_
    have hb1 : β * Cg ≤ βp * Cg := mul_le_mul_of_nonneg_right hβI.2 hCg0
    have hb2 : Real.exp (β * Cg) ≤ Real.exp (βp * Cg) := Real.exp_le_exp.2 hb1
    have hb3 : Real.exp (3 * (β * Cg)) ≤ Real.exp (3 * (βp * Cg)) := Real.exp_le_exp.2 (by linarith)
    rw [hTmax]
    exact mul_le_mul (mul_le_mul_of_nonneg_right hb2 hCg0) hb3 (Real.exp_pos _).le (by positivity)
  have hCmax1 : C2 ≤ max (max C2 (C2 ^ 2)) (Tmax ^ 2) := (le_max_left _ _).trans (le_max_left _ _)
  have hCmax2 : C2 ^ 2 ≤ max (max C2 (C2 ^ 2)) (Tmax ^ 2) := (le_max_right _ _).trans (le_max_left _ _)
  have hCmax3 : Tmax ^ 2 ≤ max (max C2 (C2 ^ 2)) (Tmax ^ 2) := le_max_right _ _
  have hrpow : (N : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt N := by
    rw [Real.rpow_neg hN0.le, ← Real.sqrt_eq_rpow, one_div]
  have hL2' := hL2 N hN x t ht' i
  refine ⟨l48_integrable hd hcrit hβ hρ hc hN x ht' i, ?_, ?_, ?_⟩
  · -- the `L²` bound
    have hcongr : eLpNorm (fun Y => (critPole d s c β ρ N x t)[fun Y' : Config d (N - 1) =>
          gPlus d s c (x - Y' i) | othersSigma i] Y -
          (∫ y, gPlus d s c (x - y) * Real.exp (-(t * (β / N)) * gPlus d s c (x - y))
            ∂(withDensityReal ρ)) /
          (∫ y, Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) ∂(withDensityReal ρ)))
        2 (critPole d s c β ρ N x t) =
        eLpNorm (fun Y : Config d (N - 1) => l48_T d s c β ρ N x t i Y -
          l48_F d s c β ρ N x t / l48_B d s c β ρ N x t) 2 (critPole d s c β ρ N x t) :=
      eLpNorm_congr_ae (hae.mono fun Y hY => by beta_reduce; rw [hY]; rfl)
    rw [hcongr]
    refine hL2'.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hrpow, ← div_eq_mul_one_div]
    exact div_le_div_of_nonneg_right hCmax1 hr0.le
  · -- the variance
    rw [evariance_congr hae]
    have hmeas : Measurable fun Y : Config d (N - 1) => l48_T d s c β ρ N x t i Y := hTm
    refine (l48_evariance_le hmeas hbd (l48_F d s c β ρ N x t / l48_B d s c β ρ N x t) ?_).trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hCmax2 hN0.le))
    have := (l48_eLpNorm_le_iff (f := fun Y : Config d (N - 1) => l48_T d s c β ρ N x t i Y -
      l48_F d s c β ρ N x t / l48_B d s c β ρ N x t) (μ := critPole d s c β ρ N x t)
      (hmeas.sub measurable_const) (b := C2 / Real.sqrt N) (by positivity)).1 hL2'
    refine this.trans (le_of_eq ?_)
    rw [div_pow, Real.sq_sqrt hN0.le]
  · -- the second moment
    have hcongr : ∫⁻ Y, ‖(critPole d s c β ρ N x t)[fun Y' : Config d (N - 1) =>
          gPlus d s c (x - Y' i) | othersSigma i] Y‖ₑ ^ 2 ∂(critPole d s c β ρ N x t) =
        ∫⁻ Y, ‖l48_T d s c β ρ N x t i Y‖ₑ ^ 2 ∂(critPole d s c β ρ N x t) :=
      lintegral_congr_ae (hae.mono fun Y hY => by beta_reduce; rw [hY])
    rw [hcongr]
    calc ∫⁻ Y, ‖l48_T d s c β ρ N x t i Y‖ₑ ^ 2 ∂(critPole d s c β ρ N x t)
        ≤ ∫⁻ _Y, ENNReal.ofReal (Tmax ^ 2) ∂(critPole d s c β ρ N x t) := by
          refine lintegral_mono fun Y => ?_
          have h1 : ‖l48_T d s c β ρ N x t i Y‖ₑ ≤ ENNReal.ofReal Tmax := by
            rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (hbd Y)
          calc ‖l48_T d s c β ρ N x t i Y‖ₑ ^ 2 ≤ ENNReal.ofReal Tmax ^ 2 := pow_le_pow_left' h1 2
            _ = ENNReal.ofReal (Tmax ^ 2) := (ENNReal.ofReal_pow hTmax0 2).symm
      _ = ENNReal.ofReal (Tmax ^ 2) := by simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal hCmax3

end HRS.ME.Unif

end
