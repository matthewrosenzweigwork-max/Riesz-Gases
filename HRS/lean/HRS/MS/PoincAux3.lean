import HRS.MS.PoincAux2

/-!
# C-POI, part 3: the expectation of the derivative term

By rotation invariance of `γ ⊗ γ` and the second moment `∫ ⟪v,x⟫² dγ = ‖v‖²/(βa)`,
`∫⁻ ofReal (cpoi_G f θ q)² d(γ ⊗ γ) = ofReal ((βa)⁻¹ ∫ ‖∇f‖² dγ)` for every `θ`
(`cpoi_lintegral_G`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HRS.MS.Poinc

variable {d : ℕ}

theorem cpoi_integrable_inner_sq {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (v : Euc d) :
    Integrable (fun x : Euc d => ⟪v, x⟫ ^ 2) (cpoi_gam d a β) := by
  have := cpoi_gam_isGaussian (d := d) ha hβ
  have := (IsGaussian.memLp_dual (cpoi_gam d a β) (innerSL ℝ v) 2 (by simp)).integrable_sq
  simpa using this

theorem cpoi_lintegral_inner_sq {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (v : Euc d) :
    ∫⁻ x, ENNReal.ofReal (⟪v, x⟫ ^ 2) ∂(cpoi_gam d a β) = ENNReal.ofReal (‖v‖ ^ 2 / (β * a)) := by
  rw [← cpoi_integral_inner_sq ha hβ v,
    ofReal_integral_eq_lintegral_ofReal (cpoi_integrable_inner_sq ha hβ v)
      (ae_of_all _ fun x => sq_nonneg _)]

theorem cpoi_lintegral_G {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : Integrable (fun x => ‖gradient f x‖ ^ 2) (cpoi_gam d a β)) (θ : ℝ) :
    ∫⁻ q, ENNReal.ofReal (cpoi_G f θ q ^ 2) ∂((cpoi_gam d a β).prod (cpoi_gam d a β)) =
      ENNReal.ofReal ((β * a)⁻¹ * ∫ x, ‖gradient f x‖ ^ 2 ∂(cpoi_gam d a β)) := by
  have := cpoi_gam_isProb (d := d) ha hβ
  set γ := cpoi_gam d a β with hγ
  have hgr := cpoi_continuous_gradient hf
  have hH : Measurable fun q : Euc d × Euc d => ENNReal.ofReal (⟪gradient f q.1, q.2⟫ ^ 2) := by
    have : Continuous fun q : Euc d × Euc d => ⟪gradient f q.1, q.2⟫ ^ 2 := by fun_prop
    exact this.measurable.ennreal_ofReal
  have hrot := cpoi_map_rotation (d := d) ha hβ θ
  have hR : Measurable (ContinuousLinearMap.rotation θ : Euc d × Euc d →L[ℝ] Euc d × Euc d) :=
    (ContinuousLinearMap.rotation θ).continuous.measurable
  have e1 : ∫⁻ q, ENNReal.ofReal (cpoi_G f θ q ^ 2) ∂(γ.prod γ) =
      ∫⁻ q, ENNReal.ofReal (⟪gradient f q.1, q.2⟫ ^ 2) ∂(γ.prod γ) := by
    have := lintegral_map (μ := γ.prod γ) hH hR
    rw [hrot] at this
    exact this.symm
  rw [e1, lintegral_prod _ hH.aemeasurable]
  dsimp only
  rw [hγ]
  simp_rw [cpoi_lintegral_inner_sq ha hβ]
  rw [← ofReal_integral_eq_lintegral_ofReal (hg.div_const (β * a)) (ae_of_all _ fun x => by positivity)]
  congr 1
  rw [← integral_const_mul]
  congr 1
  ext x
  ring

/-- Lintegral form of the Maurey-Pisier estimate. -/
theorem cpoi_lintegral_diff_le {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {f : Euc d → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : Integrable (fun x => ‖gradient f x‖ ^ 2) (cpoi_gam d a β)) :
    ∫⁻ q, ENNReal.ofReal ((f q.2 - f q.1) ^ 2) ∂((cpoi_gam d a β).prod (cpoi_gam d a β)) ≤
      ENNReal.ofReal ((Real.pi / 2) ^ 2 * ((β * a)⁻¹ * ∫ x, ‖gradient f x‖ ^ 2 ∂(cpoi_gam d a β))) := by
  have := cpoi_gam_isProb (d := d) ha hβ
  set γ := cpoi_gam d a β with hγ
  set K := (β * a)⁻¹ * ∫ x, ‖gradient f x‖ ^ 2 ∂γ with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; exact mul_nonneg (by positivity) (integral_nonneg fun x => by positivity)
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hGc := cpoi_continuous_G hf
  -- the interval integral as a lintegral over `Ioc`
  have hI : ∀ q : Euc d × Euc d, ENNReal.ofReal (∫ θ in (0 : ℝ)..(Real.pi / 2), cpoi_G f θ q ^ 2) =
      ∫⁻ θ in Set.Ioc 0 (Real.pi / 2), ENNReal.ofReal (cpoi_G f θ q ^ 2) := by
    intro q
    rw [intervalIntegral.integral_of_le (by positivity)]
    have hc : Continuous fun θ : ℝ => cpoi_G f θ q ^ 2 := (cpoi_continuous_G_left hf q).pow 2
    exact ofReal_integral_eq_lintegral_ofReal (hc.integrableOn_Ioc)
      (ae_restrict_of_forall_mem measurableSet_Ioc fun θ _ => sq_nonneg _)
  calc ∫⁻ q, ENNReal.ofReal ((f q.2 - f q.1) ^ 2) ∂(γ.prod γ)
      ≤ ∫⁻ q, (ENNReal.ofReal (Real.pi / 2) *
          ∫⁻ θ in Set.Ioc 0 (Real.pi / 2), ENNReal.ofReal (cpoi_G f θ q ^ 2)) ∂(γ.prod γ) := by
        refine lintegral_mono fun q => ?_
        rw [← hI q, ← ENNReal.ofReal_mul hpi]
        exact ENNReal.ofReal_le_ofReal (cpoi_pointwise hf q)
    _ = ENNReal.ofReal (Real.pi / 2) *
          ∫⁻ q, (∫⁻ θ in Set.Ioc 0 (Real.pi / 2), ENNReal.ofReal (cpoi_G f θ q ^ 2)) ∂(γ.prod γ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Real.pi / 2) *
          ∫⁻ θ in Set.Ioc 0 (Real.pi / 2), ∫⁻ q, ENNReal.ofReal (cpoi_G f θ q ^ 2) ∂(γ.prod γ) := by
        congr 1
        refine lintegral_lintegral_swap ?_
        have : Continuous fun p : (Euc d × Euc d) × ℝ => cpoi_G f p.2 p.1 ^ 2 :=
          ((hGc.comp (continuous_snd.prodMk continuous_fst)).pow 2)
        exact this.measurable.ennreal_ofReal.aemeasurable
    _ = ENNReal.ofReal (Real.pi / 2) * ∫⁻ θ in Set.Ioc 0 (Real.pi / 2), ENNReal.ofReal K := by
        congr 1
        refine setLIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
        exact cpoi_lintegral_G ha hβ hf hg θ
    _ = ENNReal.ofReal ((Real.pi / 2) ^ 2 * K) := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul hK0,
          ← ENNReal.ofReal_mul hpi]
        congr 1; ring

end HRS.MS.Poinc

end
