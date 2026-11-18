import HRS.PDE.MovCAux2

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movc_gibbs_integral {α : Type*} [MeasurableSpace α] (Pm : Measure α) (D φ : α → ℝ)
    (hD : Measurable D) (hD0 : ∀ x, 0 ≤ D x) {Z : ℝ} (hZ : 0 ≤ Z) :
    ∫ x, φ x ∂((ENNReal.ofReal Z)⁻¹ • Pm.withDensity (fun y => ENNReal.ofReal (D y))) =
      Z⁻¹ * ∫ x, D x * φ x ∂Pm := by
  rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul₀ (f := fun y => ENNReal.ofReal (D y))
    (ENNReal.measurable_ofReal.comp hD).aemeasurable (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ, smul_eq_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (hD0 x)]

theorem movc_gibbs_tendsto {α : Type*} [MeasurableSpace α] (Pm : Measure α) [IsProbabilityMeasure Pm]
    (a : ℝ) (ha : a ≤ 0) (Fn : ℕ → α → ℝ) (F : α → ℝ) (hFn : ∀ n, Measurable (Fn n))
    (hF : Measurable F) (c : ℝ) (hc : ∀ n x, -c ≤ Fn n x)
    (hlim : ∀ᵐ x ∂Pm, Tendsto (fun n => Fn n x) atTop (𝓝 (F x)))
    (φ : α → ℝ) (hφ : Measurable φ) (Cφ : ℝ) (hφb : ∀ x, |φ x| ≤ Cφ) :
    Tendsto (fun n => ∫ x, φ x ∂((ENNReal.ofReal (∫ y, Real.exp (a * Fn n y) ∂Pm))⁻¹ •
        Pm.withDensity (fun y => ENNReal.ofReal (Real.exp (a * Fn n y))))) atTop
      (𝓝 (∫ x, φ x ∂((ENNReal.ofReal (∫ y, Real.exp (a * F y) ∂Pm))⁻¹ •
        Pm.withDensity (fun y => ENNReal.ofReal (Real.exp (a * F y)))))) := by
  set K := Real.exp (-a * c) with hK
  have hexp : ∀ n x, Real.exp (a * Fn n x) ≤ K := fun n x => by
    rw [hK]; apply Real.exp_le_exp.2; nlinarith [hc n x]
  have hlimF : ∀ᵐ x ∂Pm, -c ≤ F x :=
    hlim.mono fun x hx => ge_of_tendsto' hx (fun n => hc n x)
  have hexpF : ∀ᵐ x ∂Pm, Real.exp (a * F x) ≤ K := hlimF.mono fun x hx => by
    rw [hK]; apply Real.exp_le_exp.2; nlinarith
  have hmeasE : ∀ n, Measurable (fun x => Real.exp (a * Fn n x)) := fun n =>
    Real.measurable_exp.comp (measurable_const.mul (hFn n))
  have hmeasEF : Measurable (fun x => Real.exp (a * F x)) :=
    Real.measurable_exp.comp (measurable_const.mul hF)
  have hZn : Tendsto (fun n => ∫ y, Real.exp (a * Fn n y) ∂Pm) atTop
      (𝓝 (∫ y, Real.exp (a * F y) ∂Pm)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => K)
      (fun n => (hmeasE n).aestronglyMeasurable) (integrable_const K) (fun n => ?_) ?_
    · exact Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hexp n x
    · filter_upwards [hlim] with x hx
      exact ((Real.continuous_exp.tendsto _).comp (hx.const_mul a))
  have hIn : Tendsto (fun n => ∫ y, Real.exp (a * Fn n y) * φ y ∂Pm) atTop
      (𝓝 (∫ y, Real.exp (a * F y) * φ y ∂Pm)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => K * Cφ)
      (fun n => ((hmeasE n).mul hφ).aestronglyMeasurable) (integrable_const _) (fun n => ?_) ?_
    · refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (hexp n x) (hφb x) (abs_nonneg _) ((Real.exp_pos _).le.trans (hexp n x))
    · filter_upwards [hlim] with x hx
      exact ((Real.continuous_exp.tendsto _).comp (hx.const_mul a)).mul_const _
  have hZpos : 0 < ∫ y, Real.exp (a * F y) ∂Pm := by
    refine integral_exp_pos ?_
    exact Integrable.mono' (integrable_const K) hmeasEF.aestronglyMeasurable
      (hexpF.mono fun x hx => by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hx)
  have e1 : ∀ n, ∫ x, φ x ∂((ENNReal.ofReal (∫ y, Real.exp (a * Fn n y) ∂Pm))⁻¹ •
        Pm.withDensity (fun y => ENNReal.ofReal (Real.exp (a * Fn n y)))) =
      (∫ y, Real.exp (a * Fn n y) ∂Pm)⁻¹ * ∫ y, Real.exp (a * Fn n y) * φ y ∂Pm := fun n =>
    movc_gibbs_integral Pm _ φ (hmeasE n) (fun x => (Real.exp_pos _).le)
      (integral_nonneg fun x => (Real.exp_pos _).le)
  rw [movc_gibbs_integral Pm _ φ hmeasEF (fun x => (Real.exp_pos _).le) hZpos.le]
  simp_rw [e1]
  exact (hZn.inv₀ hZpos.ne').mul hIn

end HRS
