import HRS.PDE.MovCAux11

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movc_Emax_integrable {ρ : Torus d → ℝ} {Λ₀ : ℝ} (hΛ0 : 0 ≤ Λ₀) (hρΛ : ∀ x, ρ x ≤ Λ₀)
    (hρ : IsProbDensity ρ)
    {W : Torus d → ℝ} (hW : Integrable W) (hW0 : ∀ z, 0 ≤ W z) (hWm : Measurable W) :
    Integrable (fun X : Config d N => movc_Emax W X (withDensityReal ρ))
      (Measure.pi fun _ : Fin N => withDensityReal ρ) := by
  haveI := isProb_withDensityReal hρ
  have hkW : RowOK (withDensityReal ρ) (fun x y => W (x - y)) :=
    (rowOK_of_dom (k := fun x y => W (x - y)) hΛ0 hρΛ hW
      (hWm.comp (measurable_fst.sub measurable_snd))
      (fun x y => by rw [abs_of_nonneg (hW0 _)])).1
  have h1 := integrable_modulatedEnergy_pair (N := N) hkW
  have h2 : Integrable (fun X : Config d N => ∑ i, ∫ y, W (X i - y) ∂(withDensityReal ρ))
      (Measure.pi fun _ : Fin N => withDensityReal ρ) :=
    integrable_finsetSum _ fun i _ =>
      integrable_comp_eval (μ := fun _ : Fin N => withDensityReal ρ) (i := i) hkW.integrable_rowInt
  exact h1.add (h2.const_mul _)

/-- Gibbs expectation convergence with varying observables dominated by an integrable function. -/
theorem movc_gibbs_tendsto2 {α : Type*} [MeasurableSpace α] (Pm : Measure α)
    [IsProbabilityMeasure Pm] (a : ℝ) (ha : a ≤ 0) (Fn : ℕ → α → ℝ) (F : α → ℝ)
    (hFn : ∀ n, Measurable (Fn n)) (hF : Measurable F) (c : ℝ) (hc : ∀ n x, -c ≤ Fn n x)
    (hlim : ∀ᵐ x ∂Pm, Tendsto (fun n => Fn n x) atTop (𝓝 (F x)))
    (φn : ℕ → α → ℝ) (φ : α → ℝ) (hφn : ∀ n, Measurable (φn n)) (hφ : Measurable φ)
    (H : α → ℝ) (hH : Integrable H Pm) (hbd : ∀ n x, |φn n x| ≤ H x)
    (hφlim : ∀ᵐ x ∂Pm, Tendsto (fun n => φn n x) atTop (𝓝 (φ x))) :
    Tendsto (fun n => ∫ x, φn n x ∂((ENNReal.ofReal (∫ y, Real.exp (a * Fn n y) ∂Pm))⁻¹ •
        Pm.withDensity (fun y => ENNReal.ofReal (Real.exp (a * Fn n y))))) atTop
      (𝓝 (∫ x, φ x ∂((ENNReal.ofReal (∫ y, Real.exp (a * F y) ∂Pm))⁻¹ •
        Pm.withDensity (fun y => ENNReal.ofReal (Real.exp (a * F y)))))) := by
  set K := Real.exp (-a * c) with hK
  have hexp : ∀ n x, Real.exp (a * Fn n x) ≤ K := fun n x => by
    rw [hK]; apply Real.exp_le_exp.2; nlinarith [hc n x]
  have hmeasE : ∀ n, Measurable (fun x => Real.exp (a * Fn n x)) := fun n =>
    Real.measurable_exp.comp (measurable_const.mul (hFn n))
  have hmeasEF : Measurable (fun x => Real.exp (a * F x)) :=
    Real.measurable_exp.comp (measurable_const.mul hF)
  obtain ⟨hZn, hZ, hZt⟩ := movc_gibbs_Z Pm a Fn F hFn hF c hc hlim ha
  have hφb : ∀ᵐ x ∂Pm, |φ x| ≤ H x :=
    hφlim.mono fun x hx => le_of_tendsto' hx.abs (fun n => hbd n x)
  have hIn : Tendsto (fun n => ∫ y, Real.exp (a * Fn n y) * φn n y ∂Pm) atTop
      (𝓝 (∫ y, Real.exp (a * F y) * φ y ∂Pm)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => K * H x)
      (fun n => ((hmeasE n).mul (hφn n)).aestronglyMeasurable) (hH.const_mul K) (fun n => ?_) ?_
    · refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (hexp n x) (hbd n x) (abs_nonneg _) ((Real.exp_pos _).le.trans (hexp n x))
    · filter_upwards [hlim, hφlim] with x hx hx'
      exact ((Real.continuous_exp.tendsto _).comp (hx.const_mul a)).mul hx'
  have e1 : ∀ n, ∫ x, φn n x ∂((ENNReal.ofReal (∫ y, Real.exp (a * Fn n y) ∂Pm))⁻¹ •
        Pm.withDensity (fun y => ENNReal.ofReal (Real.exp (a * Fn n y)))) =
      (∫ y, Real.exp (a * Fn n y) ∂Pm)⁻¹ * ∫ y, Real.exp (a * Fn n y) * φn n y ∂Pm := fun n =>
    movc_gibbs_integral Pm _ (φn n) (hmeasE n) (fun x => (Real.exp_pos _).le)
      (integral_nonneg fun x => (Real.exp_pos _).le)
  rw [movc_gibbs_integral Pm _ φ hmeasEF (fun x => (Real.exp_pos _).le) hZ.le]
  simp_rw [e1]
  exact (hZt.inv₀ hZ.ne').mul hIn

end HRS
