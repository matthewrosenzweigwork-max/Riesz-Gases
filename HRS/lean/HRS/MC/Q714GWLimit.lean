import HRS.Sections.QuenchAux6

/-!
# Packet GW (row 7.14): a.s. limits of centred Gaussians

`gw_gauss_limit`: an a.s. limit of centred real Gaussians is a centred real Gaussian (no assumption on the variances;
convergence of the variances is a consequence, by continuity of the characteristic function at `0`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MC.Q714.GW

theorem gw_gauss_limit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {V : ℕ → Ω → ℝ} {W : Ω → ℝ} {v : ℕ → ℝ≥0}
    (hV : ∀ n, P.map (V n) = gaussianReal 0 (v n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => V n ω) atTop (𝓝 (W ω)))
    (hW : AEMeasurable W P) (hVm : ∀ n, AEMeasurable (V n) P) :
    ∃ v₀ : ℝ≥0, P.map W = gaussianReal 0 v₀ := by
  haveI : IsProbabilityMeasure (P.map W) := ⟨by simp [Measure.map_apply_of_aemeasurable hW MeasurableSet.univ]⟩
  -- characteristic functions converge
  have hchar : ∀ t : ℝ, Tendsto (fun n => Complex.exp (-(v n : ℝ) * t ^ 2 / 2)) atTop
      (𝓝 (charFun (P.map W) t)) := by
    intro t
    rw [charFun_apply_real, integral_map hW (by fun_prop)]
    have h1 : Tendsto (fun n => ∫ ω, Complex.exp (t * V n ω * Complex.I) ∂P) atTop
        (𝓝 (∫ ω, Complex.exp (t * W ω * Complex.I) ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => 1) (fun n => ?_) (integrable_const _)
        (fun n => ?_) ?_
      · exact ((Complex.continuous_exp.comp (by fun_prop : Continuous fun x : ℝ => (t : ℂ) * x * Complex.I)).measurable.comp_aemeasurable
          (hVm n)).aestronglyMeasurable
      · refine Eventually.of_forall fun ω => ?_
        have : (t : ℂ) * (V n ω) * Complex.I = ((t * V n ω : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I]
      · filter_upwards [hlim] with ω hω
        exact (Complex.continuous_exp.tendsto _).comp
          (((Complex.continuous_ofReal.tendsto _).comp hω).const_mul (t : ℂ) |>.mul_const Complex.I)
    have h2 : ∀ n, ∫ ω, Complex.exp (t * V n ω * Complex.I) ∂P =
        Complex.exp (-(v n : ℝ) * t ^ 2 / 2) := by
      intro n
      have := charFun_gaussianReal (μ := 0) (v := v n) t
      rw [← hV n, charFun_apply_real, integral_map (hVm n) (by fun_prop)] at this
      rw [this]
      congr 1
      simp
      ring
    simpa only [h2] using h1
  -- real shadows
  have hreal : ∀ t : ℝ, Tendsto (fun n => Real.exp (-(v n : ℝ) * t ^ 2 / 2)) atTop
      (𝓝 ‖charFun (P.map W) t‖) := by
    intro t
    have := (hchar t).norm
    refine this.congr fun n => ?_
    have : Complex.exp (-(v n : ℝ) * t ^ 2 / 2) = ((Real.exp (-(v n : ℝ) * t ^ 2 / 2) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]; push_cast; ring_nf
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  have h1 := hreal 1
  set c : ℝ := ‖charFun (P.map W) 1‖ with hc
  by_cases hc0 : c = 0
  · exfalso
    have hz : ∀ t : ℝ, t ≠ 0 → ‖charFun (P.map W) t‖ = 0 := by
      intro t ht
      have ht2 : 0 < t ^ 2 := by positivity
      have hx : Tendsto (fun n => Real.exp (-(v n : ℝ) / 2)) atTop (𝓝 0) := by
        have h1' : Tendsto (fun n => Real.exp (-(v n : ℝ) * 1 ^ 2 / 2)) atTop (𝓝 0) := by
          rw [← hc0]; exact h1
        refine h1'.congr fun n => ?_
        congr 1; ring
      have hp : Tendsto (fun n => (Real.exp (-(v n : ℝ) / 2)) ^ (t ^ 2)) atTop (𝓝 ((0 : ℝ) ^ (t ^ 2))) :=
        hx.rpow_const (Or.inr ht2.le)
      rw [Real.zero_rpow ht2.ne'] at hp
      have hp' : Tendsto (fun n => Real.exp (-(v n : ℝ) * t ^ 2 / 2)) atTop (𝓝 0) := by
        refine hp.congr fun n => ?_
        rw [← Real.exp_mul]; congr 1; ring
      exact tendsto_nhds_unique (hreal t) hp'
    have hcont : Continuous fun t : ℝ => ‖charFun (P.map W) t‖ := continuous_charFun.norm
    have h0 : ‖charFun (P.map W) 0‖ = 1 := by
      rw [charFun_zero]; simp
    have hlim0 : Tendsto (fun t : ℝ => ‖charFun (P.map W) t‖) (𝓝[≠] 0) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hz t ht).symm
    have := tendsto_nhds_unique (hcont.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ)) ) hlim0
    rw [h0] at this
    exact one_ne_zero this
  · have hcpos : 0 < c := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hc0)
    have hlog : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 (-2 * Real.log c)) := by
      have h1' : Tendsto (fun n => Real.exp (-(v n : ℝ) * 1 ^ 2 / 2)) atTop (𝓝 c) := h1
      have := (Real.continuousAt_log hcpos.ne').tendsto.comp h1'
      refine (this.const_mul (-2)).congr fun n => ?_
      simp only [Function.comp_apply, Real.log_exp]; ring
    have hv : Tendsto v atTop (𝓝 (Real.toNNReal (-2 * Real.log c))) := by
      have := (continuous_real_toNNReal.tendsto _).comp hlog
      refine this.congr fun n => ?_
      simp
    exact ⟨_, HRS.Qch.gauss_limit P hV hv hlim hW hVm⟩

end HRS.MC.Q714.GW
