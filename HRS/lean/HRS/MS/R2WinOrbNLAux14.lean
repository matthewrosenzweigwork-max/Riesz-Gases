import HRS.MS.R2WinOrbNLAux13

/-!
# S10.3 (nonlinear branch), part 14: dominated convergence for the cancellation convolution, and the right time derivative of `∇g*(ρ_τ w)`

Prefix `s103n_`, namespace `HRS.MS.R2WinOrbNL`.

* `s103n_ultK_tendsto`: if `g_τ → g_0` pointwise along a filter, with `g_τ` uniformly Lipschitz and uniformly dominated by `A (1+‖y‖)^{-L}`, then
  `ultK κ g_τ x → ultK κ g_0 x` (the near part is dominated by `C₀ B ‖z‖^{-s}` on the unit ball, the far part by `A |κ_F(z)| ⟨x-z⟩^{-L}`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

theorem s103n_ultK_tendsto (hd : 1 ≤ d) {κ : Euc d → ℝ} {s : ℝ} (hK : UlKer κ s) {L A B : ℝ}
    (hL : (d : ℝ) < L) (hA : 0 ≤ A) (hB : 0 ≤ B) {l : Filter ℝ} [l.IsCountablyGenerated]
    (g : ℝ → Euc d → ℝ) (g0 : Euc d → ℝ) (x : Euc d)
    (hc : ∀ᶠ τ in l, Continuous (g τ)) (hLip : ∀ᶠ τ in l, ∀ a b, ‖g τ a - g τ b‖ ≤ B * ‖a - b‖)
    (hdec : ∀ᶠ τ in l, ∀ y, ‖g τ y‖ ≤ A * u2Wt L y)
    (hlim : ∀ y, Tendsto (fun τ => g τ y) l (𝓝 (g0 y))) :
    Tendsto (fun τ => ultK κ (g τ) x) l (𝓝 (ultK κ g0 x)) := by
  obtain ⟨C0, hC0, hb⟩ := ult_ker_bound hK
  unfold ultK ultNear u2Conv
  refine Tendsto.add ?_ ?_
  · refine tendsto_integral_filter_of_dominated_convergence
      (fun z => C0 * B * (ball (0 : Euc d) 1).indicator (fun z => ‖z‖ ^ (-s)) z) ?_ ?_
      ((ult_Phi_int hd hK).const_mul (C0 * B)) ?_
    · filter_upwards [hc] with τ hτ using ult_near_meas hK.meas hτ x
    · filter_upwards [hLip] with τ hτ
      filter_upwards [u2_ae_ne_zero hd] with z hz
      refine ult_near_dom hC0 hb hB hz ?_
      have := hτ (x - z) x
      simpa using this
    · exact Filter.Eventually.of_forall fun z => ((hlim (x - z)).sub (hlim x)).const_smul _
  · have hker := ult_far_U2Ker hd hK
    refine tendsto_integral_filter_of_dominated_convergence
      (fun z => A * (‖ultKF κ z‖ * u2Wt L (x - z))) ?_ ?_ ((u2_wt_translate_int hker hL x).const_mul A) ?_
    · filter_upwards [hc] with τ hτ
      exact hker.meas.aestronglyMeasurable.smul
        (hτ.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · filter_upwards [hdec] with τ hτ
      refine Filter.Eventually.of_forall fun z => ?_
      rw [norm_smul]
      calc ‖ultKF κ z‖ * ‖g τ (x - z)‖ ≤ ‖ultKF κ z‖ * (A * u2Wt L (x - z)) :=
            mul_le_mul_of_nonneg_left (hτ (x - z)) (norm_nonneg _)
        _ = A * (‖ultKF κ z‖ * u2Wt L (x - z)) := by ring
    · exact Filter.Eventually.of_forall fun z => (hlim (x - z)).const_smul _

end HRS.MS.R2WinOrbNL

end
