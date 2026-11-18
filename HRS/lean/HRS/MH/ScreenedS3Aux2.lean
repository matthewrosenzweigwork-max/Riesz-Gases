import HRS.MH.ScreenedS3Aux1

/-!
# Packet S3, part 2: the `ξ`-side limit and the logarithmic case

`s3_zero_case`: from the Riesz identity `A(s) ∫ ‖x‖^{-s} Θ = B(s) ∫ ‖ξ‖^{s-d} Φ` for `0 < s < d` and `∫ Θ = 0`,
`‖Φ ξ‖ ≤ ‖ξ‖ ‖G ξ‖` (`G` Schwartz), deduce `∫ (-log‖x‖) Θ = (B(0)/2) ∫ ‖ξ‖^{-d} Φ`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

/-- The `ξ`-side limit. -/
lemma s3_lim_xi (hd : 1 ≤ d) (Φ : Euc d → ℂ) (hΦ : Continuous Φ) (G : SchwartzMap (Euc d) ℂ)
    (hG : ∀ ξ, ‖Φ ξ‖ ≤ ‖ξ‖ * ‖G ξ‖) :
    Tendsto (fun s : ℝ => ∫ ξ : Euc d, ((‖ξ‖ ^ (s - d) : ℝ) : ℂ) * Φ ξ) (𝓝[>] 0)
      (𝓝 (∫ ξ : Euc d, ((‖ξ‖ ^ ((0 : ℝ) - d) : ℝ) : ℂ) * Φ ξ)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hb1 := s3_integrable_rpow_norm hd (a := 1 - (d : ℝ)) (by linarith) (by linarith) G
  have hb2 := G.integrable_pow_mul volume 1
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ξ : Euc d => ‖ξ‖ ^ (1 - (d : ℝ)) * ‖G ξ‖ + ‖ξ‖ ^ 1 * ‖G ξ‖) ?_ ?_ (hb1.add hb2) ?_
  · refine Eventually.of_forall fun s => ?_
    refine Measurable.aestronglyMeasurable ?_
    exact (Complex.measurable_ofReal.comp (measurable_norm.pow_const _)).mul hΦ.measurable
  · filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with s hs
    filter_upwards [HRS.Commutator.Whole.ae_ne_zero_euc hd] with ξ hξ
    have hr : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hr.le _)]
    have h1 : ‖ξ‖ ^ (s - d) * ‖Φ ξ‖ ≤ ‖ξ‖ ^ (s - d + 1) * ‖G ξ‖ := by
      rw [Real.rpow_add_one hr.ne']
      calc ‖ξ‖ ^ (s - d) * ‖Φ ξ‖ ≤ ‖ξ‖ ^ (s - d) * (‖ξ‖ * ‖G ξ‖) :=
            mul_le_mul_of_nonneg_left (hG ξ) (Real.rpow_nonneg hr.le _)
        _ = _ := by ring
    have h2 : ‖ξ‖ ^ (s - d + 1) ≤ ‖ξ‖ ^ (1 - (d : ℝ)) + ‖ξ‖ ^ 1 := by
      have hp1 : 0 ≤ ‖ξ‖ ^ (1 - (d : ℝ)) := Real.rpow_nonneg hr.le _
      have hp2 : 0 ≤ ‖ξ‖ ^ 1 := by positivity
      rcases le_or_gt ‖ξ‖ 1 with h | h
      · have := Real.rpow_le_rpow_of_exponent_ge hr h (show 1 - (d : ℝ) ≤ s - d + 1 by linarith [hs.1])
        linarith
      · have := Real.rpow_le_rpow_of_exponent_le h.le (show s - d + 1 ≤ (1 : ℝ) by linarith [hs.2])
        rw [Real.rpow_one] at this
        rw [pow_one]
        linarith
    calc ‖ξ‖ ^ (s - d) * ‖Φ ξ‖ ≤ ‖ξ‖ ^ (s - d + 1) * ‖G ξ‖ := h1
      _ ≤ (‖ξ‖ ^ (1 - (d : ℝ)) + ‖ξ‖ ^ 1) * ‖G ξ‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = _ := by ring
  · filter_upwards [HRS.Commutator.Whole.ae_ne_zero_euc hd] with ξ hξ
    have hr : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.2 hξ
    have hc : Continuous fun s : ℝ => ‖ξ‖ ^ (s - d) :=
      continuous_const.rpow (continuous_id.sub continuous_const) (fun _ => Or.inl hr)
    exact ((Complex.continuous_ofReal.comp hc).tendsto 0 |>.mono_left nhdsWithin_le_nhds).mul_const _

/-- Logarithmic case from the Riesz identity for `s > 0`. -/
lemma s3_zero_case (hd : 1 ≤ d) (Θ Φ0 : Euc d → ℂ) (Θs : SchwartzMap (Euc d) ℂ) (hΘ : ⇑Θs = Θ)
    (hΦ : Continuous Φ0) (G : SchwartzMap (Euc d) ℂ) (hG : ∀ ξ, ‖Φ0 ξ‖ ≤ ‖ξ‖ * ‖G ξ‖)
    (hint : ∫ x : Euc d, Θ x = 0)
    (hriesz : ∀ s : ℝ, 0 < s → s < d →
      (s3A s : ℂ) * ∫ x : Euc d, ((‖x‖ ^ (-s) : ℝ) : ℂ) * Θ x =
        (s3B d s : ℂ) * ∫ ξ : Euc d, ((‖ξ‖ ^ (s - d) : ℝ) : ℂ) * Φ0 ξ) :
    ∫ x : Euc d, ((-Real.log ‖x‖ : ℝ) : ℂ) * Θ x =
      ((s3B d 0 / 2 : ℝ) : ℂ) * ∫ ξ : Euc d, ((‖ξ‖ ^ ((0 : ℝ) - d) : ℝ) : ℂ) * Φ0 ξ := by
  subst hΘ
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hx := s3_lim_x hd Θs
  have hξ := s3_lim_xi hd Φ0 hΦ G hG
  have hκ := (Complex.continuous_ofReal.tendsto _).comp (s3_tendsto_kappa hd (d := d))
  have hprod := hκ.mul hξ
  refine tendsto_nhds_unique (hx.congr' ?_) hprod
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with s hs
  have hs0 : 0 < s := hs.1
  have hsd : s < d := by linarith [hs.2]
  have hA := s3A_pos hs0
  have hi1 : Integrable (fun x : Euc d => ((‖x‖ ^ (-s) : ℝ) : ℂ) * Θs x) :=
    s3_integrable_rpow_mul hd (by linarith) (by linarith) Θs
  have hi2 : Integrable (fun x : Euc d => Θs x) := Θs.integrable
  have hsplit : ∫ x : Euc d, (((‖x‖ ^ (-s) - 1) / s : ℝ) : ℂ) * Θs x =
      (1 / (s : ℂ)) * ((∫ x : Euc d, ((‖x‖ ^ (-s) : ℝ) : ℂ) * Θs x) - ∫ x : Euc d, Θs x) := by
    rw [← integral_sub hi1 hi2, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    push_cast
    ring
  rw [hsplit, hint, sub_zero]
  have hAne : (s3A s : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have hsne : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have h1 : ∫ x : Euc d, ((‖x‖ ^ (-s) : ℝ) : ℂ) * Θs x =
      (s3B d s : ℂ) / (s3A s : ℂ) * ∫ ξ : Euc d, ((‖ξ‖ ^ (s - d) : ℝ) : ℂ) * Φ0 ξ := by
    rw [div_mul_eq_mul_div, eq_div_iff hAne, mul_comm, hriesz s hs0 hsd]
  rw [h1]
  simp only [Function.comp_apply]
  push_cast
  field_simp

end HRS.MH.Screened
