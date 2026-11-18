import HRS.MS.S82P2Cent4

/-!
# S8.2 (S82P2): domination function and the vanishing of the small-ball constant
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

lemma s82p2_Bf_integrable {d : ℕ} (hd : 2 ≤ d) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A) (G c : ℝ)
    (hG : 0 < G) (hc : 0 < c) (rho : Euc d → ℝ) (hρ : HRS.Whole.IsProbDensity rho)
    (hρG : HRS.Whole.HasR2GaussianUpper G c rho) (x : Euc d) :
    Integrable (fun z => A * ((2 * jbracket x) ^ M * jbracket z ^ M) *
      (1 + 2 ^ (criticalS d - 1) * smallRadius x z ^ (1 - criticalS d)))
      (HRS.Whole.withDensityReal rho) := by
  have hs1 : 1 ≤ criticalS d := by
    unfold criticalS
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hjb : Measurable (fun x : Euc d => jbracket x) := by unfold jbracket; fun_prop
  have hsr : Measurable (fun z : Euc d => smallRadius x z) := by
    unfold smallRadius; fun_prop
  have hm : Measurable (fun z : Euc d => A * ((2 * jbracket x) ^ M * jbracket z ^ M) *
      (1 + 2 ^ (criticalS d - 1) * smallRadius x z ^ (1 - criticalS d))) :=
    measurable_const.mul (measurable_const.mul (hjb.pow_const M)) |>.mul
      (measurable_const.add (measurable_const.mul (hsr.pow_const _)))
  have hE2 := HRS.MS.S82N.s82n_E2 hd M G c 1 hM hG.le hc one_pos le_rfl rho hρ hρG x
  set K : ℝ := A * (2 * jbracket x) ^ M * 2 ^ (criticalS d - 1) with hK
  have hK0 : 0 ≤ K := by
    have := Real.rpow_nonneg (by have := HRS.MS.S82N.s82n_jb_pos x; linarith : 0 ≤ 2 * jbracket x) M
    rw [hK]; positivity
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => ?_)]
  · calc ∫⁻ z, ENNReal.ofReal (A * ((2 * jbracket x) ^ M * jbracket z ^ M) *
          (1 + 2 ^ (criticalS d - 1) * smallRadius x z ^ (1 - criticalS d)))
          ∂HRS.Whole.withDensityReal rho
        ≤ ∫⁻ z, ENNReal.ofReal K * ENNReal.ofReal (jbracket z ^ M *
            ((1 + HRS.MS.S82N.s82n_smallRadius x z ^ (1 - HRS.MS.S82N.s82n_critS d)) *
              HRS.MS.S82N.s82n_pole x z)) ∂HRS.Whole.withDensityReal rho := by
          refine lintegral_mono fun z => ?_
          rw [← ENNReal.ofReal_mul hK0]
          apply ENNReal.ofReal_le_ofReal
          have hr0 : 0 ≤ smallRadius x z := le_min zero_le_one (norm_nonneg _)
          have hr1 : 0 ≤ smallRadius x z ^ (1 - criticalS d) := Real.rpow_nonneg hr0 _
          have hp : 1 ≤ HRS.MS.S82N.s82n_pole x z := by
            unfold HRS.MS.S82N.s82n_pole
            have : 0 ≤ HRS.MS.S82N.s82n_smallRadius x z ^ (-HRS.MS.S82N.s82n_critS d) :=
              Real.rpow_nonneg (le_min zero_le_one (norm_nonneg _)) _
            linarith
          have hc1 : (1 : ℝ) ≤ 2 ^ (criticalS d - 1) :=
            Real.one_le_rpow (by norm_num) (by linarith)
          have hjz := s82p2_jb_rpow_nonneg M z
          have hjx := s82p2_jb_rpow_nonneg M x
          have h1 : 1 + 2 ^ (criticalS d - 1) * smallRadius x z ^ (1 - criticalS d) ≤
              2 ^ (criticalS d - 1) * ((1 + HRS.MS.S82N.s82n_smallRadius x z ^ (1 - HRS.MS.S82N.s82n_critS d)) *
                HRS.MS.S82N.s82n_pole x z) := by
            show 1 + 2 ^ (criticalS d - 1) * smallRadius x z ^ (1 - criticalS d) ≤
              2 ^ (criticalS d - 1) * ((1 + smallRadius x z ^ (1 - criticalS d)) *
                HRS.MS.S82N.s82n_pole x z)
            nlinarith [mul_nonneg (sub_nonneg.2 hp) (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 ^ (criticalS d - 1))
              (by linarith : 0 ≤ 1 + smallRadius x z ^ (1 - criticalS d)))]
          have hApw : 0 ≤ A * ((2 * jbracket x) ^ M * jbracket z ^ M) := by
            have := Real.rpow_nonneg (by have := HRS.MS.S82N.s82n_jb_pos x; linarith : 0 ≤ 2 * jbracket x) M
            positivity
          calc A * ((2 * jbracket x) ^ M * jbracket z ^ M) *
                (1 + 2 ^ (criticalS d - 1) * smallRadius x z ^ (1 - criticalS d))
              ≤ A * ((2 * jbracket x) ^ M * jbracket z ^ M) * (2 ^ (criticalS d - 1) *
                ((1 + HRS.MS.S82N.s82n_smallRadius x z ^ (1 - HRS.MS.S82N.s82n_critS d)) *
                  HRS.MS.S82N.s82n_pole x z)) := mul_le_mul_of_nonneg_left h1 hApw
            _ = K * (jbracket z ^ M * ((1 + HRS.MS.S82N.s82n_smallRadius x z ^
                (1 - HRS.MS.S82N.s82n_critS d)) * HRS.MS.S82N.s82n_pole x z)) := by
                rw [hK]; ring
      _ = ENNReal.ofReal K * ∫⁻ z, ENNReal.ofReal (jbracket z ^ M *
            ((1 + HRS.MS.S82N.s82n_smallRadius x z ^ (1 - HRS.MS.S82N.s82n_critS d)) *
              HRS.MS.S82N.s82n_pole x z)) ∂HRS.Whole.withDensityReal rho :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (lt_of_le_of_lt (by simpa using hE2) ENNReal.ofReal_lt_top)
  · have hjz := s82p2_jb_rpow_nonneg M z
    have hjx := s82p2_jb_rpow_nonneg M x
    have hr0 : 0 ≤ smallRadius x z := le_min zero_le_one (norm_nonneg _)
    have := Real.rpow_nonneg hr0 (1 - criticalS d)
    have h2 : 0 ≤ (2 : ℝ) ^ (criticalS d - 1) := Real.rpow_nonneg (by norm_num) _
    have hjx2 := Real.rpow_nonneg (by have := HRS.MS.S82N.s82n_jb_pos x; linarith : 0 ≤ 2 * jbracket x) M
    positivity

/-- The small-ball constant over `t` tends to zero. -/
lemma s82p2_E_tendsto {d : ℕ} (hd : 2 ≤ d) (G K1 : ℝ) :
    Tendsto (fun t : ℝ => t⁻¹ * K1 * (s82p2_ballB d G (2 * t) + s82p2_ballB d G (3 * t)))
      (𝓝[>] 0) (𝓝 0) := by
  have hs0 : 0 < criticalS d := by
    unfold criticalS
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set κ : ℝ := (d : ℝ) * (volume : Measure (Euc d)).real (Metric.ball (0 : Euc d) 1) with hκ
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hs1 : criticalS d + 1 ≠ 0 := by linarith
  set ψ : ℝ → ℝ := fun t => K1 * G * κ * (((2 : ℝ) ^ d / d + 3 ^ d / d) * t ^ (d - 1) +
    ((2 : ℝ) ^ (criticalS d + 1) + 3 ^ (criticalS d + 1)) / (criticalS d + 1) * t ^ criticalS d)
    with hψ
  have hcont : Continuous ψ := by
    refine continuous_const.mul (Continuous.add (continuous_const.mul (continuous_pow _))
      (continuous_const.mul (Real.continuous_rpow_const hs0.le)))
  have hψ0 : ψ 0 = 0 := by
    simp only [hψ]
    rw [zero_pow (by omega), Real.zero_rpow hs0.ne']
    ring
  have hlim : Tendsto ψ (𝓝[>] 0) (𝓝 0) := by
    have := hcont.tendsto 0
    rw [hψ0] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  symm
  simp only [hψ, s82p2_ballB]
  have e1 : (2 * t) ^ d = 2 ^ d * t ^ (d - 1) * t := by
    rw [mul_pow, mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega)]
  have e2 : (3 * t) ^ d = 3 ^ d * t ^ (d - 1) * t := by
    rw [mul_pow, mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega)]
  have e3 : (2 * t) ^ (criticalS d + 1) = 2 ^ (criticalS d + 1) * t ^ criticalS d * t := by
    rw [Real.mul_rpow (by norm_num) ht0.le, Real.rpow_add_one ht0.ne']; ring
  have e4 : (3 * t) ^ (criticalS d + 1) = 3 ^ (criticalS d + 1) * t ^ criticalS d * t := by
    rw [Real.mul_rpow (by norm_num) ht0.le, Real.rpow_add_one ht0.ne']; ring
  rw [e1, e2, e3, e4]
  field_simp
  ring

end HRS.MS.S82P2
