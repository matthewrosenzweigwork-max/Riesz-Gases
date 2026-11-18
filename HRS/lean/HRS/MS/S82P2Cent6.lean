import HRS.MS.S82P2Cent5

/-!
# S8.2 (S82P2): centering of the corrector gradient, `∫ ∇_x Q(x,z) dmu(z) = 0` for every `x`
Differentiation of the canonical row under the integral: dominated convergence away from the
diagonal and a small-ball estimate near it.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

theorem s82p2_centering_dir {d : ℕ} (hd : 2 ≤ d) {a beta M A : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A)
    (G c : ℝ) (hG : 0 < G) (hc : 0 < c) {rho : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity rho) (hρG : HRS.Whole.HasR2GaussianUpper G c rho)
    {f : Euc d → ℝ} {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q)
    (x v : Euc d) (hv : ‖v‖ = 1) :
    ∫ z, inner ℝ (s82p2_gt Q x z) v ∂HRS.Whole.withDensityReal rho = 0 := by
  set mu := HRS.Whole.withDensityReal rho with hmu
  have hs1 : 1 ≤ criticalS d := by
    unfold criticalS
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  -- the step sizes
  set t : ℕ → ℝ := fun n => 1 / (((n + 7 : ℕ) : ℝ) + 1) with ht
  have ht0 : ∀ n, 0 < t n := fun n => by simp only [ht]; positivity
  have ht1 : ∀ n, t n ≤ 1 / 8 := fun n => by
    simp only [ht]
    rw [one_div_le_one_div (by positivity) (by norm_num)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    push_cast; linarith
  have htlim : Tendsto t atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 7)
  have htne : Tendsto t atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨htlim, Eventually.of_forall fun n => (ht0 n).ne'⟩
  have htpos : Tendsto t atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨htlim, Eventually.of_forall fun n => ht0 n⟩
  set D : ℕ → Euc d → ℝ := fun n z => (t n)⁻¹ * (Q (x + t n • v) z - Q x z) with hD
  set S : ℕ → Set (Euc d) := fun n => {z | 2 * t n ≤ ‖z - x‖} with hS
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    measurableSet_le measurable_const (measurable_norm.comp (measurable_id.sub_const x))
  have hSc : ∀ n, (S n)ᶜ = Metric.ball x (2 * t n) := fun n => by
    ext z; simp [hS, Metric.mem_ball, dist_eq_norm, not_le]
  have hDm : ∀ n, Measurable (D n) := fun n =>
    measurable_const.mul ((s82p2_Q_row_measurable hQ _).sub (s82p2_Q_row_measurable hQ x))
  have hDi : ∀ n, Integrable (D n) mu := fun n =>
    ((hQ.canonical.2.1 (x + t n • v)).sub (hQ.canonical.2.1 x)).const_mul _
  have hD0 : ∀ n, ∫ z, D n z ∂mu = 0 := fun n => by
    simp only [hD]
    rw [integral_const_mul, integral_sub (hQ.canonical.2.1 _) (hQ.canonical.2.1 x),
      hQ.canonical.2.2.2, hQ.canonical.2.2.2]
    simp
  set F : ℕ → Euc d → ℝ := fun n => (S n).indicator (D n) with hF
  -- far part converges to the integral of the derivative
  have hfar : Tendsto (fun n => ∫ z, F n z ∂mu) atTop
      (𝓝 (∫ z, inner ℝ (s82p2_gt Q x z) v ∂mu)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun z => A * ((2 * jbracket x) ^ M * jbracket z ^ M) *
        (1 + 2 ^ (criticalS d - 1) * smallRadius x z ^ (1 - criticalS d)))
      (fun n => ((hDm n).indicator (hSm n)).aestronglyMeasurable)
      (s82p2_Bf_integrable hd M A hM hA G c hG hc rho hρ hρG x) ?_ ?_
    · intro n
      refine Eventually.of_forall fun z => ?_
      by_cases hz : z ∈ S n
      · simp only [hF, Set.indicator_of_mem hz, Real.norm_eq_abs, hD]
        have hz' : 2 * |t n| ≤ ‖z - x‖ := by rw [abs_of_pos (ht0 n)]; exact hz
        have := s82p2_Q_segment hd hM hA hQ x z v hv (t := t n) (by rw [abs_of_pos (ht0 n)]; exact ht0 n)
          (by rw [abs_of_pos (ht0 n)]; linarith [ht1 n]) hz'
        rw [abs_mul, abs_of_pos (inv_pos.2 (ht0 n))]
        rw [abs_of_pos (ht0 n)] at this
        calc (t n)⁻¹ * |Q (x + t n • v) z - Q x z|
            ≤ (t n)⁻¹ * (t n * _) := mul_le_mul_of_nonneg_left this (inv_pos.2 (ht0 n)).le
          _ = _ := by field_simp [(ht0 n).ne']
      · simp only [hF, Set.indicator_of_notMem hz, norm_zero]
        have hjx := Real.rpow_nonneg (by have := HRS.MS.S82N.s82n_jb_pos x; linarith : 0 ≤ 2 * jbracket x) M
        have hjz := s82p2_jb_rpow_nonneg M z
        have hr0 : 0 ≤ smallRadius x z := le_min zero_le_one (norm_nonneg _)
        have h1 := Real.rpow_nonneg hr0 (1 - criticalS d)
        have h2 : 0 ≤ (2 : ℝ) ^ (criticalS d - 1) := Real.rpow_nonneg (by norm_num) _
        positivity
    · have hne : ∀ᵐ z ∂mu, z ≠ x := by
        rw [ae_iff]; simpa using s82p2_mu_singleton hd rho x
      filter_upwards [hne] with z hz
      have hsl := (s82p2_slope_tendsto hQ x z v (Ne.symm hz)).comp htne
      have hev : ∀ᶠ n in atTop, 2 * t n < ‖z - x‖ := by
        have hpos : 0 < ‖z - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
        have h2 : Tendsto (fun n => 2 * t n) atTop (𝓝 0) := by simpa using htlim.const_mul 2
        exact h2.eventually (gt_mem_nhds hpos)
      refine hsl.congr' ?_
      filter_upwards [hev] with n hn
      simp only [Function.comp, hF, hD]
      rw [Set.indicator_of_mem (show z ∈ S n from le_of_lt hn)]
  -- near part tends to zero
  have hnear : Tendsto (fun n => ∫ z in Metric.ball x (2 * t n), D n z ∂mu) atTop (𝓝 0) := by
    obtain ⟨E, hE⟩ : ∃ E : ℕ → ℝ, E = fun n => (t n)⁻¹ * (2 * A * ((2 * jbracket x) ^ M *
        (2 * jbracket x) ^ M)) * (s82p2_ballB d G (2 * t n) + s82p2_ballB d G (3 * t n)) := ⟨_, rfl⟩
    have hEt : Tendsto E atTop (𝓝 0) := by
      rw [hE]
      exact (s82p2_E_tendsto hd G (2 * A * ((2 * jbracket x) ^ M * (2 * jbracket x) ^ M))).comp htpos
    refine squeeze_zero_norm (fun n => ?_) hEt
    have hb := s82p2_near_bound hd hM hA G c hG hc hρ hρG hQ x v hv (ht0 n) (ht1 n)
    have hn := norm_integral_le_lintegral_norm (μ := mu.restrict (Metric.ball x (2 * t n))) (D n)
    have hBn : 0 ≤ E n := by
      rw [hE]
      have hB0 : ∀ r : ℝ, 0 ≤ r → 0 ≤ s82p2_ballB d G r := fun r hr => by
        unfold s82p2_ballB
        have hs0 : 0 < criticalS d := by linarith
        have : 0 ≤ (volume : Measure (Euc d)).real (Metric.ball (0 : Euc d) 1) := measureReal_nonneg
        positivity
      have hjx := Real.rpow_nonneg (by have := HRS.MS.S82N.s82n_jb_pos x; linarith : 0 ≤ 2 * jbracket x) M
      have := hB0 (2 * t n) (by have := ht0 n; positivity)
      have := hB0 (3 * t n) (by have := ht0 n; positivity)
      have := ht0 n
      positivity
    refine hn.trans ?_
    have hle : ∫⁻ z, ENNReal.ofReal ‖D n z‖ ∂(mu.restrict (Metric.ball x (2 * t n))) ≤
        ENNReal.ofReal (E n) := by
      simpa [hD, hE, Real.norm_eq_abs] using hb
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans (by rw [ENNReal.toReal_ofReal hBn])
  -- combine
  have hsum : ∀ n, ∫ z, F n z ∂mu = - ∫ z in Metric.ball x (2 * t n), D n z ∂mu := fun n => by
    have h1 := integral_add_compl (hSm n) (hDi n)
    rw [hSc n, hD0 n] at h1
    have h2 : ∫ z, F n z ∂mu = ∫ z in S n, D n z ∂mu := integral_indicator (hSm n)
    rw [h2]
    linarith
  have hfar' : Tendsto (fun n => ∫ z, F n z ∂mu) atTop (𝓝 0) := by
    have := hnear.neg
    simp only [neg_zero] at this
    exact this.congr fun n => (hsum n).symm
  exact tendsto_nhds_unique hfar hfar'

end HRS.MS.S82P2
