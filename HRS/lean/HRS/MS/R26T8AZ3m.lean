import HRS.MS.R26T8AZ3
import HRS.MS.R26T8AN2

/-!
# S8.2 T8A Z3m: `r26t8a_Z3_conv_hasFDeriv`
For `G` supported in `|w| ≤ 2`, `C^1` off `0`, `|G| ≤ c0`, `‖DG(w)‖ ≤ c1 |w|^{-s1}` (`0 < s1 < d`) and `z ≠ 0`:
`HasFDerivAt (z' ↦ ∫ K(z'-v) G(v) dv) (∫ K(z-v) • DG(v) dv) z`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem r26t8a_Z3_conv_hasFDeriv (hd : 2 ≤ d) (nu : ℝ) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi)
    {G : Euc d → ℝ} (hG1 : ContDiffOn ℝ 1 G {0}ᶜ) (hGc : ∀ w, 2 < ‖w‖ → G w = 0)
    {c0 c1 s1 : ℝ} (hc0 : ∀ w, w ≠ 0 → |G w| ≤ c0)
    (hc1 : ∀ w, w ≠ 0 → ‖fderiv ℝ G w‖ ≤ c1 * ‖w‖ ^ (-s1)) (hs1 : 0 < s1) (hs1d : s1 < d)
    {z : Euc d} (hz : z ≠ 0) :
    HasFDerivAt (fun z' => ∫ v, newtonKernel d nu (z' - v) * G v)
      (∫ v, newtonKernel d nu (z - v) • fderiv ℝ G v) z := by
  have hd1 : 1 ≤ d := by omega
  haveI := r26t8a_nontrivial hd
  set K : Euc d → ℝ := newtonKernel d nu with hK
  have hKm : Measurable K := r26t8a_K_measurable nu
  have hKloc : LocallyIntegrable K (volume : Measure (Euc d)) :=
    r26t8a_N2_locInt fun r => r26t8a_K_integrableOn hd nu r
  have hae0 := r26t8a_ae_ne_zero hd
  obtain ⟨w0, hw0⟩ := exists_ne (0 : Euc d)
  have hc00 : 0 ≤ c0 := (abs_nonneg _).trans (hc0 w0 hw0)
  have hc10 : 0 ≤ c1 := by
    have h := hc1 w0 hw0
    have hp : 0 < ‖w0‖ ^ (-s1) := Real.rpow_pos_of_pos (norm_pos_iff.2 hw0) _
    by_contra hneg
    push Not at hneg
    nlinarith [norm_nonneg (fderiv ℝ G w0)]
  obtain ⟨B1, hB1⟩ : ∃ B1, ∀ x, ‖fderiv ℝ chi x‖ ≤ B1 :=
    (hchi.1.continuous_fderiv (by simp)).bounded_above_of_compact_support
      ((r26t8a_chi_hasCompactSupport hchi).fderiv (𝕜 := ℝ))
  have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  have hder0 : ∀ w, 2 < ‖w‖ → fderiv ℝ G w = 0 := fun w hw => by
    have : G =ᶠ[𝓝 w] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hw] with u hu using hGc u hu
    rw [this.fderiv_eq]; exact fderiv_const_apply 0
  have hmaj : ∀ z' : Euc d, z' ≠ 0 → Integrable (fun v => |K (z' - v)| *
      (closedBall (0 : Euc d) 2).indicator (fun v => ‖v‖ ^ (-s1)) v) := fun z' hz' =>
    r26t8a_p07_major hd nu hs1 hs1d hz'
  have hone : ∀ v : Euc d, v ≠ 0 → ‖v‖ ≤ 2 → 1 ≤ (2 : ℝ) ^ s1 * ‖v‖ ^ (-s1) := by
    intro v hv hv2
    have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
    have h2 : (2 : ℝ) ^ (-s1) ≤ ‖v‖ ^ (-s1) := Real.rpow_le_rpow_of_nonpos hvn hv2 (by linarith)
    calc (1 : ℝ) = (2 : ℝ) ^ s1 * 2 ^ (-s1) := by rw [← Real.rpow_add (by norm_num)]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
  have hind : ∀ v : Euc d, ‖v‖ ≤ 2 → (closedBall (0 : Euc d) 2).indicator (fun v => ‖v‖ ^ (-s1)) v = ‖v‖ ^ (-s1) :=
    fun v hv => Set.indicator_of_mem (by simpa [mem_closedBall_zero_iff] using hv) _
  set GN : ℕ → Euc d → ℝ := fun N w => (1 - chi ((2 : ℝ) ^ N • w)) * G w with hGNdef
  have hGN := fun N => r26t8a_Z2_GN_contDiff hchi hG1 hGc N
  have hGNd : ∀ N, ∀ w, 2 < ‖w‖ → fderiv ℝ (GN N) w = 0 := fun N w hw => by
    have : GN N =ᶠ[𝓝 w] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hw] with u hu
      simp [hGNdef, hGc u hu]
    rw [this.fderiv_eq]; exact fderiv_const_apply 0
  set r0 : ℝ := ‖z‖ / 4 with hr0
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hr0p : 0 < r0 := by positivity
  have hU : ∀ z' ∈ ball z r0, 3 * r0 < ‖z'‖ ∧ ‖z'‖ < 5 * r0 := by
    intro z' hz'
    rw [mem_ball] at hz'
    rw [dist_eq_norm] at hz'
    have h1 := norm_sub_norm_le z z'
    have h2 := norm_sub_norm_le z' z
    rw [norm_sub_rev] at h1
    constructor <;> linarith
  -- Step A: derivative of the truncated convolutions
  have hf : ∀ N : ℕ, ∀ z' : Euc d, HasFDerivAt (fun y => ∫ v, K (y - v) * GN N v)
      (∫ v, K (z' - v) • fderiv ℝ (GN N) v) z' := by
    intro N z'
    have h := (hGN N).2.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hKloc (hGN N).1 z'
    have e1 : (fun y => ∫ v, K (y - v) * GN N v) = (K ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] GN N) := by
      funext y
      rw [convolution_def]
      have := r26t8a_Z3_swap K (GN N) y
      simpa [smul_eq_mul] using this.symm
    have e2 : (∫ v, K (z' - v) • fderiv ℝ (GN N) v) =
        ((K ⋆[(ContinuousLinearMap.mul ℝ ℝ).precompR (Euc d), volume] fderiv ℝ (GN N)) z') := by
      rw [convolution_def, ← r26t8a_Z3_swap K (fderiv ℝ (GN N)) z']
      congr 1
    rw [e1, e2]; exact h
  -- Step B: pointwise convergence
  have hfg : ∀ z' ∈ ball z r0, Tendsto (fun N : ℕ => ∫ v, K (z' - v) * GN N v) atTop
      (𝓝 (∫ v, K (z' - v) * G v)) := by
    intro z' hz'
    have hz'0 : z' ≠ 0 := by
      intro h; have := (hU z' hz').1; rw [h, norm_zero] at this; linarith
    refine tendsto_integral_of_dominated_convergence
      (fun v => (c0 * 2 ^ s1) * (|K (z' - v)| *
        (closedBall (0 : Euc d) 2).indicator (fun v => ‖v‖ ^ (-s1)) v))
      (fun N => ?_) ((hmaj z' hz'0).const_mul _) (fun N => ?_) ?_
    · exact (hKm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
        (hGN N).1.continuous.aestronglyMeasurable
    · filter_upwards [hae0] with v hv
      by_cases hv2 : ‖v‖ ≤ 2
      · rw [hind v hv2, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        have h1 : |GN N v| ≤ c0 := by
          have hχ : |1 - chi ((2 : ℝ) ^ N • v)| ≤ 1 := by
            have := hchi.2.2.1 ((2 : ℝ) ^ N • v)
            rw [abs_le]; constructor <;> linarith [this.1, this.2]
          calc |GN N v| = |1 - chi ((2 : ℝ) ^ N • v)| * |G v| := by simp [hGNdef, abs_mul]
            _ ≤ 1 * c0 := mul_le_mul hχ (hc0 v hv) (abs_nonneg _) zero_le_one
            _ = c0 := one_mul _
        have h2 := hone v hv hv2
        calc |K (z' - v)| * |GN N v| ≤ |K (z' - v)| * c0 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
          _ ≤ |K (z' - v)| * (c0 * ((2 : ℝ) ^ s1 * ‖v‖ ^ (-s1))) :=
            mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _)
          _ = _ := by ring
      · have hv2' : 2 < ‖v‖ := not_le.1 hv2
        have : GN N v = 0 := by simp [hGNdef, hGc v hv2']
        rw [this]; simp only [mul_zero, norm_zero]
        have hi : 0 ≤ (closedBall (0 : Euc d) 2).indicator (fun v => ‖v‖ ^ (-s1)) v :=
          Set.indicator_nonneg (fun v _ => Real.rpow_nonneg (norm_nonneg v) _) v
        positivity
    · filter_upwards [hae0] with v hv
      have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
      have hev : ∀ᶠ N : ℕ in atTop, 2 < (2 : ℝ) ^ N * ‖v‖ :=
        ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const hvn).eventually_gt_atTop 2
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with N hN
      have h2 : 2 < ‖((2 : ℝ) ^ N) • v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]; exact hN
      simp [hGNdef, hchi.2.2.2.2 _ h2.le]
  -- Step C: uniform convergence of the derivatives
  obtain ⟨CK, hCK0, hCK⟩ := r26t8a_Z0_K_bdd (d := d) nu (ρ := r0) (R := 6 * r0) hr0p
  have hh0 : Integrable ((closedBall (0 : Euc d) 2).indicator (fun v : Euc d => ‖v‖ ^ (-s1))) := by
    refine (integrable_indicator_iff measurableSet_closedBall).2 ?_
    exact (r26t8a_integrableOn_ball_rpow hd1 hs1d 3).mono_set (closedBall_subset_ball (by norm_num))
  have htail := r26t8a_Z0_tail hd1 hh0
  have hvol := r26t8a_Z3_vol_tail hd
  set eps : ℕ → ℝ := fun N => CK * (c1 * (∫ w in ball (0 : Euc d) (3 * (1 / 2 : ℝ) ^ N),
      ‖(closedBall (0 : Euc d) 2).indicator (fun v : Euc d => ‖v‖ ^ (-s1)) w‖) +
      c0 * B1 * ((2 : ℝ) ^ N * (volume (ball (0 : Euc d) (3 * (1 / 2 : ℝ) ^ N))).toReal)) with heps
  have heps0 : Tendsto eps atTop (𝓝 0) := by
    have := ((htail.const_mul c1).add (hvol.const_mul (c0 * B1))).const_mul CK
    simpa [heps] using this
  have hind0 : ∀ v : Euc d, 0 ≤ (closedBall (0 : Euc d) 2).indicator (fun v => ‖v‖ ^ (-s1)) v := fun v =>
    Set.indicator_nonneg (fun v _ => Real.rpow_nonneg (norm_nonneg v) _) v
  have hdGm : AEStronglyMeasurable (fderiv ℝ G) (volume : Measure (Euc d)) := by
    have h1 := (hG1.continuousOn_fderiv_of_isOpen isOpen_compl_singleton le_rfl).aestronglyMeasurable
      (measurableSet_singleton (0 : Euc d)).compl (μ := (volume : Measure (Euc d)))
    have hae0' : ∀ᵐ x : Euc d ∂(volume : Measure (Euc d)), x ∈ ({0}ᶜ : Set (Euc d)) := hae0
    rwa [Measure.restrict_eq_self_of_ae_mem hae0'] at h1
  have hint_g : ∀ z' : Euc d, z' ≠ 0 → Integrable (fun v => K (z' - v) • fderiv ℝ G v) := by
    intro z' hz'
    refine Integrable.mono' ((hmaj z' hz').const_mul c1)
      ((hKm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.smul hdGm) ?_
    filter_upwards [hae0] with v hv
    rw [norm_smul, Real.norm_eq_abs]
    by_cases hv2 : ‖v‖ ≤ 2
    · rw [hind v hv2]
      calc |K (z' - v)| * ‖fderiv ℝ G v‖ ≤ |K (z' - v)| * (c1 * ‖v‖ ^ (-s1)) :=
            mul_le_mul_of_nonneg_left (hc1 v hv) (abs_nonneg _)
        _ = _ := by ring
    · rw [hder0 v (not_le.1 hv2), norm_zero, mul_zero]
      have := hind0 v
      positivity
  have hint_f : ∀ N : ℕ, ∀ z' : Euc d, z' ≠ 0 → Integrable (fun v => K (z' - v) • fderiv ℝ (GN N) v) := by
    intro N z' hz'
    refine Integrable.mono' ((hmaj z' hz').const_mul (2 * c1 + c0 * B1 * 2 ^ N * 2 ^ s1))
      ((hKm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.smul
        ((hGN N).1.continuous_fderiv (by simp)).aestronglyMeasurable) ?_
    filter_upwards [hae0] with v hv
    rw [norm_smul, Real.norm_eq_abs]
    by_cases hv2 : ‖v‖ ≤ 2
    · rw [hind v hv2]
      have hd1' := r26t8a_Z3a_diff_bound hchi hG1 hc0 hc1 hB1 N hv
      have hball : (ball (0 : Euc d) (3 * (1 / 2 : ℝ) ^ N)).indicator
          (fun v => c1 * ‖v‖ ^ (-s1) + c0 * B1 * 2 ^ N) v ≤ c1 * ‖v‖ ^ (-s1) + c0 * B1 * 2 ^ N := by
        by_cases hb : v ∈ ball (0 : Euc d) (3 * (1 / 2 : ℝ) ^ N)
        · rw [Set.indicator_of_mem hb]
        · rw [Set.indicator_of_notMem hb]
          have := Real.rpow_nonneg (norm_nonneg v) (-s1)
          positivity
      have h1 : ‖fderiv ℝ (GN N) v‖ ≤ ‖fderiv ℝ G v‖ + ‖fderiv ℝ (GN N) v - fderiv ℝ G v‖ := by
        have := norm_add_le (fderiv ℝ G v) (fderiv ℝ (GN N) v - fderiv ℝ G v)
        simpa using this
      have h2 := hone v hv hv2
      have hp : 0 ≤ ‖v‖ ^ (-s1) := Real.rpow_nonneg (norm_nonneg v) _
      have hc0B : 0 ≤ c0 * B1 * 2 ^ N := by positivity
      calc |K (z' - v)| * ‖fderiv ℝ (GN N) v‖
          ≤ |K (z' - v)| * (2 * c1 * ‖v‖ ^ (-s1) + c0 * B1 * 2 ^ N) :=
            mul_le_mul_of_nonneg_left (by nlinarith [hc1 v hv, hd1', hball]) (abs_nonneg _)
        _ ≤ |K (z' - v)| * ((2 * c1 + c0 * B1 * 2 ^ N * 2 ^ s1) * ‖v‖ ^ (-s1)) := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            nlinarith [mul_le_mul_of_nonneg_left h2 hc0B]
        _ = _ := by ring
    · rw [hGNd N v (not_le.1 hv2), norm_zero, mul_zero]
      have := hind0 v
      have hC : 0 ≤ 2 * c1 + c0 * B1 * 2 ^ N * 2 ^ s1 := by positivity
      positivity
  have hbound : ∀ N : ℕ, 3 * (1 / 2 : ℝ) ^ N ≤ r0 → 3 * (1 / 2 : ℝ) ^ N ≤ 2 → ∀ z' ∈ ball z r0,
      ‖(∫ v, K (z' - v) • fderiv ℝ (GN N) v) - ∫ v, K (z' - v) • fderiv ℝ G v‖ ≤ eps N := by
    intro N hN1 hN2 z' hz'
    have hz'0 : z' ≠ 0 := by
      intro h; have := (hU z' hz').1; rw [h, norm_zero] at this; linarith
    rw [← integral_sub (hint_f N z' hz'0) (hint_g z' hz'0)]
    simp only [← smul_sub]
    have hbI : IntegrableOn (fun v : Euc d => CK * (c1 * ‖v‖ ^ (-s1) + c0 * B1 * 2 ^ N))
        (ball (0 : Euc d) (3 * (1 / 2 : ℝ) ^ N)) :=
      (((r26t8a_integrableOn_ball_rpow hd1 hs1d _).const_mul c1).add (integrableOn_const measure_ball_lt_top.ne)).const_mul CK
    refine (norm_integral_le_of_norm_le (g := (ball (0 : Euc d) (3 * (1 / 2 : ℝ) ^ N)).indicator
      (fun v => CK * (c1 * ‖v‖ ^ (-s1) + c0 * B1 * 2 ^ N))) ((integrable_indicator_iff measurableSet_ball).2 hbI)
      ?_).trans (le_of_eq ?_)
    · filter_upwards [hae0] with v hv
      rw [norm_smul, Real.norm_eq_abs]
      have hd1' := r26t8a_Z3a_diff_bound hchi hG1 hc0 hc1 hB1 N hv
      by_cases hb : v ∈ ball (0 : Euc d) (3 * (1 / 2 : ℝ) ^ N)
      · rw [Set.indicator_of_mem hb]
        rw [Set.indicator_of_mem hb] at hd1'
        have hvr : ‖v‖ < r0 := by
          rw [mem_ball_zero_iff] at hb; linarith
        have hz1 := (hU z' hz').1
        have hz2 := (hU z' hz').2
        have hlo : r0 ≤ ‖z' - v‖ := by have := norm_sub_norm_le z' v; linarith
        have hhi : ‖z' - v‖ ≤ 6 * r0 := by have := norm_sub_le z' v; linarith
        have hk := hCK (z' - v) hlo hhi
        exact mul_le_mul hk hd1' (norm_nonneg _) hCK0
      · rw [Set.indicator_of_notMem hb]
        rw [Set.indicator_of_notMem hb] at hd1'
        have : ‖fderiv ℝ (GN N) v - fderiv ℝ G v‖ = 0 := le_antisymm hd1' (norm_nonneg _)
        rw [this, mul_zero]
    · rw [integral_indicator measurableSet_ball, heps]
      beta_reduce
      have hsub : ball (0 : Euc d) (3 * (1 / 2 : ℝ) ^ N) ⊆ closedBall (0 : Euc d) 2 := fun w hw => by
        rw [mem_ball_zero_iff] at hw; rw [mem_closedBall_zero_iff]; linarith
      have hc : ∫ w in ball (0 : Euc d) (3 * (1 / 2 : ℝ) ^ N), ‖(closedBall (0 : Euc d) 2).indicator
          (fun v : Euc d => ‖v‖ ^ (-s1)) w‖ = ∫ w in ball (0 : Euc d) (3 * (1 / 2 : ℝ) ^ N), ‖w‖ ^ (-s1) := by
        refine setIntegral_congr_fun measurableSet_ball fun w hw => ?_
        rw [Set.indicator_of_mem (hsub hw), Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg w) _)]
      rw [hc, integral_const_mul, integral_add ((r26t8a_integrableOn_ball_rpow hd1 hs1d _).const_mul c1)
        (integrableOn_const measure_ball_lt_top.ne), integral_const_mul, setIntegral_const]
      simp only [Measure.real, smul_eq_mul]
      ring
  have hunif : TendstoUniformlyOn (fun N (z' : Euc d) => ∫ v, K (z' - v) • fderiv ℝ (GN N) v)
      (fun z' => ∫ v, K (z' - v) • fderiv ℝ G v) atTop (ball z r0) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hev1 : ∀ᶠ N : ℕ in atTop, eps N < ε := heps0.eventually (gt_mem_nhds hε)
    have hsm : Tendsto (fun N : ℕ => 3 * (1 / 2 : ℝ) ^ N) atTop (𝓝 (3 * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul 3
    rw [mul_zero] at hsm
    have hev2 : ∀ᶠ N : ℕ in atTop, 3 * (1 / 2 : ℝ) ^ N < min r0 2 :=
      hsm.eventually (gt_mem_nhds (lt_min hr0p (by norm_num)))
    filter_upwards [hev1, hev2] with N h1 h2 z' hz'
    rw [dist_comm, dist_eq_norm]
    exact (hbound N (lt_min_iff.1 h2).1.le (lt_min_iff.1 h2).2.le z' hz').trans_lt h1
  exact hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_ball hunif.tendstoLocallyUniformlyOn
    (fun N z' _ => hf N z') hfg (mem_ball_self hr0p)

end HRS.MS.R26T8A
