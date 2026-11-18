import HRS.MS.SharpInsAux2

/-!
# HRS.MS.SharpInsAux3 -- S7.6 `sharp_insertion_radius`: prefactor replacement and diagonal evaluation

Packet S76, namespace `HRS.MS.S76`, helper prefix `s76_`.  No frozen file is edited.

* `s76_pow1`, `s76_pow2`: `λ r^{d-s} = λ^p L^{d-s}` and `λ² r^{d-2s} = λ^p L^{d-2s}` for `r = λ^{1/s} L`;
* `s76_lemmaB`: if the first marginal has density `w·A` with `|A - 1| ≤ ε` then
  `|E f(Y_0) - ∫ f w dμ| ≤ ε ∫ f w dμ` (`f, w ≥ 0`);
* `s76_kk_tail_le`: `∫_{|u| ≥ L} k_s ≤ C L^{d-2s}`;
* `s76_lintegral_smul`: the dilation formula for the Lebesgue `lintegral`;
* `s76_diag_lintegral`: `∫_0^1 (1-t) ∫ ψ² e^{-tλ g} dμ dt = λ^p ∫_{|u|<L} k_s(u) ρ(x - λ^{1/s} u) du`
  (Tonelli, Taylor formula `Q34.integral_taylor`, change of variables `y = x - λ^{1/s} u`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.S76

open HRS.Whole (rieszKernel EucConfig)

variable {d : ℕ} {s : ℝ}

/-! ### Powers -/

theorem s76_pow1 (hs0 : 0 < s) {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    lam * (lam ^ (1 / s) * L) ^ ((d : ℝ) - s) = lam ^ ((d : ℝ) / s) * L ^ ((d : ℝ) - s) := by
  rw [Real.mul_rpow (Real.rpow_nonneg hlam.le _) hL.le, ← Real.rpow_mul hlam.le]
  have : (d : ℝ) / s = 1 + 1 / s * ((d : ℝ) - s) := by field_simp; ring
  rw [this, Real.rpow_add hlam, Real.rpow_one]
  ring

theorem s76_pow2 (hs0 : 0 < s) {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    lam ^ 2 * (lam ^ (1 / s) * L) ^ ((d : ℝ) - 2 * s) =
      lam ^ ((d : ℝ) / s) * L ^ ((d : ℝ) - 2 * s) := by
  rw [Real.mul_rpow (Real.rpow_nonneg hlam.le _) hL.le, ← Real.rpow_mul hlam.le]
  have : (d : ℝ) / s = 2 + 1 / s * ((d : ℝ) - 2 * s) := by field_simp; ring
  rw [this, Real.rpow_add hlam, Real.rpow_two]
  ring

/-! ### Replacing the prefactor -/

theorem s76_lemmaB {n : ℕ} (hn : 0 < n) {Q : Measure (EucConfig d n)} {μ : Measure (Euc d)}
    {w : Euc d → ℝ} (hwm : Measurable w) (hw0 : ∀ y, 0 ≤ w y)
    {A : Euc d → ℝ} (hAm : Measurable A)
    (hfm : HRS.Whole.firstMarginal Q = μ.withDensity (fun y => ENNReal.ofReal (w y * A y)))
    (hA0 : ∀ᵐ y ∂μ, 0 ≤ A y) {ε : ℝ} (hε : ∀ᵐ y ∂μ, |A y - 1| ≤ ε)
    {f : Euc d → ℝ} (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    (hint : Integrable (fun y => f y * w y) μ) :
    |∫ Y, f (Y ⟨0, hn⟩) ∂Q - ∫ y, f y * w y ∂μ| ≤ ε * ∫ y, f y * w y ∂μ := by
  have hfmQ : HRS.Whole.firstMarginal Q = Q.map (fun Y : EucConfig d n => Y ⟨0, hn⟩) := by
    unfold HRS.Whole.firstMarginal; rw [dif_pos hn]
  have hm0 : Measurable (fun Y : EucConfig d n => Y ⟨0, hn⟩) := measurable_pi_apply _
  have e1 : ∫ Y, f (Y ⟨0, hn⟩) ∂Q = ∫ y, f y ∂(HRS.Whole.firstMarginal Q) := by
    rw [hfmQ]
    exact (integral_map hm0.aemeasurable hf.aestronglyMeasurable).symm
  rw [e1, hfm, integral_withDensity_eq_integral_toReal_smul (f := fun y => ENNReal.ofReal (w y * A y))
    (ENNReal.measurable_ofReal.comp (hwm.mul hAm))
    (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top) f]
  have e2 : ∀ᵐ y ∂μ, (ENNReal.ofReal (w y * A y)).toReal • f y =
      f y * w y + f y * w y * (A y - 1) := by
    filter_upwards [hA0] with y hy
    rw [ENNReal.toReal_ofReal (mul_nonneg (hw0 y) hy), smul_eq_mul]; ring
  rw [integral_congr_ae e2]
  have hfw : ∀ y, 0 ≤ f y * w y := fun y => mul_nonneg (hf0 y) (hw0 y)
  have hbd : ∀ᵐ y ∂μ, ‖f y * w y * (A y - 1)‖ ≤ ε * (f y * w y) := by
    filter_upwards [hε] with y hy
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hfw y)]
    calc f y * w y * |A y - 1| ≤ f y * w y * ε := mul_le_mul_of_nonneg_left hy (hfw y)
      _ = ε * (f y * w y) := by ring
  have hint2 : Integrable (fun y => f y * w y * (A y - 1)) μ :=
    Integrable.mono' (hint.const_mul ε)
      ((hf.mul hwm).mul (hAm.sub measurable_const)).aestronglyMeasurable hbd
  rw [integral_add hint hint2]
  have h3 : |∫ y, f y * w y * (A y - 1) ∂μ| ≤ ε * ∫ y, f y * w y ∂μ := by
    calc |∫ y, f y * w y * (A y - 1) ∂μ| = ‖∫ y, f y * w y * (A y - 1) ∂μ‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∫ y, ‖f y * w y * (A y - 1)‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ y, ε * (f y * w y) ∂μ := integral_mono_ae hint2.norm (hint.const_mul ε) hbd
      _ = ε * ∫ y, f y * w y ∂μ := integral_const_mul _ _
  have : ∫ y, f y * w y ∂μ + ∫ y, f y * w y * (A y - 1) ∂μ - ∫ y, f y * w y ∂μ =
      ∫ y, f y * w y * (A y - 1) ∂μ := by ring
  rw [this]
  exact h3

/-! ### The tail of the compensated kernel (closed complement) -/

theorem s76_kk_tail_le (hd : 1 ≤ d) (hs0 : 0 < s) (hds : (d : ℝ) < 2 * s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 < L →
      ∫ u in {u : Euc d | L ≤ ‖u‖}, HRS.Whole.Q34.kk (‖u‖ ^ (-s)) ≤ C * L ^ ((d : ℝ) - 2 * s) := by
  have hsA := HRS.Whole.Q34.sphereArea_nonneg hd
  have h2s : 0 < 2 * s - (d : ℝ) := by linarith
  refine ⟨HRS.sphereArea d / (2 * (2 * s - d)), by positivity, fun L hL0 => ?_⟩
  have hm := HRS.Whole.Q34.measurable_kk_norm_rpow (d := d) s
  have hnn : ∀ u : Euc d, 0 ≤ HRS.Whole.Q34.kk (‖u‖ ^ (-s)) := fun u =>
    HRS.Whole.Q34.kk_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
  have hset : MeasurableSet {u : Euc d | L ≤ ‖u‖} := measurableSet_le measurable_const measurable_norm
  have hLp : 0 ≤ L ^ ((d : ℝ) - 2 * s) := Real.rpow_nonneg hL0.le _
  have hC : 0 ≤ HRS.sphereArea d / (2 * (2 * s - d)) * L ^ ((d : ℝ) - 2 * s) := by positivity
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun u => hnn u)) hm.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal hC ?_
  have hpt : ∀ u : Euc d, ENNReal.ofReal (HRS.Whole.Q34.kk (‖u‖ ^ (-s))) ≤
      ENNReal.ofReal (2⁻¹) * ENNReal.ofReal (‖u‖ ^ (-(2 * s))) := by
    intro u
    rw [← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := HRS.Whole.Q34.kk_le_half_sq (Real.rpow_nonneg (norm_nonneg u) (-s))
    rw [s76_sq_rpow] at h1
    linarith
  calc ∫⁻ u in {u : Euc d | L ≤ ‖u‖}, ENNReal.ofReal (HRS.Whole.Q34.kk (‖u‖ ^ (-s)))
      ≤ ∫⁻ u in {u : Euc d | L ≤ ‖u‖}, ENNReal.ofReal (2⁻¹) *
          ENNReal.ofReal (‖u‖ ^ (-(2 * s))) := lintegral_mono hpt
    _ = ENNReal.ofReal (2⁻¹) * ∫⁻ u in {u : Euc d | L ≤ ‖u‖}, ENNReal.ofReal (‖u‖ ^ (-(2 * s))) :=
        lintegral_const_mul _ ((measurable_norm.pow_const _).ennreal_ofReal)
    _ = ENNReal.ofReal (2⁻¹) * ENNReal.ofReal (HRS.sphereArea d *
          (L ^ ((d : ℝ) - 2 * s) / (2 * s - (d : ℝ)))) := by
        rw [HRS.Whole.Q34.lintegral_compl_rpow hd hL0 hds]
    _ = ENNReal.ofReal (HRS.sphereArea d / (2 * (2 * s - d)) * L ^ ((d : ℝ) - 2 * s)) := by
        rw [← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        field_simp

/-! ### Dilations -/

theorem s76_lintegral_smul {c : ℝ} (hc : 0 < c) (F : Euc d → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, F z = ENNReal.ofReal (c ^ d) * ∫⁻ u, F (c • u) := by
  have h := Measure.map_addHaar_smul (volume : Measure (Euc d)) hc.ne'
  have hfr : Module.finrank ℝ (Euc d) = d := by simp
  rw [hfr] at h
  have h2 : ∫⁻ u, F (c • u) = ∫⁻ z, F z ∂(Measure.map (c • ·) (volume : Measure (Euc d))) :=
    (lintegral_map hF (measurable_const_smul c)).symm
  rw [h2, h, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have : c ^ d * |(c ^ d)⁻¹| = 1 := by
    rw [abs_of_pos (by positivity)]; field_simp
  rw [this]; simp

theorem s76_scale {lam : ℝ} (hs0 : 0 < s) (hlam : 0 < lam) (u : Euc d) :
    lam * (lam ^ (1 / s) * ‖u‖) ^ (-s) = ‖u‖ ^ (-s) := by
  rw [Real.mul_rpow (Real.rpow_nonneg hlam.le _) (norm_nonneg _), ← Real.rpow_mul hlam.le]
  have : 1 / s * -s = -1 := by field_simp
  rw [this, Real.rpow_neg_one]
  field_simp

/-! ### The diagonal evaluation -/

theorem s76_diag_lintegral (hd : 1 ≤ d) (hs0 : 0 < s) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) (x : Euc d) :
    ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (1 - t) *
        ∫⁻ y, ENNReal.ofReal (s76_psi d s lam (lam ^ (1 / s) * L) x y ^ 2 *
          Real.exp (-(t * lam) * rieszKernel d s (x - y))) ∂(HRS.Whole.withDensityReal ρ) =
      ENNReal.ofReal (lam ^ ((d : ℝ) / s)) *
        ∫⁻ u in ball (0 : Euc d) L, ENNReal.ofReal (ρ (x - (lam ^ (1 / s)) • u)) *
          ENNReal.ofReal (HRS.Whole.Q34.kk (‖u‖ ^ (-s))) := by
  set μ := HRS.Whole.withDensityReal ρ with hμ
  haveI : SFinite μ := by rw [hμ]; unfold HRS.Whole.withDensityReal; infer_instance
  set c : ℝ := lam ^ (1 / s) with hcdef
  have hc : 0 < c := Real.rpow_pos_of_pos hlam _
  set r : ℝ := c * L with hrdef
  have hr : 0 < r := mul_pos hc hL
  have hpsim := s76_psi_meas (d := d) (s := s) lam r x
  have hg : Measurable (fun y : Euc d => rieszKernel d s (x - y)) :=
    (HRS.Whole.Q34.measurable_rieszKernel hs0.ne').comp (measurable_const.sub measurable_id)
  have hrk : ∀ y : Euc d, rieszKernel d s (x - y) = ‖x - y‖ ^ (-s) :=
    fun y => HRS.Whole.Q34.rieszKernel_eq hs0.ne' _
  set F : ℝ → Euc d → ℝ≥0∞ := fun t y => ENNReal.ofReal (1 - t) *
    ENNReal.ofReal (s76_psi d s lam r x y ^ 2 * Real.exp (-(t * lam) * rieszKernel d s (x - y)))
    with hF
  have hFm : Measurable (Function.uncurry F) := by
    refine (ENNReal.measurable_ofReal.comp (measurable_const.sub measurable_fst)).mul
      (ENNReal.measurable_ofReal.comp ?_)
    exact ((hpsim.comp measurable_snd).pow_const 2).mul
      (Real.measurable_exp.comp (((measurable_fst.mul measurable_const).neg).mul
        (hg.comp measurable_snd)))
  have step1 : ∀ t : ℝ, ENNReal.ofReal (1 - t) * ∫⁻ y, ENNReal.ofReal (s76_psi d s lam r x y ^ 2 *
      Real.exp (-(t * lam) * rieszKernel d s (x - y))) ∂μ = ∫⁻ y, F t y ∂μ :=
    fun t => (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
  simp_rw [step1]
  rw [lintegral_lintegral_swap hFm.aemeasurable]
  -- the inner `t`-integral
  set H : Euc d → ℝ≥0∞ := (ball (0 : Euc d) r).indicator
    (fun z => ENNReal.ofReal (HRS.Whole.Q34.kk (lam * ‖z‖ ^ (-s)))) with hH
  have inner : ∀ y : Euc d, ∫⁻ t in Ioc (0 : ℝ) 1, F t y = H (x - y) := by
    intro y
    by_cases hb : ‖x - y‖ < r
    · have hHy : H (x - y) = ENNReal.ofReal (HRS.Whole.Q34.kk (lam * ‖x - y‖ ^ (-s))) := by
        simp [hH, hb]
      rw [hHy]
      rcases (norm_nonneg (x - y)).eq_or_lt with h0 | hpos
      · -- `x = y`
        have hz : ‖x - y‖ ^ (-s) = 0 := by rw [← h0]; exact Real.zero_rpow (by linarith)
        have hpsi : s76_psi d s lam r x y = 0 := by simp [s76_psi, hb, hz]
        simp only [hF, hpsi, hz, mul_zero]
        simp [HRS.Whole.Q34.kk]
      · set a : ℝ := lam * ‖x - y‖ ^ (-s) with hadef
        have ha : 0 < a := mul_pos hlam (Real.rpow_pos_of_pos hpos _)
        have hpsi : s76_psi d s lam r x y = a := by simp [s76_psi, hb, hadef]
        have hint : ∀ t ∈ Ioc (0 : ℝ) 1, F t y =
            ENNReal.ofReal ((1 - t) * (a ^ 2 * Real.exp (-t * a))) := by
          intro t ht
          simp only [hF]
          rw [← ENNReal.ofReal_mul (by linarith [ht.2]), hpsi, hrk]
          congr 3
          rw [hadef]; ring
        rw [setLIntegral_congr_fun measurableSet_Ioc hint]
        have hcont : Continuous (fun t : ℝ => (1 - t) * (a ^ 2 * Real.exp (-t * a))) := by fun_prop
        rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Ioc)
          (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht =>
            mul_nonneg (by linarith [ht.2]) (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le))]
        congr 1
        have htay := HRS.Whole.Q34.integral_taylor ha
        rw [integral_Icc_eq_integral_Ioc] at htay
        calc ∫ t in Ioc (0 : ℝ) 1, (1 - t) * (a ^ 2 * Real.exp (-t * a))
            = a ^ 2 * ∫ t in Ioc (0 : ℝ) 1, (1 - t) * Real.exp (-t * a) := by
              rw [← integral_const_mul]
              refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
              ring
          _ = HRS.Whole.Q34.kk a := by rw [htay]; field_simp
    · have hHy : H (x - y) = 0 := by simp [hH, hb]
      rw [hHy]
      have hpsi : s76_psi d s lam r x y = 0 := by simp [s76_psi, hb]
      simp [hF, hpsi]
  simp_rw [inner]
  -- now `∫⁻ y, H (x - y) ∂μ`
  have hHm : Measurable H :=
    (ENNReal.measurable_ofReal.comp (HRS.Whole.Q34.measurable_kk.comp
      (measurable_const.mul (measurable_norm.pow_const _)))).indicator measurableSet_ball
  have hHm' : Measurable (fun y : Euc d => H (x - y)) :=
    hHm.comp (measurable_const.sub measurable_id)
  rw [hμ, HRS.Whole.Q34.lintegral_nu hρ _ hHm']
  set f : Euc d → ℝ≥0∞ := fun z => ENNReal.ofReal (ρ (x - z)) * H z with hf
  have hfm : Measurable f :=
    (ENNReal.measurable_ofReal.comp (hρ.measurable.comp (measurable_const.sub measurable_id))).mul hHm
  have e1 : ∫⁻ y, ENNReal.ofReal (ρ y) * H (x - y) = ∫⁻ y, f (x - y) := by
    refine lintegral_congr fun y => ?_
    simp [hf]
  rw [e1, lintegral_sub_left_eq_self f x, s76_lintegral_smul hc f hfm]
  have e2 : ∀ u : Euc d, f (c • u) =
      (ball (0 : Euc d) L).indicator (fun u => ENNReal.ofReal (ρ (x - c • u)) *
        ENNReal.ofReal (HRS.Whole.Q34.kk (‖u‖ ^ (-s)))) u := by
    intro u
    by_cases hu : ‖u‖ < L
    · have hu' : ‖c • u‖ < r := by
        rw [norm_smul, Real.norm_of_nonneg hc.le, hrdef]; exact mul_lt_mul_of_pos_left hu hc
      have hsc : lam * ‖c • u‖ ^ (-s) = ‖u‖ ^ (-s) := by
        rw [norm_smul, Real.norm_of_nonneg hc.le]; exact s76_scale hs0 hlam u
      simp [hf, hH, hu', hu, hsc]
    · have hu' : ¬ ‖c • u‖ < r := by
        rw [norm_smul, Real.norm_of_nonneg hc.le, hrdef]
        intro h; exact hu ((mul_lt_mul_iff_right₀ hc).1 h)
      simp [hf, hH, hu', hu]
  simp_rw [e2]
  rw [lintegral_indicator measurableSet_ball]
  have e3 : c ^ d = lam ^ ((d : ℝ) / s) := by
    rw [hcdef, ← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
    congr 1; field_simp
  rw [e3]

end HRS.MS.S76
