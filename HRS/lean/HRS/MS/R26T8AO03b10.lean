import HRS.MS.R26T8AO03b9

/-!
# S8.2 T8A O03b (part 10): `aSource f` is continuous for a test function `f`
The commutator source is rewritten, by the substitution `y = x - z`, as an integral over `z` of an integrand that is
continuous in `x`; it is dominated near any `x0` by a truncated pole plus a gaussian.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U HRS.MS.S82W HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 12800000 in
theorem r26t8a_o03b_aSource_cont (hd : 2 ≤ d) {a beta : ℝ} (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) {f : Euc d → ℝ} {A : ℝ}
    (hTB : TestBound (testOrder d) A f) :
    Continuous (aSource (HRS.Whole.withDensityReal rho) f) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  have hsd : criticalS d < d := by unfold criticalS; linarith
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  obtain ⟨hdiff, C, c, hC, hc, hb⟩ := HRS.MS.Wad.s84_thermal_gaussReg hd ha hbeta hrho
  have hρs : ContDiff ℝ ∞ rho := (HRS.MS.Mov0.mv0_hgauss hd hs0.le hsd ha hbeta hrho).1
  have hρg : ∀ y, rho y ≤ C * Real.exp (-c * ‖y‖ ^ 2) := fun y => (le_abs_self _).trans (hb y).1
  obtain ⟨hf, hj⟩ := hTB
  set Rn : ℝ := ‖r26t8a_Rz d‖ with hRn
  have hRn0 : 0 ≤ Rn := norm_nonneg (r26t8a_Rz d)
  have hA : 0 ≤ A := (norm_nonneg _).trans (hj 1 le_rfl (by unfold testOrder; omega) 0)
  have hf2 : ∀ w, ‖iteratedFDeriv ℝ 2 f w‖ ≤ A := fun w => hj 2 (by norm_num) (by unfold testOrder; omega) w
  have hgb : ∀ w, ‖gradient f w‖ ≤ Rn * A := fun w => by
    rw [r26t8a_gradient_eq_Rz]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    have := hj 1 le_rfl (by unfold testOrder; omega) w
    rw [norm_iteratedFDeriv_one] at this
    exact mul_le_mul_of_nonneg_left this hRn0
  have hgc : Continuous (gradient f) := by
    rw [r26t8a_gradient_eq_Rz]
    exact (r26t8a_Rz d).continuous.comp (hf.continuous_fderiv (by simp))
  have hκm : Measurable (rieszKernelGrad d (criticalS d)) := by
    unfold rieszKernelGrad gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp
      (measurable_fderiv ℝ (rieszKernel d (criticalS d)))
  have hgm : Measurable (gradient f) := hgc.measurable
  set μ := HRS.Whole.withDensityReal rho with hμ
  set s := criticalS d with hsdef
  let F : Euc d → Euc d → ℝ := fun x z =>
    rho (x - z) * inner ℝ (gradient f x - gradient f (x - z)) (rieszKernelGrad d s z)
  have hrep : ∀ x, aSource μ f x = (1 / 2) * ∫ z, F x z := by
    intro x
    unfold aSource
    congr 1
    rw [r26t8a_f25_wd_integral hprob]
    have := integral_sub_left_eq_self (fun y => rho y * hSource f x y) (volume : Measure (Euc d)) x
    rw [← this]
    congr 1
    funext z
    simp only [F, hSource, commutatorKernel, sub_sub_cancel]
    rfl
  rw [continuous_iff_continuousAt]
  intro x0
  have hfun : aSource μ f = fun x => (1 / 2) * ∫ z, F x z := funext hrep
  rw [hfun]
  refine ContinuousAt.const_mul ?_ _
  set R : ℝ := ‖x0‖ + 1 with hR
  set K1 : ℝ := C * Rn * A * s with hK1
  set K2 : ℝ := 2 * Rn * A * s * C * Real.exp (c * R ^ 2) with hK2
  have hK10 : 0 ≤ K1 := by positivity
  have hK20 : 0 ≤ K2 := by positivity
  set ind : Euc d → ℝ := (Metric.ball (0 : Euc d) 1).indicator (fun z : Euc d => ‖z‖ ^ (-s)) with hind
  have hind0 : ∀ z, 0 ≤ ind z := fun z =>
    indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg _) _) z
  have hbi : Integrable (fun z : Euc d => K1 * ind z + K2 * Real.exp (-(c / 2) * ‖z‖ ^ 2)) :=
    ((r26t8a_o03b_ind_int hd hsd).const_mul K1).add ((r26t8a_o03b_gauss_int (half_pos hc)).const_mul K2)
  refine continuousAt_of_dominated (bound := fun z : Euc d => K1 * ind z + K2 * Real.exp (-(c / 2) * ‖z‖ ^ 2))
    (Filter.Eventually.of_forall fun x => ?_) ?_ hbi (Filter.Eventually.of_forall fun z => ?_)
  · refine Measurable.aestronglyMeasurable ?_
    have h1 : Measurable (fun z : Euc d => gradient f x - gradient f (x - z)) :=
      measurable_const.sub (hgm.comp (measurable_const.sub measurable_id))
    exact (hρs.continuous.measurable.comp (measurable_const.sub measurable_id)).mul (h1.inner hκm)
  · filter_upwards [Metric.ball_mem_nhds x0 one_pos] with x hx
    have hxR : ‖x‖ ≤ R := by
      have := norm_le_norm_add_norm_sub' x x0
      rw [hR]
      have h2 : ‖x - x0‖ < 1 := by simpa [dist_eq_norm] using hx
      linarith
    have hae0 : ∀ᵐ z : Euc d, z ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton 0)
    filter_upwards [hae0] with z hz
    have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hkn : ‖rieszKernelGrad d s z‖ = s * ‖z‖ ^ (-s - 1) := r26t8a_norm_rieszGrad hs0 hz
    have hρ0 : 0 ≤ rho (x - z) := hprob.nonneg _
    have hP : 0 ≤ ‖z‖ ^ (-s - 1) := Real.rpow_nonneg hzn.le _
    have hex0 : 0 ≤ K2 * Real.exp (-(c / 2) * ‖z‖ ^ 2) := by positivity
    have hFn : ‖F x z‖ ≤ rho (x - z) * (‖gradient f x - gradient f (x - z)‖ * (s * ‖z‖ ^ (-s - 1))) := by
      simp only [F]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hρ0]
      refine mul_le_mul_of_nonneg_left ?_ hρ0
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [hkn]
    by_cases hnear : z ∈ Metric.ball (0 : Euc d) 1
    · have hzn1 : ‖z‖ < 1 := by simpa using hnear
      have hL := r26t8a_o02_grad_lip hf hf2 x (x - z)
      rw [sub_sub_cancel] at hL
      have hρC : rho (x - z) ≤ C := by
        refine (hρg _).trans ?_
        have : Real.exp (-c * ‖x - z‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x - z‖])
        nlinarith
      have e : ‖z‖ * ‖z‖ ^ (-s - 1) = ‖z‖ ^ (-s) := by
        rw [← Real.rpow_one_add' hzn.le (by linarith)]; congr 1; ring
      have hs0' : 0 ≤ s := hs0.le
      have h1 : ‖F x z‖ ≤ C * (Rn * A * ‖z‖ * (s * ‖z‖ ^ (-s - 1))) := by
        refine hFn.trans ?_
        refine mul_le_mul hρC (mul_le_mul_of_nonneg_right hL (by positivity)) (by positivity) hC
      have h2 : C * (Rn * A * ‖z‖ * (s * ‖z‖ ^ (-s - 1))) = K1 * ‖z‖ ^ (-s) := by
        rw [← e, hK1]; ring
      have h3 : ind z = ‖z‖ ^ (-s) := by simp only [hind]; rw [Set.indicator_of_mem hnear]
      rw [h2] at h1
      rw [← h3] at h1
      linarith
    · have hzn1 : 1 ≤ ‖z‖ := by
        by_contra h; exact hnear (by simpa using not_le.1 h)
      have hi0 : ind z = 0 := by simp only [hind]; rw [Set.indicator_of_notMem hnear]
      have hgd : ‖gradient f x - gradient f (x - z)‖ ≤ 2 * (Rn * A) :=
        (norm_sub_le _ _).trans (by linarith [hgb x, hgb (x - z)])
      have hpz : ‖z‖ ^ (-s - 1) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hzn1 (by linarith)
      have hs0' : 0 ≤ s := hs0.le
      have h1 : ‖F x z‖ ≤ rho (x - z) * (2 * (Rn * A) * s) := by
        refine hFn.trans (mul_le_mul_of_nonneg_left ?_ hρ0)
        calc ‖gradient f x - gradient f (x - z)‖ * (s * ‖z‖ ^ (-s - 1))
            ≤ (2 * (Rn * A)) * (s * 1) :=
              mul_le_mul hgd (mul_le_mul_of_nonneg_left hpz hs0') (by positivity) (by positivity)
          _ = 2 * (Rn * A) * s := by ring
      have hexp : Real.exp (-c * ‖x - z‖ ^ 2) ≤ Real.exp (c * R ^ 2) * Real.exp (-(c / 2) * ‖z‖ ^ 2) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have hz2 : ‖z‖ ≤ ‖x‖ + ‖x - z‖ := by
          have := norm_sub_le x (x - z)
          simpa using this
        have hxR0 : 0 ≤ ‖x‖ := norm_nonneg _
        have hz3 : ‖z‖ ^ 2 ≤ (‖x‖ + ‖x - z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hz2 2
        have hx2 : ‖x‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hxR0 hxR 2
        have hpos : 0 ≤ R ^ 2 + ‖x - z‖ ^ 2 - ‖z‖ ^ 2 / 2 := by
          nlinarith [sq_nonneg (‖x‖ - ‖x - z‖)]
        nlinarith [mul_nonneg hc.le hpos]
      have h2 : rho (x - z) * (2 * (Rn * A) * s) ≤ K2 * Real.exp (-(c / 2) * ‖z‖ ^ 2) := by
        calc rho (x - z) * (2 * (Rn * A) * s) ≤ (C * Real.exp (-c * ‖x - z‖ ^ 2)) * (2 * (Rn * A) * s) :=
              mul_le_mul_of_nonneg_right (hρg _) (by positivity)
          _ ≤ (C * (Real.exp (c * R ^ 2) * Real.exp (-(c / 2) * ‖z‖ ^ 2))) * (2 * (Rn * A) * s) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hC) (by positivity)
          _ = K2 * Real.exp (-(c / 2) * ‖z‖ ^ 2) := by rw [hK2]; ring
      rw [hi0, mul_zero, zero_add]
      exact h1.trans h2
  · have hcz : Continuous fun x : Euc d => F x z := by
      simp only [F]
      exact (hρs.continuous.comp (continuous_id.sub continuous_const)).mul
        ((hgc.sub (hgc.comp (continuous_id.sub continuous_const))).inner continuous_const)
    exact hcz.continuousAt

end HRS.MS.R26T8A
