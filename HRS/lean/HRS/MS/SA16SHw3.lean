import HRS.MS.SA16SHw2

/-!
# S.A.16 (SA16S) Hw3: integrability and continuity of `σ ↦ ℓ_χ(Γ_{νσ} y)` and of the integral in `y`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Hw3
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16sw_f_bound {ν T : ℝ} (hν : 0 < ν) {χ : Euc d → ℝ} (hχ : IsCcInfty χ) (k : ℕ)
    (y : WmpSpace d k p) {σ : ℝ} (hσ : 0 < σ) (hσT : σ ≤ T) :
    |ν * sa16r_ell d (k + 1) p hχ (sa16r_GamT d k p ν σ y)| ≤
      ν * ‖sa16r_ell d (k + 1) p hχ‖ * (sa16r_Cgam d ν T * ‖y‖) * σ ^ (-(1 / 2 : ℝ)) := by
  have h1 := (sa16r_ell d (k + 1) p hχ).le_opNorm (sa16r_GamT d k p ν σ y)
  have h2 := (sa16r_GamT d k p ν σ).le_opNorm y
  have h3 := sa16r_GamT_bound (p := p) (d := d) hν k hσ hσT
  have hσp : 0 ≤ σ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hσ.le _
  have hn := norm_nonneg (sa16r_ell d (k + 1) p hχ)
  have hy := norm_nonneg y
  rw [abs_mul, abs_of_pos hν, ← Real.norm_eq_abs]
  have h4 : ‖sa16r_GamT d k p ν σ y‖ ≤ sa16r_Cgam d ν T * σ ^ (-(1 / 2 : ℝ)) * ‖y‖ :=
    h2.trans (mul_le_mul_of_nonneg_right h3 hy)
  have h5 : ‖sa16r_ell d (k + 1) p hχ (sa16r_GamT d k p ν σ y)‖ ≤
      ‖sa16r_ell d (k + 1) p hχ‖ * (sa16r_Cgam d ν T * σ ^ (-(1 / 2 : ℝ)) * ‖y‖) :=
    h1.trans (mul_le_mul_of_nonneg_left h4 hn)
  calc ν * ‖sa16r_ell d (k + 1) p hχ (sa16r_GamT d k p ν σ y)‖
      ≤ ν * (‖sa16r_ell d (k + 1) p hχ‖ * (sa16r_Cgam d ν T * σ ^ (-(1 / 2 : ℝ)) * ‖y‖)) :=
        mul_le_mul_of_nonneg_left h5 hν.le
    _ = _ := by ring

lemma sa16sw_f_cont {ν T : ℝ} (hν : 0 < ν) {χ : Euc d → ℝ} (hχ : IsCcInfty χ) (k : ℕ)
    (y : WmpSpace d k p) :
    ContinuousOn (fun σ : ℝ => ν * sa16r_ell d (k + 1) p hχ (sa16r_GamT d k p ν σ y)) (Ioc 0 T) :=
  continuousOn_const.mul ((sa16r_ell d (k + 1) p hχ).continuous.comp_continuousOn
    (sa16r_GamT_cont hν k y))

lemma sa16sw_f_ii {ν : ℝ} (hν : 0 < ν) {χ : Euc d → ℝ} (hχ : IsCcInfty χ) (k : ℕ)
    (y : WmpSpace d k p) {s : ℝ} (hs : 0 < s) :
    IntervalIntegrable (fun σ : ℝ => ν * sa16r_ell d (k + 1) p hχ (sa16r_GamT d k p ν σ y))
      volume 0 s := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs.le]
  have hb : IntegrableOn (fun σ : ℝ => ν * ‖sa16r_ell d (k + 1) p hχ‖ * (sa16r_Cgam d ν s * ‖y‖) *
      σ ^ (-(1 / 2 : ℝ))) (Ioc 0 s) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := s) (r := -(1 / 2 : ℝ))
      (by norm_num)).const_mul (ν * ‖sa16r_ell d (k + 1) p hχ‖ * (sa16r_Cgam d ν s * ‖y‖))
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hs.le] at this
  refine Integrable.mono' hb ((sa16sw_f_cont (T := s) hν hχ k y).aestronglyMeasurable measurableSet_Ioc) ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun σ hσ => ?_
  rw [Real.norm_eq_abs]
  exact sa16sw_f_bound hν hχ k y hσ.1 hσ.2

lemma sa16sw_int_cont {ν : ℝ} (hν : 0 < ν) {χ : Euc d → ℝ} (hχ : IsCcInfty χ) (k : ℕ)
    {s : ℝ} (hs : 0 < s) :
    Continuous (fun y : WmpSpace d k p => ∫ σ in (0 : ℝ)..s,
      ν * sa16r_ell d (k + 1) p hχ (sa16r_GamT d k p ν σ y)) := by
  rw [continuous_iff_continuousAt]
  intro y0
  have hbi : IntervalIntegrable (fun σ : ℝ => ν * ‖sa16r_ell d (k + 1) p hχ‖ *
      (sa16r_Cgam d ν s * (‖y0‖ + 1)) * σ ^ (-(1 / 2 : ℝ))) volume 0 s :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := s) (r := -(1 / 2 : ℝ))
      (by norm_num)).const_mul (ν * ‖sa16r_ell d (k + 1) p hχ‖ * (sa16r_Cgam d ν s * (‖y0‖ + 1)))
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun σ : ℝ =>
    ν * ‖sa16r_ell d (k + 1) p hχ‖ * (sa16r_Cgam d ν s * (‖y0‖ + 1)) * σ ^ (-(1 / 2 : ℝ))) ?_ ?_ hbi ?_
  · refine Eventually.of_forall fun y => ?_
    rw [Set.uIoc_of_le hs.le]
    exact (sa16sw_f_cont (T := s) hν hχ k y).aestronglyMeasurable measurableSet_Ioc
  · have hball : ∀ᶠ y in 𝓝 y0, ‖y‖ ≤ ‖y0‖ + 1 := by
      filter_upwards [Metric.ball_mem_nhds y0 (show (0 : ℝ) < 1 by norm_num)] with y hy
      have := norm_le_norm_add_norm_sub' y y0
      rw [mem_ball, dist_eq_norm] at hy
      linarith [norm_sub_rev y y0]
    filter_upwards [hball] with y hy
    refine Eventually.of_forall fun σ hσ => ?_
    rw [Set.uIoc_of_le hs.le] at hσ
    rw [Real.norm_eq_abs]
    refine (sa16sw_f_bound hν hχ k y hσ.1 hσ.2).trans ?_
    have hC := sa16r_Cgam_nonneg d hν s
    have hσp : 0 ≤ σ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hσ.1.le _
    have hn := norm_nonneg (sa16r_ell d (k + 1) p hχ)
    gcongr
  · refine Eventually.of_forall fun σ _ => ?_
    exact (continuous_const.mul ((sa16r_ell d (k + 1) p hχ).continuous.comp
      ((sa16r_GamT d k p ν σ).continuous))).continuousAt

end Hw3

end HRS.Whole.AppendixA.Phase2SA16R
