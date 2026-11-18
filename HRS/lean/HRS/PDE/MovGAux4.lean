import HRS.PDE.MovGAux3

/-!
# MOVG Aux4: the one-body identity with the singular kernel

`movg_OBcore`: `∫ g(x-y) div F(y) dy = ∫ ⟨∇g(x-y), F(y)⟩ dy` for a `C¹` field `F` with `F(x) = 0`
(smooth truncations `g_M`, `M → ∞`, dominated convergence with `|∇g| |F| ≲ |z|^{-s}`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ} {s : ℝ}

/-- Reflection: `∂_j [y ↦ h(x - y)] = -(∂_j h)(x - y)`. -/
theorem movg_partialDeriv_reflect (j : Fin d) {h : Torus d → ℝ} (hh : Differentiable ℝ (Torus.lift h))
    (x y : Torus d) :
    Torus.partialDeriv j (fun y => h (x - y)) y = -Torus.partialDeriv j h (x - y) := by
  set y0 := Torus.rep y with hy0
  set x0 := Torus.rep x with hx0
  have hmk : ∀ w : Euc d, Torus.lift (fun y => h (x - y)) w = Torus.lift h (x0 - w) := by
    intro w
    simp only [Torus.lift, Function.comp, hx0, movg_mk_sub, Torus.mk_rep]
  have e : Torus.lift (fun y => h (x - y)) = fun w => Torus.lift h (x0 - w) := funext hmk
  have hd1 : HasFDerivAt (fun w : Euc d => Torus.lift h (x0 - w))
      (-(fderiv ℝ (Torus.lift h) (x0 - y0))) y0 := by
    have := (hh (x0 - y0)).hasFDerivAt.comp y0 ((hasFDerivAt_id y0).const_sub x0)
    exact this.congr_fderiv (by ext v; simp)
  unfold Torus.partialDeriv
  rw [← hy0, e, hd1.fderiv]
  simp only [neg_apply]
  congr 1
  rw [← movg_partialDeriv_mk]
  congr 1
  rw [movg_mk_sub, hx0, hy0, Torus.mk_rep, Torus.mk_rep]

theorem movg_isCk_reflect {h : Torus d → ℝ} {k : WithTop ℕ∞} (hh : Torus.IsCk k h) (x : Torus d) :
    Torus.IsCk k (fun y => h (x - y)) := by
  unfold Torus.IsCk
  have e : Torus.lift (fun y => h (x - y)) = fun w => Torus.lift h (Torus.rep x - w) := by
    funext w
    simp only [Torus.lift, Function.comp, movg_mk_sub, Torus.mk_rep]
  rw [e]
  exact hh.comp (contDiff_const.sub contDiff_id)

theorem movg_OB_level (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (M : ℝ) {x : Torus d}
    {F : Fin d → Torus d → ℝ} (hF : ∀ j, Torus.IsCk 1 (F j)) :
    ∫ y, b15c_gReg d s M (x - y) * ∑ j, Torus.partialDeriv j (F j) y =
      ∫ y, ∑ j, (movsx_lam d s M (x - y) * (periodicRieszGrad d s (x - y)).ofLp j) * F j y := by
  have hgc := b15c_gReg_isSmooth hd hs0 hsd M
  have hg1 : Torus.IsCk 1 (b15c_gReg d s M) := mova_isCk_one_of_two (mova_isCk_two_of_smooth hgc)
  have hdiff : Differentiable ℝ (Torus.lift (b15c_gReg d s M)) := hg1.differentiable (by norm_num)
  have hgcont : Continuous (b15c_gReg d s M) := mova_continuous_of_isCk hg1
  have hFc : ∀ j, Continuous (F j) := fun j => mova_continuous_of_isCk (hF j)
  have hdFc : ∀ j, Continuous (Torus.partialDeriv j (F j)) := fun j => mova_continuous_partialDeriv (hF j) j
  have hdgc : ∀ j, Continuous (Torus.partialDeriv j (b15c_gReg d s M)) := fun j =>
    mova_continuous_partialDeriv hg1 j
  have hsub : Continuous fun y : Torus d => x - y := continuous_const.sub continuous_id
  have hj : ∀ j, ∫ y, Torus.partialDeriv j (F j) y * b15c_gReg d s M (x - y) =
      ∫ y, F j y * Torus.partialDeriv j (b15c_gReg d s M) (x - y) := by
    intro j
    have h := mova_integral_ibp j (hF j) (movg_isCk_reflect hg1 x)
    rw [h, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [movg_partialDeriv_reflect j hdiff x y]
    ring
  calc ∫ y, b15c_gReg d s M (x - y) * ∑ j, Torus.partialDeriv j (F j) y
      = ∫ y, ∑ j, Torus.partialDeriv j (F j) y * b15c_gReg d s M (x - y) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ j, ∫ y, Torus.partialDeriv j (F j) y * b15c_gReg d s M (x - y) :=
        integral_finsetSum _ fun j _ => mova_int_cont ((hdFc j).mul (hgcont.comp hsub))
    _ = ∑ j, ∫ y, F j y * Torus.partialDeriv j (b15c_gReg d s M) (x - y) :=
        Finset.sum_congr rfl fun j _ => hj j
    _ = ∫ y, ∑ j, F j y * Torus.partialDeriv j (b15c_gReg d s M) (x - y) :=
        (integral_finsetSum _ fun j _ => mova_int_cont ((hFc j).mul ((hdgc j).comp hsub))).symm
    _ = _ := by
        refine integral_congr_ae ?_
        filter_upwards [movg_ae_ne hd x] with y hy
        have hz : x - y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mova_grad_apply, movsx_grad_gReg hd hs0 hsd M hz]
        simp only [PiLp.smul_apply, smul_eq_mul, movsx_lam]
        ring

theorem movg_tdistG_integrable (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    Integrable (fun z : Torus d => KernelGrad.tdist z 0 * ‖periodicRieszGrad d s z‖) := by
  obtain ⟨C, hG⟩ := KernelGradD1.goodKernel_periodicRieszGrad_of_one_le hd hs0 hsd
  have hdom : Integrable (fun z : Torus d => C * (‖z‖ ^ (-s) + (d : ℝ))) :=
    ((KernelGrad.integrable_norm_rpow_neg (by omega) hsd).add (integrable_const (d : ℝ))).const_mul C
  have hm : Measurable (fun z : Torus d => KernelGrad.tdist z 0 * ‖periodicRieszGrad d s z‖) :=
    (CoercAux.continuous_tdist_zero.measurable).mul (KernelGrad.measurable_periodicRieszGrad hsd).norm
  refine hdom.mono' hm.aestronglyMeasurable ?_
  filter_upwards [KernelGrad.torus_ae_ne' (by omega : 0 < d)] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (KernelGrad.tdist_nonneg _ _) (norm_nonneg _))]
  exact hG.norm_mul_tdist_le z hz

theorem movg_OBcore (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {x : Torus d}
    {F : Fin d → Torus d → ℝ} (hF : ∀ j, Torus.IsCk 1 (F j)) (hFx : ∀ j, F j x = 0) :
    ∫ y, periodicRiesz d s (x - y) * ∑ j, Torus.partialDeriv j (F j) y =
      ∫ y, ∑ j, (periodicRieszGrad d s (x - y)).ofLp j * F j y := by
  have hFc : ∀ j, Continuous (F j) := fun j => mova_continuous_of_isCk (hF j)
  have hdFc : ∀ j, Continuous (Torus.partialDeriv j (F j)) := fun j => mova_continuous_partialDeriv (hF j) j
  have hsub : Continuous fun y : Torus d => x - y := continuous_const.sub continuous_id
  obtain ⟨B, hB⟩ := periodicRiesz_ge_of_one_le (d := d) hd hs0 hsd
  set B' := |B| with hB'
  have hB'0 : 0 ≤ B' := abs_nonneg _
  have hBg : ∀ z : Torus d, -B' ≤ periodicRiesz d s z := fun z => by
    have := hB z; have := le_abs_self B; linarith
  obtain ⟨Cd, -, hCd⟩ := mova_bound_of_continuous
    (continuous_finsetSum Finset.univ fun j _ => hdFc j)
  have hgint : Integrable (fun z : Torus d => periodicRiesz d s z) := mova_integrable_periodicRiesz hd hs0 hsd
  -- the two limits
  have hL : Tendsto (fun n : ℕ => ∫ y, b15c_gReg d s (n : ℝ) (x - y) * ∑ j, Torus.partialDeriv j (F j) y) atTop
      (𝓝 (∫ y, periodicRiesz d s (x - y) * ∑ j, Torus.partialDeriv j (F j) y)) := by
    refine tendsto_integral_of_dominated_convergence (fun y => (|periodicRiesz d s (x - y)| + B') * Cd) ?_ ?_ ?_ ?_
    · intro n
      have hgc : Continuous (b15c_gReg d s (n : ℝ)) := b15c_isSmooth_continuous (b15c_gReg_isSmooth hd hs0 hsd _)
      exact ((hgc.comp hsub).mul (continuous_finsetSum _ fun j _ => hdFc j)).aestronglyMeasurable
    · exact (((hgint.comp_sub_left x).abs.add (integrable_const B')).mul_const Cd)
    · intro n
      filter_upwards [movg_ae_ne hd x] with y hy
      have hz : x - y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
      have h1 := b15c_gReg_le (s := s) (n : ℝ) hz
      have h2 := b15c_gReg_ge s hB'0 (Nat.cast_nonneg n) hBg (x - y)
      have h3 : |b15c_gReg d s (n : ℝ) (x - y)| ≤ |periodicRiesz d s (x - y)| + B' := by
        rw [abs_le]; constructor
        · have := abs_nonneg (periodicRiesz d s (x - y)); linarith
        · have := le_abs_self (periodicRiesz d s (x - y)); linarith
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul h3 (hCd y) (abs_nonneg _) (by positivity)
    · filter_upwards [movg_ae_ne hd x] with y hy
      have hz : x - y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
      have hev : ∀ᶠ n : ℕ in atTop, b15c_gReg d s (n : ℝ) (x - y) = periodicRiesz d s (x - y) :=
        (tendsto_natCast_atTop_atTop.eventually (b15c_gReg_eventuallyEq (d := d) s hz))
      exact (tendsto_const_nhds (x := periodicRiesz d s (x - y) * ∑ j, Torus.partialDeriv j (F j) y)).congr'
        (hev.mono fun n hn => by simp only [hn])
  have hR : Tendsto (fun n : ℕ => ∫ y, ∑ j, (movsx_lam d s (n : ℝ) (x - y) * (periodicRieszGrad d s (x - y)).ofLp j) * F j y)
      atTop (𝓝 (∫ y, ∑ j, (periodicRieszGrad d s (x - y)).ofLp j * F j y)) := by
    have hGm : Measurable (periodicRieszGrad d s : Torus d → Euc d) := KernelGrad.measurable_periodicRieszGrad hsd
    have hGj : ∀ j : Fin d, Measurable (fun z : Torus d => (periodicRieszGrad d s z).ofLp j) := fun j =>
      (measurable_pi_apply j).comp (WithLp.measurable_ofLp (p := 2) (X := Fin d → ℝ) |>.comp hGm)
    have hLip : ∀ j, ∀ y : Torus d, |F j y| ≤ Torus.cbNorm 1 (F j) * KernelGrad.tdist (x - y) 0 := by
      intro j y
      have h := PDE.R2Aux.isLipschitz_of_cbNorm (hF j) y x
      rw [hFx j, sub_zero] at h
      have e : KernelGrad.tdist y x = KernelGrad.tdist (x - y) 0 := by
        rw [KernelGrad.tdist_sub_comm, KernelGrad.tdist_eq_sub_zero]
      rw [← e]; exact h
    refine tendsto_integral_of_dominated_convergence
      (fun y => (∑ j, Torus.cbNorm 1 (F j)) * (KernelGrad.tdist (x - y) 0 * ‖periodicRieszGrad d s (x - y)‖)) ?_ ?_ ?_ ?_
    · intro n
      refine Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
      refine AEStronglyMeasurable.mul ?_ (hFc j).aestronglyMeasurable
      exact (((movsx_lam_measurable hd hs0 hsd _).comp hsub.measurable).mul
        ((hGj j).comp hsub.measurable)).aestronglyMeasurable
    · exact ((movg_tdistG_integrable hd hs0 hsd).comp_sub_left x).const_mul _
    · intro n
      refine Filter.Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (movsx_lam_nonneg s _ _)]
      have h1 : |(periodicRieszGrad d s (x - y)).ofLp j| ≤ ‖periodicRieszGrad d s (x - y)‖ := by
        simpa using PiLp.norm_apply_le (periodicRieszGrad d s (x - y)) j
      have h2 := movsx_lam_le_one s (n : ℝ) (x - y)
      have h3 := hLip j y
      have h4 := movsx_lam_nonneg s (n : ℝ) (x - y)
      calc movsx_lam d s (n : ℝ) (x - y) * |(periodicRieszGrad d s (x - y)).ofLp j| * |F j y|
          ≤ 1 * ‖periodicRieszGrad d s (x - y)‖ * (Torus.cbNorm 1 (F j) * KernelGrad.tdist (x - y) 0) := by
            gcongr
        _ = _ := by ring
    · refine Filter.Eventually.of_forall fun y => ?_
      refine tendsto_finsetSum _ fun j _ => ?_
      have hev : ∀ᶠ n : ℕ in atTop, movsx_lam d s (n : ℝ) (x - y) = 1 := by
        have : ∀ᶠ n : ℕ in atTop, periodicRiesz d s (x - y) ≤ (n : ℝ) :=
          tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
        filter_upwards [this] with n hn
        unfold movsx_lam
        rw [Real.smoothTransition.zero_of_nonpos (by linarith)]; ring
      exact (tendsto_const_nhds (x := (periodicRieszGrad d s (x - y)).ofLp j * F j y)).congr'
        (hev.mono fun n hn => by simp only [hn, one_mul])
  have heq : ∀ n : ℕ, ∫ y, b15c_gReg d s (n : ℝ) (x - y) * ∑ j, Torus.partialDeriv j (F j) y =
      ∫ y, ∑ j, (movsx_lam d s (n : ℝ) (x - y) * (periodicRieszGrad d s (x - y)).ofLp j) * F j y :=
    fun n => movg_OB_level hd hs0 hsd (n : ℝ) hF
  simp only [heq] at hL
  exact tendsto_nhds_unique hL hR

end HRS
