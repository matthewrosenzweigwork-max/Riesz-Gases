import HRS.MS.R26T8AO03b7

/-!
# S8.2 T8A O03b (part 8): the commutator source `hSource` is linear in `f` and integrable against the thermal law
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U HRS.MS.S82W HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_o03b_grad_add {f g : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    gradient (f + g) = gradient f + gradient g := by
  funext x
  unfold gradient
  have e : fderiv ℝ (f + g) x = fderiv ℝ f x + fderiv ℝ g x :=
    fderiv_add (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)
  rw [e, map_add]
  rfl

theorem r26t8a_o03b_grad_smul (c : ℝ) {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) :
    gradient (c • f) = c • gradient f := by
  funext x
  unfold gradient
  have e : fderiv ℝ (c • f) x = c • fderiv ℝ f x := fderiv_const_smul (hf.differentiable (by simp) x) c
  rw [e, map_smul]
  rfl

theorem r26t8a_o03b_hs_add {f g : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x y : Euc d) :
    hSource (f + g) x y = hSource f x y + hSource g x y := by
  unfold hSource commutatorKernel
  rw [r26t8a_o03b_grad_add hf hg]
  simp only [Pi.add_apply]
  rw [← inner_add_left]
  congr 1
  abel

theorem r26t8a_o03b_hs_smul (c : ℝ) {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (x y : Euc d) :
    hSource (c • f) x y = c * hSource f x y := by
  unfold hSource commutatorKernel
  rw [r26t8a_o03b_grad_smul c hf]
  simp only [Pi.smul_apply, ← smul_sub, inner_smul_left]
  simp

theorem r26t8a_o03b_hs_meas (f : Euc d → ℝ) :
    Measurable (fun p : Euc d × Euc d => hSource f p.1 p.2) := by
  have hG : Measurable (gradient f) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)
  have hK : Measurable (rieszKernelGrad d (criticalS d)) := by
    unfold rieszKernelGrad gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp
      (measurable_fderiv ℝ (rieszKernel d (criticalS d)))
  unfold hSource commutatorKernel
  exact ((hG.comp measurable_fst).sub (hG.comp measurable_snd)).inner
    (hK.comp (measurable_fst.sub measurable_snd))

set_option maxHeartbeats 6400000 in
theorem r26t8a_o03b_hs_int (hd : 2 ≤ d) {a beta : ℝ} (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) {f : Euc d → ℝ} {A : ℝ}
    (hTB : TestBound (testOrder d) A f) (x : Euc d) :
    Integrable (hSource f x) (HRS.Whole.withDensityReal rho) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  have hsd : criticalS d < d := by unfold criticalS; linarith
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  obtain ⟨hdiff, C, c, hC, hc, hb⟩ := HRS.MS.Wad.s84_thermal_gaussReg hd ha hbeta hrho
  have hρs : ContDiff ℝ ∞ rho := (HRS.MS.Mov0.mv0_hgauss hd hs0.le hsd ha hbeta hrho).1
  have hρi : Integrable rho := Integrable.of_integral_ne_zero (by rw [hprob.integral_one]; norm_num)
  have hρK : ∀ y, rho y ≤ C := fun y => by
    refine (le_abs_self _).trans ((hb y).1.trans ?_)
    have : Real.exp (-c * ‖y‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖y‖])
    nlinarith
  obtain ⟨Ω, hΩ0, hΩ⟩ := r26t8a_f25_conv_bound hd hs0 hsd
  set Rn : ℝ := ‖r26t8a_Rz d‖ with hRn
  have hRn0 : 0 ≤ Rn := norm_nonneg (r26t8a_Rz d)
  obtain ⟨hf, hj⟩ := hTB
  have hA : 0 ≤ A := (norm_nonneg _).trans (hj 1 le_rfl (by unfold testOrder; omega) 0)
  have hf2 : ∀ w, ‖iteratedFDeriv ℝ 2 f w‖ ≤ A := fun w => hj 2 (by norm_num) (by unfold testOrder; omega) w
  have hae : ∀ᵐ y : Euc d ∂volume, y ≠ x := compl_mem_ae_iff.mpr (measure_singleton x)
  set μ := HRS.Whole.withDensityReal rho with hμ
  obtain ⟨hI, hIb⟩ := hΩ rho C (fun y => hprob.nonneg y) hρK hρs.continuous hρi x
  set g : Euc d → ℝ := fun y => Rn * A * criticalS d * (1 + ‖x - y‖ ^ (-criticalS d)) with hg
  have hgi : Integrable g μ := by
    rw [r26t8a_f25_wd_integrable hprob]
    have := hI.const_mul (Rn * A * criticalS d)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [hg]; ring
  have hbound : ∀ᵐ y ∂μ, ‖hSource f x y‖ ≤ g y := by
    have hae' : ∀ᵐ y ∂μ, y ≠ x :=
      (withDensity_absolutelyContinuous volume (fun x => ENNReal.ofReal (rho x))).ae_le
        (by filter_upwards [hae] with y hy using hy)
    filter_upwards [hae'] with y hy
    have hxy : x - y ≠ 0 := sub_ne_zero.2 hy.symm
    have hn : 0 < ‖x - y‖ := norm_pos_iff.2 hxy
    have hG := r26t8a_norm_rieszGrad hs0 hxy
    have hL := r26t8a_o02_grad_lip hf hf2 x y
    unfold hSource commutatorKernel
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hG]
    have e : ‖x - y‖ * ‖x - y‖ ^ (-criticalS d - 1) = ‖x - y‖ ^ (-criticalS d) := by
      rw [← Real.rpow_one_add' hn.le (by linarith)]; congr 1; ring
    have hp : 0 ≤ ‖x - y‖ ^ (-criticalS d) := Real.rpow_nonneg hn.le _
    calc ‖gradient f x - gradient f y‖ * (criticalS d * ‖x - y‖ ^ (-criticalS d - 1))
        ≤ (Rn * A * ‖x - y‖) * (criticalS d * ‖x - y‖ ^ (-criticalS d - 1)) :=
          mul_le_mul_of_nonneg_right hL (by positivity)
      _ = Rn * A * criticalS d * ‖x - y‖ ^ (-criticalS d) := by rw [← e]; ring
      _ ≤ g y := by
          simp only [hg]
          have : 0 ≤ Rn * A * criticalS d := by positivity
          nlinarith
  have hm : AEStronglyMeasurable (hSource f x) μ :=
    ((r26t8a_o03b_hs_meas f).comp (measurable_prodMk_left (x := x))).aestronglyMeasurable
  exact Integrable.mono' hgi hm hbound

end HRS.MS.R26T8A
