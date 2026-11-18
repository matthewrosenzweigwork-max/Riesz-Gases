import HRS.MS.R26T8AP11g3
import HRS.MS.R26T8AF01b
import HRS.MS.R26T8AP11f23
import HRS.MS.MovForceAux1
import HRS.MS.R26T8AP10a16

/-!
# S8.2 T8A P11g (part 4): the thermal potential
For a thermal equilibrium `ρ`, `H = HRS.Whole.convFun (rieszKernel d (criticalS d)) ρ` is `C^1`, bounded, with bounded gradient and
`∂_j H = (forceMean ρ)_j`; `H u = ∫ ρ(x) ‖x - u‖^(-s) dx`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_g4_potential (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d (criticalS d) a β ρ) :
    ContDiff ℝ 1 (HRS.Whole.convFun (rieszKernel d (criticalS d)) ρ) ∧
    (∃ B0 : ℝ, ∀ u, |HRS.Whole.convFun (rieszKernel d (criticalS d)) ρ u| ≤ B0) ∧
    (∃ B1 : ℝ, ∀ u, ‖fderiv ℝ (HRS.Whole.convFun (rieszKernel d (criticalS d)) ρ) u‖ ≤ B1) ∧
    (∀ u (j : Fin d), fderiv ℝ (HRS.Whole.convFun (rieszKernel d (criticalS d)) ρ) u (EuclideanSpace.single j 1) =
      forceMean ρ u j) ∧
    (∀ u, HRS.Whole.convFun (rieszKernel d (criticalS d)) ρ u = ∫ x, ρ x * ‖x - u‖ ^ (-criticalS d)) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : 1 ≤ d := by omega
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  have hsd : criticalS d < d := by unfold criticalS; linarith
  obtain ⟨hρs, hg⟩ := HRS.MS.Mov0.mv0_hgauss hd hs0.le hsd ha hβ hρ
  obtain ⟨Cρ, cρ, hCρ, hcρ, hb⟩ := r26t8a_f23_rho_unif hg 1
  have hρ1 : ContDiff ℝ 1 ρ := hρs.of_le (by exact_mod_cast le_top)
  have h0 : ∀ y, |ρ y| ≤ Cρ * Real.exp (-cρ * ‖y‖ ^ 2) := fun y => by
    have := hb 0 (by omega) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have h1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ Cρ * Real.exp (-cρ * ‖y‖ ^ 2) := fun y => by
    have := hb 1 (by omega) y
    rwa [norm_iteratedFDeriv_one] at this
  have hF := fun x => HRS.MS.MovForce.mv1_force_eq_grad hd1 hs0.le hsd hcρ hCρ hρ1 h0 h1 x
  have hgrad : ∀ x, gradient (HRS.Whole.convFun (rieszKernel d (criticalS d)) ρ) x = forceMean ρ x := fun x =>
    ((hF x).1).symm
  have hdiff : Differentiable ℝ (HRS.Whole.convFun (rieszKernel d (criticalS d)) ρ) := fun x => (hF x).2
  have hfd : ∀ u (j : Fin d), fderiv ℝ (HRS.Whole.convFun (rieszKernel d (criticalS d)) ρ) u
      (EuclideanSpace.single j 1) = forceMean ρ u j := by
    intro u j
    rw [← movtr_gradient_apply, hgrad u]
  have hfc : Continuous (forceMean ρ) :=
    (r26t8a_thermal_force d hd a β ha hβ ρ hρ).1.continuous
  have hnorm : ∀ u, ‖fderiv ℝ (HRS.Whole.convFun (rieszKernel d (criticalS d)) ρ) u‖ = ‖forceMean ρ u‖ := fun u => by
    rw [← r26t8a_norm_gradient, hgrad u]
  have hC1 : ContDiff ℝ 1 (HRS.Whole.convFun (rieszKernel d (criticalS d)) ρ) := by
    rw [contDiff_one_iff_fderiv]
    refine ⟨hdiff, ?_⟩
    have hdual : fderiv ℝ (HRS.Whole.convFun (rieszKernel d (criticalS d)) ρ) = fun u => innerSL ℝ (forceMean ρ u) := by
      funext u
      ext v
      rw [← hgrad u]
      simp [gradient]
    rw [hdual]
    exact (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).continuous.comp hfc
  obtain ⟨Cf, hCf0, hCf⟩ := (r26t8a_thermal_force d hd a β ha hβ ρ hρ).2 0
  have hker : ∀ w : Euc d, rieszKernel d (criticalS d) w = ‖w‖ ^ (-criticalS d) := by
    intro w
    have hs : criticalS d ≠ 0 := hs0.ne'
    rw [rieszKernel, if_neg hs]
  have hcv : ∀ u, HRS.Whole.convFun (rieszKernel d (criticalS d)) ρ u = ∫ x, ρ x * ‖x - u‖ ^ (-criticalS d) := by
    intro u
    unfold HRS.Whole.convFun
    congr 1; funext x
    rw [hker, norm_sub_rev u x]; ring
  refine ⟨hC1, ?_, ⟨Cf, fun u => ?_⟩, hfd, hcv⟩
  · have hρ0 : ∀ y, 0 ≤ ρ y := hρ.1.1.nonneg
    have hρK : ∀ y, ρ y ≤ Cρ := fun y => by
      have := h0 y
      refine (le_abs_self _).trans (this.trans ?_)
      have : Real.exp (-cρ * ‖y‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖y‖])
      nlinarith
    have hρc : Continuous ρ := hρ1.continuous
    have hρi : Integrable ρ := Integrable.of_integral_ne_zero (by rw [hρ.1.1.integral_one]; norm_num)
    obtain ⟨Ω, hΩ0, hΩ⟩ := r26t8a_f25_conv_bound hd hs0 hsd
    refine ⟨3 * (∫ y, ρ y) + Cρ * Ω, fun u => ?_⟩
    obtain ⟨hI, hIb⟩ := hΩ ρ Cρ hρ0 hρK hρc hρi u
    rw [hcv u]
    have hint : Integrable (fun x => ρ x * ‖x - u‖ ^ (-criticalS d)) := by
      refine Integrable.mono' hI ?_ (Filter.Eventually.of_forall fun x => ?_)
      · exact (hρc.aestronglyMeasurable).mul
          ((measurable_id.sub measurable_const).norm.pow_const _).aestronglyMeasurable
      · rw [Real.norm_of_nonneg (mul_nonneg (hρ0 x) (Real.rpow_nonneg (norm_nonneg _) _))]
        rw [norm_sub_rev x u]
        exact mul_le_mul_of_nonneg_left (by linarith) (hρ0 x)
    have hle : ∫ x, ρ x * ‖x - u‖ ^ (-criticalS d) ≤ ∫ x, ρ x * (1 + ‖u - x‖ ^ (-criticalS d)) := by
      refine integral_mono hint hI fun x => ?_
      rw [norm_sub_rev x u]
      exact mul_le_mul_of_nonneg_left (by linarith) (hρ0 x)
    have hnn : 0 ≤ ∫ x, ρ x * ‖x - u‖ ^ (-criticalS d) :=
      integral_nonneg fun x => mul_nonneg (hρ0 x) (Real.rpow_nonneg (norm_nonneg _) _)
    rw [abs_of_nonneg hnn]
    exact hle.trans hIb
  · rw [hnorm u]
    have := hCf u
    rw [norm_iteratedFDeriv_zero] at this
    linarith [norm_nonneg (fderiv ℝ (iteratedFDeriv ℝ 0 (forceMean ρ)) u u)]

end HRS.MS.R26T8A
