import HRS.MS.S111X2Aux6

/-!
# S11.1 X2, packet E02 (part 2): the nonlocal integration by parts

`s111x2_nonlocal_ibp`: for `ρ ∈ C²` with Gaussian envelope for `ρ, Dρ` and `h ∈ C²` with bounded `Dh, D²h`,
`∫ g(x-y) (ρ Δh + ⟨∇ρ,∇h⟩)(y) dy = ∫ ρ(y) ⟨∇h(y), ∇g(x-y)⟩ dy`  (singular kernel `g`, `0 ≤ s`, `s+1 < d`).
The weak derivative of the kernel is `HRS.Whole.movtr_eq_zero`/`movtr_force_apply` applied to `ρ ∂_j h`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X2

open HRS HRS.Whole

variable {d : ℕ}

/-- `g(x-·) φ` is integrable for `φ` continuous with a Gaussian envelope. -/
theorem s111x2_g_conv_integrable (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {c C : ℝ} (hc : 0 < c)
    (hC : 0 ≤ C) {φ : Euc d → ℝ} (hφm : Continuous φ) (hφ : ∀ y, |φ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2))
    (x : Euc d) : Integrable (fun z => rieszKernel d s z * φ (x - z)) := by
  have hgm : Measurable (rieszKernel d s) := by
    rw [← movtr_gEps_zero d s]; exact movtr_gEps_measurable s 0
  refine ((movtr_majorant_integrable hd hs0 hsd (c := c / 2) (by positivity)).const_mul
    (C * Real.exp (c * ‖x‖ ^ 2))).mono'
    (hgm.aestronglyMeasurable.mul (hφm.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    ?_
  filter_upwards [movtr_ae_ne_zero (d := d) hd] with z hz
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  have hg := movtr_gEps_abs_le hs0 le_rfl zero_le_one hz
  rw [movtr_gEps_zero] at hg
  have hfz : |φ (x - z)| ≤ C * (Real.exp (c * ‖x‖ ^ 2) * Real.exp (-(c / 2) * ‖z‖ ^ 2)) :=
    (hφ _).trans (mul_le_mul_of_nonneg_left (movtr_gauss_shift hc le_rfl z) hC)
  calc |rieszKernel d s z| * |φ (x - z)|
      ≤ (2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) *
          (C * (Real.exp (c * ‖x‖ ^ 2) * Real.exp (-(c / 2) * ‖z‖ ^ 2))) :=
        mul_le_mul hg hfz (abs_nonneg _) ((abs_nonneg _).trans hg)
    _ = C * Real.exp (c * ‖x‖ ^ 2) *
          ((2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) * Real.exp (-(c / 2) * ‖z‖ ^ 2)) := by ring

theorem s111x2_nonlocal_ibp (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s + 1 < d) {ρ : Euc d → ℝ} {M : ℝ}
    (K : HRS.MS.S111X1.KData d s ρ M) (hρ2 : ContDiff ℝ 2 ρ) {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hρ0 : ∀ y, |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2))
    (hρ1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ C * Real.exp (-c * ‖y‖ ^ 2))
    {h : Euc d → ℝ} (hh : ContDiff ℝ 2 h) {B1 B2 : ℝ} (h1 : ∀ x, ‖fderiv ℝ h x‖ ≤ B1)
    (h2 : ∀ x, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ B2) (x : Euc d) :
    ∫ y, rieszKernel d s (x - y) *
        (ρ y * Laplacian.laplacian h y + inner ℝ (gradient ρ y) (gradient h y)) =
      ∫ y, ρ y * inner ℝ (gradient h y) (rieszKernelGrad d s (x - y)) := by
  have hsd : s < d := by linarith
  set b := EuclideanSpace.basisFun (Fin d) ℝ with hb
  have hbn : ∀ j, ‖b j‖ = 1 := fun j => b.norm_eq_one j
  have hbj : ∀ j, (b j : Euc d) = EuclideanSpace.single j 1 := fun j => by simp [hb]
  have hB1 : 0 ≤ B1 := (norm_nonneg _).trans (h1 0)
  have hB2 : 0 ≤ B2 := (norm_nonneg (fderiv ℝ (fderiv ℝ h) 0)).trans (h2 0)
  have hh1 : ContDiff ℝ 1 (fderiv ℝ h) := hh.fderiv_right (by norm_num)
  have hρ1' : ContDiff ℝ 1 ρ := hρ2.of_le (by norm_num)
  let F : Fin d → Euc d → ℝ := fun j y => ρ y * fderiv ℝ h y (b j)
  have hFc : ∀ j, ContDiff ℝ 1 (F j) := fun j =>
    hρ1'.mul (hh1.clm_apply contDiff_const)
  have hDh : ∀ j, Differentiable ℝ (fun y => fderiv ℝ h y (b j)) := fun j =>
    (hh1.differentiable (by norm_num)).clm_apply (differentiable_const _)
  have hFd : ∀ j y, fderiv ℝ (F j) y =
      ρ y • fderiv ℝ (fun y => fderiv ℝ h y (b j)) y + (fderiv ℝ h y (b j)) • fderiv ℝ ρ y := by
    intro j y
    exact fderiv_fun_mul (hρ1'.differentiable (by norm_num) y) (hDh j y)
  have hDh_apply : ∀ j y v, fderiv ℝ (fun y => fderiv ℝ h y (b j)) y v =
      fderiv ℝ (fderiv ℝ h) y v (b j) := by
    intro j y v
    have := ((hh1.differentiable (by norm_num)) y).hasFDerivAt.clm_apply (hasFDerivAt_const (b j) y)
    rw [this.fderiv]
    simp
  have hDhd : ∀ j y, ‖fderiv ℝ (fun y => fderiv ℝ h y (b j)) y‖ ≤ B2 := by
    intro j y
    refine ContinuousLinearMap.opNorm_le_bound _ hB2 fun v => ?_
    rw [hDh_apply]
    have h3 := (fderiv ℝ (fderiv ℝ h) y).le_opNorm₂ v (b j)
    rw [hbn j, mul_one] at h3
    calc ‖fderiv ℝ (fderiv ℝ h) y v (b j)‖ ≤ ‖fderiv ℝ (fderiv ℝ h) y‖ * ‖v‖ := h3
      _ ≤ B2 * ‖v‖ := by gcongr; exact h2 y
  have hDhb : ∀ j y, |fderiv ℝ h y (b j)| ≤ B1 := fun j y => by
    have := (fderiv ℝ h y).le_opNorm (b j)
    rw [hbn j, mul_one] at this
    rw [← Real.norm_eq_abs]
    exact this.trans (h1 y)
  have hF0 : ∀ j y, |F j y| ≤ (C * B1) * Real.exp (-c * ‖y‖ ^ 2) := by
    intro j y
    simp only [F]
    rw [abs_mul]
    calc |ρ y| * |fderiv ℝ h y (b j)| ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * B1 :=
          mul_le_mul (hρ0 y) (hDhb j y) (abs_nonneg _) (mul_nonneg hC (Real.exp_pos _).le)
      _ = _ := by ring
  have hF1 : ∀ j y, ‖fderiv ℝ (F j) y‖ ≤ (C * (B1 + B2)) * Real.exp (-c * ‖y‖ ^ 2) := by
    intro j y
    rw [hFd]
    have hE := Real.exp_pos (-c * ‖y‖ ^ 2)
    have a1 : ‖ρ y • fderiv ℝ (fun y => fderiv ℝ h y (b j)) y‖ ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * B2 := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hρ0 y) (hDhd j y) (norm_nonneg _) (mul_nonneg hC hE.le)
    have a2 : ‖(fderiv ℝ h y (b j)) • fderiv ℝ ρ y‖ ≤ B1 * (C * Real.exp (-c * ‖y‖ ^ 2)) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hDhb j y) (hρ1 y) (norm_nonneg _) hB1
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * B2 + B1 * (C * Real.exp (-c * ‖y‖ ^ 2)) := add_le_add a1 a2
      _ = _ := by ring
  -- pointwise value of the diagonal derivative
  have hFdiag : ∀ j y, fderiv ℝ (F j) y (b j) =
      ρ y * fderiv ℝ (fderiv ℝ h) y (b j) (b j) + fderiv ℝ h y (b j) * fderiv ℝ ρ y (b j) := by
    intro j y
    rw [hFd]
    simp [hDh_apply]
  have hsumF : ∀ y, ∑ j, fderiv ℝ (F j) y (b j) =
      ρ y * Laplacian.laplacian h y + inner ℝ (gradient ρ y) (gradient h y) := by
    intro y
    simp_rw [hFdiag]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
      InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis h b]
    simp only [iteratedFDeriv_two_apply]
    congr 1
    have e1 : ∀ j, fderiv ℝ h y (b j) = inner ℝ (b j) (gradient h y) := fun j => by
      rw [HRS.MS.PoisKolm.kl_inner_gradient]
    have e2 : ∀ j, fderiv ℝ ρ y (b j) = inner ℝ (b j) (gradient ρ y) := fun j => by
      rw [HRS.MS.PoisKolm.kl_inner_gradient]
    simp_rw [e1, e2]
    have := b.sum_inner_mul_inner (gradient ρ y) (gradient h y)
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm (gradient ρ y) (b j)]; ring
  have hcont : ∀ j, Continuous fun y => fderiv ℝ (F j) y (b j) := fun j =>
    ((hFc j).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hbnd : ∀ j y, |fderiv ℝ (F j) y (b j)| ≤ (C * (B1 + B2)) * Real.exp (-c * ‖y‖ ^ 2) := by
    intro j y
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ (F j) y (b j)‖ ≤ ‖fderiv ℝ (F j) y‖ * ‖b j‖ := (fderiv ℝ (F j) y).le_opNorm _
      _ ≤ _ := by rw [hbn j, mul_one]; exact hF1 j y
  have hCC : 0 ≤ C * (B1 + B2) := mul_nonneg hC (add_nonneg hB1 hB2)
  have hint : ∀ j, Integrable (fun y => rieszKernel d s (x - y) * fderiv ℝ (F j) y (b j)) := by
    intro j
    have := s111x2_g_conv_integrable hd hs0 hsd hc hCC (hcont j) (hbnd j) x
    have h' := (this.comp_sub_left x)
    refine h'.congr (Filter.Eventually.of_forall fun y => ?_)
    simp
  have hj : ∀ j, ∫ y, rieszKernel d s (x - y) * fderiv ℝ (F j) y (b j) =
      (convGradConvW (rieszKernelGrad d s) (F j) x) j := by
    intro j
    rw [movtr_force_apply hd hs0 hsd hc (C := C * B1 + C * (B1 + B2) ) (by positivity) (hFc j)
      (fun y => (hF0 j y).trans (by
        have := Real.exp_pos (-c * ‖y‖ ^ 2)
        nlinarith [mul_nonneg hC hB1, mul_nonneg hC hB2]))
      (fun y => (hF1 j y).trans (by
        have := Real.exp_pos (-c * ‖y‖ ^ 2)
        nlinarith [mul_nonneg hC hB1, mul_nonneg hC hB2])) x j]
    rw [← hbj j]
    rw [← movtr_eq_zero hd hs0 hsd hc (C := C * B1 + C * (B1 + B2)) (by positivity) (hFc j)
      (fun y => (hF0 j y).trans (by
        have := Real.exp_pos (-c * ‖y‖ ^ 2)
        nlinarith [mul_nonneg hC hB1, mul_nonneg hC hB2]))
      (fun y => (hF1 j y).trans (by
        have := Real.exp_pos (-c * ‖y‖ ^ 2)
        nlinarith [mul_nonneg hC hB1, mul_nonneg hC hB2])) x (b j) (by rw [hbn j])]
    rw [← integral_sub_left_eq_self (fun z => rieszKernel d s z * fderiv ℝ (F j) (x - z) (b j)) volume x]
    simp
  have hgradm : Measurable (gradient h) := by
    have : Continuous fun x => (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ h x) :=
      (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp (hh.continuous_fderiv (by norm_num))
    exact this.measurable
  have hnl := HRS.MS.S111X1.nl_plain K (a := gradient h) hgradm (Ba := B1)
    (fun y => by simpa [gradient] using h1 y) x
  have hFeq : ∀ j, F j = fun y => ρ y * gradient h y j := by
    intro j
    funext y
    simp only [F]
    congr 1
    rw [hbj j]
    have e := HRS.MS.PoisKolm.kl_inner_gradient h y (EuclideanSpace.single j (1 : ℝ))
    rw [EuclideanSpace.inner_single_left] at e
    simpa using e.symm
  calc ∫ y, rieszKernel d s (x - y) *
        (ρ y * Laplacian.laplacian h y + inner ℝ (gradient ρ y) (gradient h y))
      = ∫ y, ∑ j, rieszKernel d s (x - y) * fderiv ℝ (F j) y (b j) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only
        rw [← hsumF, Finset.mul_sum]
    _ = ∑ j, ∫ y, rieszKernel d s (x - y) * fderiv ℝ (F j) y (b j) :=
        integral_finset_sum _ fun j _ => hint j
    _ = ∑ j, (convGradConvW (rieszKernelGrad d s) (F j) x) j := Finset.sum_congr rfl fun j _ => hj j
    _ = ∑ j, (convGradConvW (rieszKernelGrad d s) (fun y => ρ y * gradient h y j) x) j := by
        simp_rw [hFeq]
    _ = _ := hnl

end HRS.MS.S111X2
