import HRS.Whole.MovtrAux3

/-!
# MOVTR auxiliary 4: the cancellation-convention force is the gradient of the potential
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

lemma movtr_rieszKernelGrad_measurable (s : ℝ) : Measurable (rieszKernelGrad d s) := by
  unfold rieszKernelGrad gradient
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp
    (measurable_fderiv ℝ _)

lemma movtr_force_eq (s : ℝ) (ρ : Euc d → ℝ) (x : Euc d) :
    convGradConvW (rieszKernelGrad d s) ρ x = ∫ z, movtr_R ρ x z • rieszKernelGrad d s z := by
  unfold convGradConvW
  rw [← integral_sub_left_eq_self (fun y => if ‖x - y‖ ≤ 1 / 4 then
    (ρ y - ρ x) • rieszKernelGrad d s (x - y) else ρ y • rieszKernelGrad d s (x - y)) volume x]
  congr 1
  funext z
  unfold movtr_R
  simp only [sub_sub_cancel]
  split_ifs <;> rfl

lemma movtr_force_integrable (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {c C : ℝ} (hc : 0 < c)
    (hC : 0 ≤ C) {ρ : Euc d → ℝ} (hρ1 : ContDiff ℝ 1 ρ)
    (h0 : ∀ y, |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2))
    (h1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ C * Real.exp (-c * ‖y‖ ^ 2)) (x : Euc d) :
    Integrable (fun z => movtr_R ρ x z • rieszKernelGrad d s z) := by
  have hρc : Continuous ρ := hρ1.continuous
  refine Integrable.mono' (movtr_b2_integrable hd hs0 hsd hc x (C := C)) ?_ ?_
  · exact ((movtr_R_measurable hρc x).smul (movtr_rieszKernelGrad_measurable s)).aestronglyMeasurable
  · filter_upwards [movtr_ae_ne_zero (d := d) hd] with z hz
    rw [norm_smul]
    have := movtr_b2_bound_gen hd hs0 hsd hc hC hρ1 h0 h1 x hz (a := ‖rieszKernelGrad d s z‖) (by
      rw [abs_norm, movtr_rieszKernelGrad_norm s hs0 hz])
    calc ‖movtr_R ρ x z‖ * ‖rieszKernelGrad d s z‖
        = |‖rieszKernelGrad d s z‖ * movtr_R ρ x z| := by
          rw [abs_mul, abs_norm, Real.norm_eq_abs, mul_comm]
      _ ≤ _ := this

lemma movtr_force_apply (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {c C : ℝ} (hc : 0 < c)
    (hC : 0 ≤ C) {ρ : Euc d → ℝ} (hρ1 : ContDiff ℝ 1 ρ)
    (h0 : ∀ y, |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2))
    (h1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ C * Real.exp (-c * ‖y‖ ^ 2)) (x : Euc d) (i : Fin d) :
    (convGradConvW (rieszKernelGrad d s) ρ x) i =
      ∫ z, movtr_dEps d s 0 (EuclideanSpace.single i 1) z * movtr_R ρ x z := by
  rw [movtr_force_eq]
  have hint := movtr_force_integrable hd hs0 hsd hc hC hρ1 h0 h1 x
  have key : (∫ z, movtr_R ρ x z • rieszKernelGrad d s z) i =
      ∫ z, (movtr_R ρ x z • rieszKernelGrad d s z) i :=
    (ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) hint).symm
  rw [key]
  refine integral_congr_ae ?_
  filter_upwards [movtr_ae_ne_zero (d := d) hd] with z hz
  simp [movtr_rieszKernelGrad_apply s hz i, mul_comm]


lemma movtr_norm_single (i : Fin d) : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ ≤ 1 := by
  simp

/-- The derivative of the potential `g * ρ` along `e_i` is the `i`-th component of the force. -/
lemma movtr_hasDerivAt_potential (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {c C : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) {ρ : Euc d → ℝ} (hρ1 : ContDiff ℝ 1 ρ)
    (h0 : ∀ y, |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2))
    (h1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ C * Real.exp (-c * ‖y‖ ^ 2)) (x : Euc d) (i : Fin d) :
    HasDerivAt (fun h : ℝ => ∫ y, rieszKernel d s (x + h • (EuclideanSpace.single i (1 : ℝ) : Euc d) - y) * ρ y)
      ((convGradConvW (rieszKernelGrad d s) ρ x) i) 0 := by
  set e : Euc d := EuclideanSpace.single i (1 : ℝ) with he_def
  have he : ‖e‖ ≤ 1 := movtr_norm_single i
  have hgm : Measurable (rieszKernel d s) := by
    rw [← movtr_gEps_zero d s]; exact movtr_gEps_measurable s 0
  have A := movtr_hasDerivAt_conv (c := c) hc (k := rieszKernel d s)
    (B := fun z => 2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) hgm.aestronglyMeasurable
    (by
      filter_upwards [movtr_ae_ne_zero (d := d) hd] with z hz
      rw [← movtr_gEps_zero d s]
      exact movtr_gEps_abs_le hs0 le_rfl zero_le_one hz)
    (movtr_majorant_integrable hd hs0 hsd (c := c / 2) (by positivity)) hC hρ1 h0 h1 x e he
  have hfun : (fun h : ℝ => ∫ z, rieszKernel d s z * ρ (x + h • e - z)) =
      fun h : ℝ => ∫ y, rieszKernel d s (x + h • e - y) * ρ y := by
    funext h
    rw [← integral_sub_left_eq_self (fun y => rieszKernel d s (x + h • e - y) * ρ y) volume
      (x + h • e)]
    simp
  rw [hfun] at A
  convert A using 1
  rw [movtr_force_apply hd hs0 hsd hc hC hρ1 h0 h1 x i, ← movtr_eq_zero hd hs0 hsd hc hC hρ1 h0 h1 x e he]

end HRS.Whole
