import HRS.MS.R2SeAux32

/-!
# S9.9 `r2_static_edgeworth`, packet 33: the gradient of the potentials

Worker S99, namespace `S99`.  For `r = ρ u` (`u ∈ C_b^1`, `ρ` the thermal density) and `G(x) = ∫ g(x-y) r(y) dy`:
if `G` is differentiable then `D G(x) e = ∫ g(x-y) D r(y) e dy` (copy of `s45_gradU_apply` for a signed density).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

section PotC

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β C c BU : ℝ} (hT : ThermalData d s a β C c BU)

include hd hs0 hsd hT

theorem s99_Gpot_leb (u : Euc d → ℝ) (x : Euc d) :
    Gpot d s a β u x = ∫ y, rieszKernel d s (x - y) * (thermalDensity d s a β y * u y) := by
  unfold Gpot
  show ∫ y, rieszKernel d s (x - y) * u y ∂(withDensityReal (thermalDensity d s a β)) = _
  rw [HRS.MS.S98.s98_integral_wDR _ hT.smooth.continuous.measurable (fun y => (hT.pos y).le)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only; ring

/-- Gaussian bounds for `r = ρ u`. -/
theorem s99_r_bounds {u : Euc d → ℝ} (hu : ContDiff ℝ 1 u) {Bu Du : ℝ} (hBu : ∀ x, |u x| ≤ Bu)
    (hDu : ∀ x, ‖fderiv ℝ u x‖ ≤ Du) :
    ContDiff ℝ 1 (fun y => thermalDensity d s a β y * u y) ∧
    (∀ y, |thermalDensity d s a β y * u y| ≤ (C * (Bu + Du + 1)) * Real.exp (-c * ‖y‖ ^ 2)) ∧
    (∀ y, ‖fderiv ℝ (fun y => thermalDensity d s a β y * u y) y‖ ≤
      (C * (Bu + Du + 1)) * Real.exp (-c * ‖y‖ ^ 2)) := by
  have hBu0 : 0 ≤ Bu := (abs_nonneg _).trans (hBu 0)
  have hDu0 : 0 ≤ Du := (norm_nonneg _).trans (hDu 0)
  have hρ1 : ContDiff ℝ 1 (thermalDensity d s a β) := hT.smooth.of_le (by exact_mod_cast le_top)
  refine ⟨hρ1.mul hu, fun y => ?_, fun y => ?_⟩
  · rw [abs_mul, abs_of_pos (hT.pos y)]
    have h0 : thermalDensity d s a β y ≤ C * Real.exp (-c * ‖y‖ ^ 2) := by
      simpa [abs_of_pos (hT.pos y)] using hT.h0 y
    calc thermalDensity d s a β y * |u y| ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * Bu :=
          mul_le_mul h0 (hBu y) (abs_nonneg _) (mul_nonneg hT.C0 (Real.exp_pos _).le)
      _ ≤ (C * (Bu + Du + 1)) * Real.exp (-c * ‖y‖ ^ 2) := by
          have := hT.C0; have := (Real.exp_pos (-c * ‖y‖ ^ 2)).le
          nlinarith [mul_nonneg this (by linarith : (0 : ℝ) ≤ Du + 1)]
  · have hd1 : DifferentiableAt ℝ (thermalDensity d s a β) y := (hρ1.differentiable (by norm_num)) y
    have hd2 : DifferentiableAt ℝ u y := (hu.differentiable (by norm_num)) y
    have hm : HasFDerivAt (fun y => thermalDensity d s a β y * u y)
        (thermalDensity d s a β y • fderiv ℝ u y + u y • fderiv ℝ (thermalDensity d s a β) y) y :=
      hd1.hasFDerivAt.mul hd2.hasFDerivAt
    rw [hm.fderiv]
    refine (norm_add_le _ _).trans ?_
    have h0 : thermalDensity d s a β y ≤ C * Real.exp (-c * ‖y‖ ^ 2) := by
      simpa [abs_of_pos (hT.pos y)] using hT.h0 y
    have hexp := (Real.exp_pos (-c * ‖y‖ ^ 2)).le
    have e1 : ‖thermalDensity d s a β y • fderiv ℝ u y‖ ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * Du := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hT.pos y)]
      exact mul_le_mul h0 (hDu y) (norm_nonneg _) (mul_nonneg hT.C0 hexp)
    have e2 : ‖u y • fderiv ℝ (thermalDensity d s a β) y‖ ≤ Bu * (C * Real.exp (-c * ‖y‖ ^ 2)) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hBu y) (hT.h1 y) (norm_nonneg _) hBu0
    refine (add_le_add e1 e2).trans ?_
    have := hT.C0
    nlinarith [mul_nonneg this hexp]

theorem s99_Gpot_fderiv {u : Euc d → ℝ} (hu : ContDiff ℝ 1 u) {Bu Du : ℝ} (hBu : ∀ x, |u x| ≤ Bu)
    (hDu : ∀ x, ‖fderiv ℝ u x‖ ≤ Du) (hdiff : Differentiable ℝ (Gpot d s a β u)) (x e : Euc d)
    (he : ‖e‖ ≤ 1) :
    fderiv ℝ (Gpot d s a β u) x e = ∫ y, rieszKernel d s (x - y) *
      fderiv ℝ (fun y => thermalDensity d s a β y * u y) y e := by
  obtain ⟨hr1, hr0, hr1'⟩ := s99_r_bounds hd hs0 hsd hT hu hBu hDu
  have hBu0 : 0 ≤ Bu := (abs_nonneg _).trans (hBu 0)
  have hDu0 : 0 ≤ Du := (norm_nonneg _).trans (hDu 0)
  have hC' : 0 ≤ C * (Bu + Du + 1) := by have := hT.C0; positivity
  have hgm : Measurable (rieszKernel d s) := by
    rw [← movtr_gEps_zero d s]; exact movtr_gEps_measurable s 0
  have A := movtr_hasDerivAt_conv (c := c) hT.hc (k := rieszKernel d s)
    (B := fun z => 2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) hgm.aestronglyMeasurable
    (by
      filter_upwards [movtr_ae_ne_zero (d := d) (by omega)] with z hz
      rw [← movtr_gEps_zero d s]
      exact movtr_gEps_abs_le hs0 le_rfl zero_le_one hz)
    (movtr_majorant_integrable (by omega) hs0 hsd (c := c / 2) (by have := hT.hc; positivity)) hC' hr1 hr0 hr1'
    x e he
  have hfun : (fun h : ℝ => ∫ z, rieszKernel d s z *
      (fun y => thermalDensity d s a β y * u y) (x + h • e - z)) =
      fun h : ℝ => Gpot d s a β u (x + h • e) := by
    funext h
    rw [s99_Gpot_leb hd hs0 hsd hT u (x + h • e), ← integral_sub_left_eq_self
      (fun y => rieszKernel d s (x + h • e - y) * (thermalDensity d s a β y * u y)) volume (x + h • e)]
    simp
  rw [hfun] at A
  have hline : HasDerivAt (fun h : ℝ => x + h • e) e 0 := by
    have := ((hasDerivAt_id (0:ℝ)).smul_const e).const_add x
    simpa using this
  have hB := (hdiff (x + (0 : ℝ) • e)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline
  have hEq := A.unique hB
  simp only [zero_smul, add_zero] at hEq
  rw [← hEq]
  rw [← integral_sub_left_eq_self (fun z => rieszKernel d s z *
    fderiv ℝ (fun y => thermalDensity d s a β y * u y) (x - z) e) volume x]
  simp

end PotC

end S99

end
