import HRS.Whole.Q34Aux2
import HRS.MS.R26T6CI01

/-! R26-T6C.I02: positive Riesz row in L2 from the squared-kernel estimate. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace HRS.MS.R26T6C
open HRS HRS.Whole HRS.Whole.Q34
variable {d : ℕ}

theorem r26t6c_riesz_row_L2 (hd : 2 ≤ d) (s M : ℝ)
    (hs : 0 < s) (h2s : 2 * s < d) (rho : Euc d → ℝ)
    (hrho : HRS.Whole.IsProbDensity rho) (hM : ∀ x, rho x ≤ M) (x : Euc d) :
    MemLp (fun y => HRS.Whole.rieszKernel d s (x-y)) 2 (HRS.Whole.withDensityReal rho) ∧
    eLpNorm (fun y => HRS.Whole.rieszKernel d s (x-y)) 2 (HRS.Whole.withDensityReal rho) ≤
      ENNReal.ofReal (Real.sqrt (M * sphereArea d / ((d : ℝ)-2*s) + 1)) := by
  set μ : Measure (Euc d) := HRS.Whole.withDensityReal rho with hμ
  letI : IsProbabilityMeasure μ := Q34.isProbabilityMeasure_nu hrho
  have hs2 : 0 < 2 * s := by linarith
  have hd2 : (2 : ℝ) * s < d := h2s
  have hM0 : 0 ≤ M := (hrho.nonneg 0).trans (hM 0)
  have hdpos : 0 < (d : ℝ) - 2 * s := by linarith
  have hSphere : 0 ≤ sphereArea d := Q34.sphereArea_nonneg (by omega : 1 ≤ d)
  set K : ℝ := M * sphereArea d / ((d : ℝ) - 2*s) + 1 with hK
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hkernel : ∀ y : Euc d,
      HRS.Whole.rieszKernel d s (x-y) = ‖x-y‖ ^ (-s) :=
    fun y => Q34.rieszKernel_eq (ne_of_gt hs) _
  have hsq : ∀ y : Euc d,
      (HRS.Whole.rieszKernel d s (x-y)) ^ 2 = ‖x-y‖ ^ (-(2*s)) := by
    intro y
    rw [hkernel]
    calc
      (‖x-y‖ ^ (-s)) ^ (2 : ℕ) = (‖x-y‖ ^ (-s)) ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ = ‖x-y‖ ^ ((-s) * 2) := (Real.rpow_mul (norm_nonneg _) (-s) 2).symm
      _ = _ := by congr 1; ring
  have hmeasure : ∫⁻ y, ENNReal.ofReal ((HRS.Whole.rieszKernel d s (x-y)) ^ 2) ∂μ ≤
      ENNReal.ofReal K := by
    simp_rw [hsq]
    simpa only [μ, K] using (Q34.lintegral_kernel_le (by omega : 1 ≤ d) hs2 hd2 hrho hM x)
  have hmeas : Measurable fun y : Euc d => HRS.Whole.rieszKernel d s (x-y) :=
    (Q34.measurable_rieszKernel (ne_of_gt hs)).comp (measurable_const.sub measurable_id)
  have hnonneg : ∀ y, 0 ≤ (HRS.Whole.rieszKernel d s (x-y)) ^ 2 :=
    fun y => sq_nonneg _
  have hintegrable : Integrable (fun y => (HRS.Whole.rieszKernel d s (x-y)) ^ 2) μ :=
    (Q34.integrable_of_lintegral_le (hmeas.pow_const 2) hnonneg hK0 hmeasure).1
  have hLp : MemLp (fun y => HRS.Whole.rieszKernel d s (x-y)) 2 μ :=
    (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 hintegrable
  refine ⟨hLp, ?_⟩
  have hnormsq : ∀ y, ‖HRS.Whole.rieszKernel d s (x-y)‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal ((HRS.Whole.rieszKernel d s (x-y)) ^ 2) := by
    intro y
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
      Real.rpow_two, sq_abs]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hmeas.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  simp_rw [hnormsq]
  calc
    (∫⁻ y, ENNReal.ofReal ((HRS.Whole.rieszKernel d s (x-y)) ^ 2) ∂μ) ^ (1 / 2 : ℝ) ≤
      (ENNReal.ofReal K) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hmeasure (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt K) := by
      rw [Real.sqrt_eq_rpow]
      exact ENNReal.ofReal_rpow_of_nonneg hK0 (by norm_num : 0 ≤ (1 / 2 : ℝ))

end HRS.MS.R26T6C
