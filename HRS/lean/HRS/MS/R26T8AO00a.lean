import HRS.MS.CritForceAssemblyMaj

/-!
# S8.2 observed-time layer, packet T8A.O00 (helper a): norm of the Riesz force kernel

For `s > 0` and `z ≠ 0`, `‖∇ rieszKernel d s z‖ = s ‖z‖^(-s-1)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole

theorem r26t8a_o00a_kernel_fun (d : ℕ) {s : ℝ} (hs : 0 < s) :
    rieszKernel d s = fun x => (‖x‖ ^ 2) ^ (-s / 2) := by
  funext x
  unfold rieszKernel
  rw [if_neg hs.ne', ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  push_cast
  ring

theorem r26t8a_o00a_kernel_grad (d : ℕ) {s : ℝ} (hs : 0 < s) (z : Euc d) (hz : z ≠ 0) :
    gradient (rieszKernel d s) z = (-s * ‖z‖ ^ (-s - 2)) • z := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hne : ‖z‖ ^ 2 ≠ 0 := (pow_pos hzn 2).ne'
  have hF : HasFDerivAt (rieszKernel d s)
      ((-s / 2 * (‖z‖ ^ 2) ^ (-s / 2 - 1)) • (2 • innerSL ℝ z)) z := by
    rw [r26t8a_o00a_kernel_fun d hs]
    exact (hasStrictFDerivAt_norm_sq z).hasFDerivAt.rpow_const (Or.inl hne)
  have hpow : (‖z‖ ^ 2) ^ (-s / 2 - 1) = ‖z‖ ^ (-s - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    push_cast
    ring
  unfold gradient
  rw [hF.fderiv, hpow, LinearIsometryEquiv.symm_apply_eq]
  ext w
  simp [innerSL_apply_apply]
  ring

theorem r26t8a_o00a_kernel_grad_norm (d : ℕ) {s : ℝ} (hs : 0 < s) (z : Euc d) (hz : z ≠ 0) :
    ‖gradient (rieszKernel d s) z‖ = s * ‖z‖ ^ (-s - 1) := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hp : 0 < ‖z‖ ^ (-s - 2) := Real.rpow_pos_of_pos hzn _
  have e : ‖z‖ ^ (-s - 1) = ‖z‖ ^ (-s - 2) * ‖z‖ := by
    rw [show (-s - 1 : ℝ) = (-s - 2) + 1 by ring, Real.rpow_add hzn, Real.rpow_one]
  rw [r26t8a_o00a_kernel_grad d hs z hz, norm_smul, Real.norm_eq_abs, abs_mul, abs_neg,
    abs_of_pos hs, abs_of_pos hp, e]
  ring

end HRS.MS.R26T8A

end
