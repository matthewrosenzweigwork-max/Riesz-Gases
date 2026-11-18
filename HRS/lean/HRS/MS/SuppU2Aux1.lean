import HRS.Whole.Adjoint

/-!
# U2 auxiliary 1: the kernel `K = ∇g` away from the origin

Explicit formula, homogeneity, smoothness and derivative bounds `‖D^j κ(z)‖ ≤ C ‖z‖^{-a-j}` for the
components `κ = K_i` (`a = s+1`), and local integrability of `‖z‖^{-a}`, `0 < a < d`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

/-- `σ = 1` for the logarithmic kernel, `σ = s` otherwise. -/
def u2_sigma (s : ℝ) : ℝ := if s = 0 then 1 else s

lemma u2_hasFDerivAt_normSq (z : Euc d) :
    HasFDerivAt (fun y : Euc d => ‖y‖ ^ 2) ((2 : ℝ) • innerSL ℝ z) z := by
  have h := (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have e : ((2 : ℕ) • innerSL ℝ z : Euc d →L[ℝ] ℝ) = (2 : ℝ) • innerSL ℝ z := by
    rw [two_smul, two_smul]
  rw [e] at h
  exact h

lemma u2_rieszKernel_eq_comp (s : ℝ) :
    rieszKernel d s = (fun u : ℝ => if s = 0 then -(1 / 2) * Real.log u else u ^ (-s / 2)) ∘
      (fun y : Euc d => ‖y‖ ^ 2) := by
  funext z
  unfold rieszKernel
  by_cases hs : s = 0
  · simp [hs, Real.log_pow]
  · simp only [hs, ite_false, Function.comp]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg z)]
    congr 1
    push_cast
    ring

lemma u2_hasFDerivAt_rieszKernel (s : ℝ) (z : Euc d) (hz : z ≠ 0) :
    HasFDerivAt (rieszKernel d s)
      ((-(u2_sigma s * (‖z‖ ^ 2) ^ (-s / 2 - 1))) • innerSL ℝ z) z := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hu : 0 < ‖z‖ ^ 2 := by positivity
  have hinner := u2_hasFDerivAt_normSq z
  rw [u2_rieszKernel_eq_comp]
  by_cases hs : s = 0
  · subst hs
    have h1 : HasDerivAt (fun u : ℝ => -(1 / 2) * Real.log u) (-(1 / 2) * (‖z‖ ^ 2)⁻¹)
        (‖z‖ ^ 2) := (Real.hasDerivAt_log hu.ne').const_mul _
    have h2 := h1.comp_hasFDerivAt z hinner
    simp only [ite_true]
    convert h2 using 1
    simp only [u2_sigma, ite_true, neg_zero, zero_div, zero_sub]
    rw [Real.rpow_neg_one, smul_smul]
    congr 1
    ring
  · have h1 : HasDerivAt (fun u : ℝ => u ^ (-s / 2)) ((-s / 2) * (‖z‖ ^ 2) ^ (-s / 2 - 1))
        (‖z‖ ^ 2) := Real.hasDerivAt_rpow_const (Or.inl hu.ne')
    have h2 := h1.comp_hasFDerivAt z hinner
    simp only [hs, ite_false]
    convert h2 using 1
    simp only [u2_sigma, hs, ite_false, smul_smul]
    congr 1
    ring

/-- The force `∇g(z)` off the origin. -/
lemma u2_rieszKernelGrad_eq (s : ℝ) {z : Euc d} (hz : z ≠ 0) :
    rieszKernelGrad d s z = (-(u2_sigma s * (‖z‖ ^ 2) ^ (-s / 2 - 1))) • z := by
  have h := u2_hasFDerivAt_rieszKernel (d := d) s z hz
  have h2 : HasGradientAt (rieszKernel d s) ((-(u2_sigma s * (‖z‖ ^ 2) ^ (-s / 2 - 1))) • z) z := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert h using 1
    ext v
    simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
  unfold rieszKernelGrad
  rw [h2.gradient]

/-- The scalar kernel `κ_i = (∇g)_i`. -/
def u2_kap (d : ℕ) (s : ℝ) (i : Fin d) (z : Euc d) : ℝ := rieszKernelGrad d s z i

lemma u2_kap_eq (s : ℝ) (i : Fin d) {z : Euc d} (hz : z ≠ 0) :
    u2_kap d s i z = -(u2_sigma s * (‖z‖ ^ 2) ^ (-s / 2 - 1)) * z i := by
  unfold u2_kap
  rw [u2_rieszKernelGrad_eq s hz]
  simp

lemma u2_kap_measurable (s : ℝ) (i : Fin d) : Measurable (u2_kap d s i) := by
  unfold u2_kap rieszKernelGrad gradient
  have h1 : Measurable fun z : Euc d => (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ (rieszKernel d s) z) :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp (measurable_fderiv ℝ _)
  exact (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.measurable.comp h1

lemma u2_kap_hom (s : ℝ) (i : Fin d) {t : ℝ} (ht : 0 < t) {z : Euc d} (hz : z ≠ 0) :
    u2_kap d s i (t • z) = t ^ (-(s + 1)) * u2_kap d s i z := by
  have htz : t • z ≠ 0 := smul_ne_zero ht.ne' hz
  rw [u2_kap_eq s i htz, u2_kap_eq s i hz]
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h1 : (‖t • z‖ ^ 2) ^ (-s / 2 - 1) = t ^ (-s - 2) * (‖z‖ ^ 2) ^ (-s / 2 - 1) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_pow, Real.mul_rpow (by positivity)
      (by positivity)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1
    push_cast
    ring
  rw [h1]
  simp only [PiLp.smul_apply, smul_eq_mul]
  have h2 : t ^ (-(s + 1)) = t ^ (-s - 2) * t := by
    rw [show -(s + 1) = (-s - 2) + 1 by ring, Real.rpow_add ht, Real.rpow_one]
  rw [h2]
  ring

lemma u2_kap_contDiffAt (s : ℝ) (i : Fin d) {z : Euc d} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (u2_kap d s i) z := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hn : ContDiffAt ℝ ∞ (fun y : Euc d => ‖y‖) z := contDiffAt_norm ℝ hz
  have h2 : ContDiffAt ℝ ∞ (fun y : Euc d => ‖y‖ ^ 2) z := hn.pow 2
  have h3 : ContDiffAt ℝ ∞ (fun y : Euc d => (‖y‖ ^ 2) ^ (-s / 2 - 1)) z :=
    h2.rpow_const_of_ne (by positivity)
  have h4 : ContDiffAt ℝ ∞ (fun y : Euc d => -(u2_sigma s * (‖y‖ ^ 2) ^ (-s / 2 - 1)) * y i) z := by
    have hp : ContDiff ℝ ∞ (fun y : Euc d => y i) := by
      exact (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff
    exact ((h3.const_smul (u2_sigma s)).neg.mul hp.contDiffAt)
  refine h4.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ne.mem_nhds hz] with y hy
  exact u2_kap_eq s i hy

end HRS.Whole
