import HRS.MS.S111X1E1

/-!
# S11.1 X1 (energy), part 2: the cancellation convention equals the plain convolution
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X1

open HRS HRS.Whole

variable {d : ℕ}

theorem kG_near_integrable (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s + 1 < d) :
    Integrable (Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4)) (rieszKernelGrad d s)) := by
  have hdb := HRS.MH.DualityRd.db1G_integrable (d := d) hd hs1
  have hbd : Integrable (Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4))
      (fun z => kσ s * (HRS.MH.DualityRd.db1G (d := d) (s + 1) z + 1))) := by
    rw [integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
    exact ((hdb.integrableOn.add (integrableOn_const (measure_closedBall_lt_top.ne))).const_mul _)
  refine hbd.mono' ((kG_measurable s).indicator Metric.isClosed_closedBall.measurableSet).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ Metric.closedBall (0 : Euc d) (1 / 4)
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    exact kG_envelope hd hs0 z
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
    simp

theorem kG_near_integral_zero (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) :
    ∫ z, Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4)) (rieszKernelGrad d s) z = 0 := by
  set F := Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4)) (rieszKernelGrad d s) with hF
  have hodd : ∀ z, F (-z) = -F z := by
    intro z
    simp only [hF, Set.indicator, Metric.mem_closedBall, dist_zero_right, norm_neg]
    split_ifs
    · exact HRS.MS.R2Interp.s102_rieszKernelGrad_neg s z
    · simp
  have h1 : ∫ z, F (-z) = ∫ z, F z := integral_neg_eq_self F volume
  simp_rw [hodd] at h1
  rw [integral_neg] at h1
  have h2 : (2 : ℝ) • ∫ z, F z = 0 := by
    rw [two_smul]; nth_rewrite 1 [← h1]; simp
  exact (smul_eq_zero.1 h2).resolve_left (by norm_num)

theorem plain_integrable (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s + 1 < d) {ρ : Euc d → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M)
    {h : Euc d → ℝ} (hhm : Measurable h) {Bh : ℝ} (hh : ∀ y, |h y| ≤ Bh * ρ y) (x : Euc d) :
    Integrable (fun y => h y • rieszKernelGrad d s (x - y)) := by
  have hmeasG : Measurable fun y => rieszKernelGrad d s (x - y) :=
    (kG_measurable s).comp (measurable_const.sub measurable_id)
  refine ((kG_weighted hd hs0 hs1 hρm hρ0 hρi hM x).1.const_mul Bh).mono'
    (hhm.smul hmeasG).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  calc |h y| * ‖rieszKernelGrad d s (x - y)‖ ≤ Bh * ρ y * ‖rieszKernelGrad d s (x - y)‖ :=
        mul_le_mul_of_nonneg_right (hh y) (norm_nonneg _)
    _ = Bh * (ρ y * ‖rieszKernelGrad d s (x - y)‖) := by ring

/-- the cancellation convention is the plain convolution (density bounded by a multiple of `ρ`) -/
theorem conv_eq_plain (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s + 1 < d) {ρ : Euc d → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M)
    {h : Euc d → ℝ} (hhm : Measurable h) {Bh : ℝ} (hh : ∀ y, |h y| ≤ Bh * ρ y) (x : Euc d) :
    convGradConvW (rieszKernelGrad d s) h x = ∫ y, h y • rieszKernelGrad d s (x - y) := by
  have hJ1 := plain_integrable hd hs0 hs1 hρm hρ0 hρi hM hhm hh x
  have hind : Integrable (fun y => Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4)) (rieszKernelGrad d s) (x - y)) :=
    (kG_near_integrable hd hs0 hs1).comp_sub_left x
  have hJ2 : Integrable (fun y => h x • Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4)) (rieszKernelGrad d s) (x - y)) :=
    hind.smul (h x)
  have hsplit : ∀ y, (if ‖x - y‖ ≤ 1 / 4 then (h y - h x) • (rieszKernelGrad d s) (x - y) else h y • (rieszKernelGrad d s) (x - y)) =
      h y • (rieszKernelGrad d s) (x - y) - h x • Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4)) (rieszKernelGrad d s) (x - y) := by
    intro y
    by_cases hy : ‖x - y‖ ≤ 1 / 4
    · rw [if_pos hy, Set.indicator_of_mem (by simpa using hy), sub_smul]
    · rw [if_neg hy, Set.indicator_of_notMem (by simpa using hy)]
      simp
  unfold convGradConvW
  simp_rw [hsplit]
  rw [integral_sub hJ1 hJ2, integral_smul, integral_sub_left_eq_self
    (Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4)) (rieszKernelGrad d s)) volume x, kG_near_integral_zero hd hs0]
  simp

end HRS.MS.S111X1
