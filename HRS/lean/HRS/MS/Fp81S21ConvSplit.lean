import HRS.MS.S111X1E2
import HRS.MH.ScreenedA1

/-!
# HRS S2.1(iii): generic singular-force convolution split

The pointwise plain-convolution conversion is stated with the integrability of the raw
kernel product at the point in question.  An `L¹ ∩ L²` assumption on the input alone does not
give that integrability for every allowed `s` (the local kernel need not be in `L²`).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators

set_option maxHeartbeats 400000

namespace HRS.Fp81.S21

open HRS HRS.Whole

variable {d : ℕ}

/-- The norm of the force kernel restricted to the cancellation ball. -/
def fp81s21_localKernel (s : ℝ) (z : Euc d) : ℝ :=
  if ‖z‖ ≤ 1 / 4 then ‖rieszKernelGrad d s z‖ else 0

/-- The force kernel restricted to the complement of the cancellation ball. -/
def fp81s21_farKernel (s : ℝ) (z : Euc d) : ℝ :=
  if 1 / 4 < ‖z‖ then ‖rieszKernelGrad d s z‖ else 0

/-- The local part of the convolution, using the cancellation radius `1/4`. -/
def fp81s21_localConv (s : ℝ) (g : Euc d → ℝ) (x : Euc d) : Euc d :=
  ∫ y, (if ‖x - y‖ ≤ 1 / 4 then g y • rieszKernelGrad d s (x - y) else 0)

/-- The far part of the convolution, using the cancellation radius `1/4`. -/
def fp81s21_farConv (s : ℝ) (g : Euc d → ℝ) (x : Euc d) : Euc d :=
  ∫ y, (if 1 / 4 < ‖x - y‖ then g y • rieszKernelGrad d s (x - y) else 0)

private lemma fp81s21_far_power_bound {s : ℝ} (hs0 : 0 ≤ s) {z : Euc d}
    (hz : 1 / 4 < ‖z‖) : ‖z‖ ^ (-(s + 1)) ≤ 4 ^ (s + 1) := by
  have hquarter : ((1 / 4 : ℝ)) ^ (-(s + 1)) = 4 ^ (s + 1) := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_neg]
  rw [← hquarter]
  exact Real.rpow_le_rpow_of_nonpos (by norm_num) hz.le (by linarith)

/-- Kernel facts needed for the local/far split.  The pointwise singular estimate is exact up to
`movtr_sigma s`; the far bound is uniform outside the fixed radius and includes `s = 0`. -/
theorem fp81s21_kernel_facts (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s + 1 < d) :
    Function.Odd (rieszKernelGrad d s) ∧
    (∀ z, ‖rieszKernelGrad d s z‖ ≤ movtr_sigma s * ‖z‖ ^ (-(s + 1))) ∧
    Integrable (fun z => fp81s21_localKernel (d := d) s z) ∧
    (∫ z in Metric.closedBall (0 : Euc d) (1 / 4), rieszKernelGrad d s z) = 0 ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ z, 1 / 4 < ‖z‖ → ‖rieszKernelGrad d s z‖ ≤ C) := by
  have hd' : 1 ≤ d := by omega
  have hodd : Function.Odd (rieszKernelGrad d s) :=
    fun z => HRS.MS.R2Interp.s102_rieszKernelGrad_neg s z
  have hnorm : ∀ z, ‖rieszKernelGrad d s z‖ ≤ movtr_sigma s * ‖z‖ ^ (-(s + 1)) := by
    intro z
    by_cases hz : z = 0
    · subst z
      have hg0 := HRS.MP.SelfSimP2.ssp2_riesz_grad_zero hd' s hs0
      rw [hg0, norm_zero]
      have hσ : 0 ≤ movtr_sigma s := by
        unfold movtr_sigma
        split_ifs <;> linarith
      exact mul_nonneg hσ (Real.rpow_nonneg (by norm_num) _)
    · rw [HRS.Whole.movtr_rieszKernelGrad_norm s hs0 hz]
      have hexp : -s - 1 = -(s + 1) := by ring
      rw [hexp]
  have hGI : Integrable (Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4))
      (rieszKernelGrad d s)) := HRS.MS.S111X1.kG_near_integrable hd' hs0 hs1
  have hlocal : Integrable (fun z => fp81s21_localKernel (d := d) s z) := by
    refine (hGI.norm).congr (Filter.Eventually.of_forall fun z => ?_)
    change ‖Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4))
      (rieszKernelGrad d s) z‖ =
      (if ‖z‖ ≤ 1 / 4 then ‖rieszKernelGrad d s z‖ else 0)
    by_cases hz : ‖z‖ ≤ 1 / 4
    · have hm : z ∈ Metric.closedBall (0 : Euc d) (1 / 4) := mem_closedBall_zero_iff.mpr hz
      rw [Set.indicator_of_mem hm, if_pos hz]
    · have hm : z ∉ Metric.closedBall (0 : Euc d) (1 / 4) := by
        intro hh
        exact hz (mem_closedBall_zero_iff.mp hh)
      rw [Set.indicator_of_notMem hm, if_neg hz]
      simp
  have hzeroI : (∫ z, Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4))
      (rieszKernelGrad d s) z) = 0 := HRS.MS.S111X1.kG_near_integral_zero hd' hs0
  have hzero : (∫ z in Metric.closedBall (0 : Euc d) (1 / 4),
      rieszKernelGrad d s z) = 0 := by
    rw [← integral_indicator Metric.isClosed_closedBall.measurableSet]
    exact hzeroI
  have hdb : ∀ z, 1 / 4 < ‖z‖ →
      HRS.MH.DualityRd.db1G (d := d) (s + 1) z ≤ 4 ^ (s + 1) := by
    intro z hz
    unfold HRS.MH.DualityRd.db1G
    by_cases hball : z ∈ Metric.ball (0 : Euc d) 1
    · rw [Set.indicator_of_mem hball]
      have hz' : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hball
      have hp := fp81s21_far_power_bound hs0 hz
      simpa [hz', show -(s + 1) = -s - 1 by ring] using hp
    · rw [Set.indicator_of_notMem hball]
      positivity
  have hC0 : 0 ≤ HRS.MS.S111X1.kσ s * (4 ^ (s + 1) + 1) := by
    exact mul_nonneg (HRS.MS.S111X1.kσ_nonneg s) (by positivity)
  have hfar : ∀ z, 1 / 4 < ‖z‖ →
      ‖rieszKernelGrad d s z‖ ≤ HRS.MS.S111X1.kσ s * (4 ^ (s + 1) + 1) := by
    intro z hz
    calc ‖rieszKernelGrad d s z‖
        ≤ HRS.MS.S111X1.kσ s *
          (HRS.MH.DualityRd.db1G (d := d) (s + 1) z + 1) :=
          HRS.MS.S111X1.kG_envelope hd' hs0 z
      _ ≤ HRS.MS.S111X1.kσ s * (4 ^ (s + 1) + 1) := by
          have hsum : HRS.MH.DualityRd.db1G (d := d) (s + 1) z + 1 ≤
              4 ^ (s + 1) + 1 := by
            nlinarith [hdb z hz]
          exact mul_le_mul_of_nonneg_left hsum (HRS.MS.S111X1.kσ_nonneg s)
  exact ⟨hodd, hnorm, hlocal, hzero,
    ⟨HRS.MS.S111X1.kσ s * (4 ^ (s + 1) + 1), hC0, hfar⟩⟩

/-- Convert the cancellation convention into local and far plain convolutions.  Besides `L¹`
and `L²`, pointwise conversion requires integrability of the raw kernel product at `x`.
This premise holds for the smooth, decaying inputs used by the S2.1(iii) force application. -/
theorem fp81s21_conv_split (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s + 1 < d)
    (g : Euc d → ℝ) (hg1 : Integrable g) (hg2 : MemLp g 2 volume) (x : Euc d)
    (hraw : Integrable (fun y => g y • rieszKernelGrad d s (x - y))) :
    convGradConvW (rieszKernelGrad d s) g x =
      (∫ y, (if ‖x - y‖ ≤ 1 / 4 then g y • rieszKernelGrad d s (x - y) else 0)) +
      ∫ y, (if 1 / 4 < ‖x - y‖ then g y • rieszKernelGrad d s (x - y) else 0) := by
  have hd' : 1 ≤ d := by omega
  have hG := HRS.MS.S111X1.kG_near_integrable (d := d) hd' hs0 hs1
  have hGS : Integrable (fun y => (Set.indicator
      (Metric.closedBall (0 : Euc d) (1 / 4)) (rieszKernelGrad d s)) (x - y)) :=
    hG.comp_sub_left x
  have hsub : Integrable (fun y => g x •
      (Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4)) (rieszKernelGrad d s)) (x - y)) :=
    hGS.smul (g x)
  have hconv : Integrable (fun y =>
      if ‖x - y‖ ≤ 1 / 4 then (g y - g x) • rieszKernelGrad d s (x - y)
      else g y • rieszKernelGrad d s (x - y)) := by
    refine (hraw.sub hsub).congr (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : ‖x - y‖ ≤ 1 / 4
    · have hm : x - y ∈ Metric.closedBall (0 : Euc d) (1 / 4) :=
        mem_closedBall_zero_iff.mpr hy
      change g y • rieszKernelGrad d s (x - y) - g x •
        (Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4))
          (rieszKernelGrad d s)) (x - y) =
        (if ‖x - y‖ ≤ 1 / 4 then (g y - g x) • rieszKernelGrad d s (x - y)
          else g y • rieszKernelGrad d s (x - y))
      rw [Set.indicator_of_mem hm, if_pos hy, sub_smul]
    · have hm : x - y ∉ Metric.closedBall (0 : Euc d) (1 / 4) := by
        intro hh
        exact hy (mem_closedBall_zero_iff.mp hh)
      change g y • rieszKernelGrad d s (x - y) - g x •
        (Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4))
          (rieszKernelGrad d s)) (x - y) =
        (if ‖x - y‖ ≤ 1 / 4 then (g y - g x) • rieszKernelGrad d s (x - y)
          else g y • rieszKernelGrad d s (x - y))
      rw [Set.indicator_of_notMem hm, if_neg hy]
      simp
  have hnear : Integrable (fun y =>
      if ‖x - y‖ ≤ 1 / 4 then g y • rieszKernelGrad d s (x - y) else 0) := by
    let S : Set (Euc d) := {y | ‖x - y‖ ≤ 1 / 4}
    have hmnorm : Measurable (fun y : Euc d => ‖x - y‖) :=
      measurable_norm.comp (measurable_const.sub measurable_id)
    have hSm : MeasurableSet S := by
      exact measurableSet_le hmnorm measurable_const
    have hI := (integrable_indicator_iff hSm).2 hraw.integrableOn
    refine hI.congr (Filter.Eventually.of_forall fun y => ?_)
    change S.indicator (fun z => g z • rieszKernelGrad d s (x - z)) y = _
    simp [S, Set.indicator]
  have hfar : Integrable (fun y =>
      if 1 / 4 < ‖x - y‖ then g y • rieszKernelGrad d s (x - y) else 0) := by
    let S : Set (Euc d) := {y | 1 / 4 < ‖x - y‖}
    have hmnorm : Measurable (fun y : Euc d => ‖x - y‖) :=
      measurable_norm.comp (measurable_const.sub measurable_id)
    have hSm : MeasurableSet S := by
      exact measurableSet_lt measurable_const hmnorm
    have hI := (integrable_indicator_iff hSm).2 hraw.integrableOn
    refine hI.congr (Filter.Eventually.of_forall fun y => ?_)
    change S.indicator (fun z => g z • rieszKernelGrad d s (x - z)) y = _
    simp [S, Set.indicator]
  have hsplit : ∀ y, g y • rieszKernelGrad d s (x - y) =
      (if ‖x - y‖ ≤ 1 / 4 then g y • rieszKernelGrad d s (x - y) else 0) +
      (if 1 / 4 < ‖x - y‖ then g y • rieszKernelGrad d s (x - y) else 0) := by
    intro y
    by_cases hy : ‖x - y‖ ≤ 1 / 4
    · have hfar : ¬ 1 / 4 < ‖x - y‖ := not_lt.mpr hy
      simpa only [if_pos hy, if_neg hfar, add_zero]
    · have hy' : 1 / 4 < ‖x - y‖ := lt_of_not_ge hy
      have hnear : ¬ ‖x - y‖ ≤ 1 / 4 := not_le.mpr hy'
      simpa only [if_neg hnear, if_pos hy', zero_add]
  have hcancel : ∫ y, g x •
      (Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4)) (rieszKernelGrad d s)) (x - y) = 0 := by
    rw [integral_smul, integral_sub_left_eq_self
      (Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4)) (rieszKernelGrad d s)) volume x,
      HRS.MS.S111X1.kG_near_integral_zero hd' hs0]
    simp
  have hconv_eq : convGradConvW (rieszKernelGrad d s) g x =
      (∫ y, g y • rieszKernelGrad d s (x - y)) -
        ∫ y, g x • (Set.indicator
          (Metric.closedBall (0 : Euc d) (1 / 4)) (rieszKernelGrad d s)) (x - y) := by
    unfold convGradConvW
    have hpt : ∀ y, (if ‖x - y‖ ≤ 1 / 4 then
        (g y - g x) • rieszKernelGrad d s (x - y) else
        g y • rieszKernelGrad d s (x - y)) =
        g y • rieszKernelGrad d s (x - y) - g x •
          (Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4))
            (rieszKernelGrad d s)) (x - y) := by
      intro y
      by_cases hy : ‖x - y‖ ≤ 1 / 4
      · have hm : x - y ∈ Metric.closedBall (0 : Euc d) (1 / 4) :=
          mem_closedBall_zero_iff.mpr hy
        rw [Set.indicator_of_mem hm, if_pos hy, sub_smul]
      · have hm : x - y ∉ Metric.closedBall (0 : Euc d) (1 / 4) := by
          intro hh
          exact hy (mem_closedBall_zero_iff.mp hh)
        rw [Set.indicator_of_notMem hm, if_neg hy]
        simp
    simp_rw [hpt]
    exact integral_sub hraw hsub
  have hrawSplit : (∫ y, g y • rieszKernelGrad d s (x - y)) =
      (∫ y, (if ‖x - y‖ ≤ 1 / 4 then g y • rieszKernelGrad d s (x - y) else 0)) +
      ∫ y, (if 1 / 4 < ‖x - y‖ then g y • rieszKernelGrad d s (x - y) else 0) := by
    calc ∫ y, g y • rieszKernelGrad d s (x - y)
        = ∫ y, ((if ‖x - y‖ ≤ 1 / 4 then g y • rieszKernelGrad d s (x - y) else 0) +
          (if 1 / 4 < ‖x - y‖ then g y • rieszKernelGrad d s (x - y) else 0)) := by
            exact integral_congr_ae (Filter.Eventually.of_forall fun y => hsplit y)
      _ = _ := integral_add hnear hfar
  rw [hconv_eq, hcancel, sub_zero, hrawSplit]

/-- Uniform far-field estimate.  This is the pointwise `L¹ → L∞` half of the split bound. -/
theorem fp81s21_farConv_bound (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s + 1 < d)
    : ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : Euc d → ℝ), Integrable g → Measurable g → ∀ x,
      ‖fp81s21_farConv (d := d) s g x‖ ≤ C * ∫ y, ‖g y‖ := by
  have hfacts := fp81s21_kernel_facts (d := d) hd hs0 hs1
  rcases hfacts.2.2.2.2 with ⟨C, hC, hfar⟩
  refine ⟨C, hC, fun g hg1 hgm x => ?_⟩
  have hGm : Measurable (rieszKernelGrad d s) := HRS.MS.S111X1.kG_measurable s
  have hmajor : Integrable (fun y => C * ‖g y‖) := hg1.norm.const_mul C
  have hset : MeasurableSet {y : Euc d | 1 / 4 < ‖x - y‖} :=
    measurableSet_lt measurable_const (measurable_norm.comp (measurable_const.sub measurable_id))
  have hmeas : Measurable (fun y : Euc d =>
      if 1 / 4 < ‖x - y‖ then g y • rieszKernelGrad d s (x - y) else 0) :=
    Measurable.ite hset (hgm.smul (hGm.comp (measurable_const.sub measurable_id))) measurable_const
  have hI : Integrable (fun y =>
      if 1 / 4 < ‖x - y‖ then g y • rieszKernelGrad d s (x - y) else 0) := by
    refine hmajor.mono' hmeas.aestronglyMeasurable ?_
    · filter_upwards with y
      by_cases hy : 1 / 4 < ‖x - y‖
      · rw [if_pos hy, norm_smul, Real.norm_eq_abs]
        calc |g y| * ‖rieszKernelGrad d s (x - y)‖
            ≤ |g y| * C := mul_le_mul_of_nonneg_left (hfar (x - y) hy) (abs_nonneg _)
          _ = C * ‖g y‖ := by rw [Real.norm_eq_abs]; ring
      · rw [if_neg hy, norm_zero]
        exact mul_nonneg hC (abs_nonneg (g y))
  have hnorm := norm_integral_le_integral_norm
    (μ := (volume : Measure (Euc d)))
    (fun y => if 1 / 4 < ‖x - y‖ then g y • rieszKernelGrad d s (x - y) else 0)
  have hInorm : Integrable (fun y => ‖if 1 / 4 < ‖x - y‖ then
      g y • rieszKernelGrad d s (x - y) else 0‖) := hI.norm
  calc ‖fp81s21_farConv (d := d) s g x‖
      = ‖∫ y, (if 1 / 4 < ‖x - y‖ then g y • rieszKernelGrad d s (x - y) else 0)‖ := rfl
    _ ≤ ∫ y, ‖if 1 / 4 < ‖x - y‖ then g y • rieszKernelGrad d s (x - y) else 0‖ := hnorm
    _ ≤ ∫ y, C * ‖g y‖ := by
      refine integral_mono hInorm hmajor ?_
      intro y
      change ‖if 1 / 4 < ‖x - y‖ then g y • rieszKernelGrad d s (x - y) else 0‖ ≤
        C * ‖g y‖
      by_cases hy : 1 / 4 < ‖x - y‖
      · rw [if_pos hy, norm_smul, Real.norm_eq_abs]
        calc |g y| * ‖rieszKernelGrad d s (x - y)‖ ≤ |g y| * C :=
                mul_le_mul_of_nonneg_left (hfar (x - y) hy) (abs_nonneg _)
          _ = C * ‖g y‖ := by
                rw [Real.norm_eq_abs]
                ring
      · rw [if_neg hy, norm_zero]
        exact mul_nonneg hC (norm_nonneg (g y))
    _ = C * ∫ y, ‖g y‖ := by
      rw [integral_const_mul]

/-- Measurability of the local vector convolution in the split. -/
theorem fp81s21_localConv_measurable {s : ℝ} (g : Euc d → ℝ) (hgm : Measurable g) :
    Measurable (fp81s21_localConv (d := d) s g) := by
  have hdiff : Measurable (fun p : Euc d × Euc d => p.1 - p.2) :=
    measurable_fst.sub measurable_snd
  have hnear : MeasurableSet {p : Euc d × Euc d | ‖p.1 - p.2‖ ≤ 1 / 4} :=
    measurableSet_le (measurable_norm.comp hdiff) measurable_const
  have hGm : Measurable (rieszKernelGrad d s) := HRS.MS.S111X1.kG_measurable s
  have hF : Measurable (fun p : Euc d × Euc d =>
      if ‖p.1 - p.2‖ ≤ 1 / 4 then g p.2 • rieszKernelGrad d s (p.1 - p.2) else 0) :=
    Measurable.ite hnear
      ((hgm.comp measurable_snd).smul (hGm.comp hdiff)) measurable_const
  have hFs : StronglyMeasurable (fun p : Euc d × Euc d =>
      if ‖p.1 - p.2‖ ≤ 1 / 4 then g p.2 • rieszKernelGrad d s (p.1 - p.2) else 0) :=
    hF.stronglyMeasurable
  have hI : Measurable (fun x : Euc d =>
      ∫ y, (if ‖x - y‖ ≤ 1 / 4 then g y • rieszKernelGrad d s (x - y) else 0)) :=
    (hFs.integral_prod_right' (ν := (volume : Measure (Euc d)))).measurable
  change Measurable (fun x : Euc d =>
      ∫ y, (if ‖x - y‖ ≤ 1 / 4 then g y • rieszKernelGrad d s (x - y) else 0))
  exact hI

#print axioms fp81s21_kernel_facts
#print axioms fp81s21_conv_split
#print axioms fp81s21_farConv_bound
#print axioms fp81s21_localConv_measurable

end HRS.Fp81.S21
