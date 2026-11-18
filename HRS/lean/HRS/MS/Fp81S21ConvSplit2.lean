import HRS.MS.Fp81S21ConvSplit
import HRS.MS.SA16Y3Yg1

/-!
# HRS S2.1(iii): bounded-input convolution split

For bounded inputs the raw kernel product is integrable at every spatial point,
so the cancellation split is pointwise without an extra raw-integrability premise.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators

set_option maxHeartbeats 400000

namespace HRS.Fp81.S21

open HRS HRS.Whole

variable {d : ℕ}

private theorem fp81s21_raw_integrable_of_bounded
    (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s + 1 < d)
    (g : Euc d → ℝ) (hgm : Measurable g) (hg1 : Integrable g)
    (hbound : ∃ M : ℝ, ∀ y, ‖g y‖ ≤ M) (x : Euc d) :
    Integrable (fun y => g y • rieszKernelGrad d s (x - y)) := by
  obtain ⟨M, hM⟩ := hbound
  have hM0 : 0 ≤ M := (norm_nonneg (g 0)).trans (hM 0)
  have hfacts := fp81s21_kernel_facts (d := d) hd hs0 hs1
  have hlocalK : Integrable (fun z : Euc d => fp81s21_localKernel (d := d) s z) :=
    hfacts.2.2.1
  have hlocalKx : Integrable (fun y : Euc d =>
      fp81s21_localKernel (d := d) s (x - y)) := hlocalK.comp_sub_left x
  have hnearMajor : Integrable (fun y : Euc d =>
      M * fp81s21_localKernel (d := d) s (x - y)) := hlocalKx.const_mul M
  have hGm : Measurable (rieszKernelGrad d s) := HRS.MS.S111X1.kG_measurable s
  have hnearSet : MeasurableSet {y : Euc d | ‖x - y‖ ≤ 1 / 4} :=
    measurableSet_le
      (measurable_norm.comp (measurable_const.sub measurable_id)) measurable_const
  have hnearMeas : Measurable (fun y : Euc d =>
      if ‖x - y‖ ≤ 1 / 4 then g y • rieszKernelGrad d s (x - y) else 0) :=
    Measurable.ite hnearSet
      (hgm.smul (hGm.comp (measurable_const.sub measurable_id))) measurable_const
  have hnear : Integrable (fun y : Euc d =>
      if ‖x - y‖ ≤ 1 / 4 then g y • rieszKernelGrad d s (x - y) else 0) := by
    refine hnearMajor.mono' hnearMeas.aestronglyMeasurable ?_
    filter_upwards with y
    by_cases hy : ‖x - y‖ ≤ 1 / 4
    · rw [if_pos hy, norm_smul, Real.norm_eq_abs]
      change |g y| * ‖rieszKernelGrad d s (x - y)‖ ≤
        M * (if ‖x - y‖ ≤ 1 / 4 then ‖rieszKernelGrad d s (x - y)‖ else 0)
      rw [if_pos hy]
      exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hM y)
        (norm_nonneg (rieszKernelGrad d s (x - y)))
    · rw [if_neg hy, norm_zero]
      change 0 ≤ M * (if ‖x - y‖ ≤ 1 / 4 then ‖rieszKernelGrad d s (x - y)‖ else 0)
      rw [if_neg hy]
      simp
  rcases hfacts.2.2.2.2 with ⟨C, hC, hfarK⟩
  have hfarMajor : Integrable (fun y : Euc d => C * ‖g y‖) := hg1.norm.const_mul C
  have hfarSet : MeasurableSet {y : Euc d | 1 / 4 < ‖x - y‖} :=
    measurableSet_lt measurable_const
      (measurable_norm.comp (measurable_const.sub measurable_id))
  have hfarMeas : Measurable (fun y : Euc d =>
      if 1 / 4 < ‖x - y‖ then g y • rieszKernelGrad d s (x - y) else 0) :=
    Measurable.ite hfarSet
      (hgm.smul (hGm.comp (measurable_const.sub measurable_id))) measurable_const
  have hfar : Integrable (fun y : Euc d =>
      if 1 / 4 < ‖x - y‖ then g y • rieszKernelGrad d s (x - y) else 0) := by
    refine hfarMajor.mono' hfarMeas.aestronglyMeasurable ?_
    filter_upwards with y
    by_cases hy : 1 / 4 < ‖x - y‖
    · rw [if_pos hy, norm_smul, Real.norm_eq_abs]
      calc |g y| * ‖rieszKernelGrad d s (x - y)‖
          ≤ |g y| * C := mul_le_mul_of_nonneg_left (hfarK (x - y) hy) (abs_nonneg _)
        _ = C * ‖g y‖ := by rw [Real.norm_eq_abs]; ring
    · rw [if_neg hy, norm_zero]
      exact mul_nonneg hC (norm_nonneg _)
  have hsplit : ∀ y : Euc d,
      g y • rieszKernelGrad d s (x - y) =
        (if ‖x - y‖ ≤ 1 / 4 then g y • rieszKernelGrad d s (x - y) else 0) +
        (if 1 / 4 < ‖x - y‖ then g y • rieszKernelGrad d s (x - y) else 0) := by
    intro y
    by_cases hy : ‖x - y‖ ≤ 1 / 4
    · have hfar' : ¬ (1 / 4 : ℝ) < ‖x - y‖ := not_lt.mpr hy
      rw [if_pos hy, if_neg hfar', add_zero]
    · have hy' : 1 / 4 < ‖x - y‖ := lt_of_not_ge hy
      rw [if_neg hy, if_pos hy', zero_add]
  have hsum : Integrable (fun y : Euc d =>
      (if ‖x - y‖ ≤ 1 / 4 then g y • rieszKernelGrad d s (x - y) else 0) +
      (if 1 / 4 < ‖x - y‖ then g y • rieszKernelGrad d s (x - y) else 0)) :=
    hnear.add hfar
  refine hsum.congr (Filter.Eventually.of_forall fun y => ?_)
  exact (hsplit y).symm

/-- For measurable bounded integrable data, the cancellation convolution is the
pointwise sum of its local and far pieces. Boundedness supplies `MemLp 2` as well. -/
theorem fp81s21_conv_split_bdd
    (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s + 1 < d)
    (g : Euc d → ℝ) (hgm : Measurable g) (hg1 : Integrable g)
    (hbound : ∃ M : ℝ, ∀ y, ‖g y‖ ≤ M) :
    ∀ x, convGradConvW (rieszKernelGrad d s) g x =
      fp81s21_localConv (d := d) s g x + fp81s21_farConv (d := d) s g x := by
  have hg2 : MemLp g 2 (volume : Measure (Euc d)) := by
    obtain ⟨M, hM⟩ := hbound
    have hM0 : 0 ≤ M := (norm_nonneg (g 0)).trans (hM 0)
    have hmajor : Integrable (fun y : Euc d => M * ‖g y‖) := hg1.norm.const_mul M
    have hsq : Integrable (fun y : Euc d => g y ^ 2) := by
      refine hmajor.mono' (hgm.pow_const 2).aestronglyMeasurable ?_
      filter_upwards with y
      have hgy : |g y| ≤ M := by simpa [Real.norm_eq_abs] using hM y
      have hprod := mul_le_mul_of_nonneg_right hgy (abs_nonneg (g y))
      rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
      nlinarith [sq_abs (g y), hprod]
    exact (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).2 hsq
  intro x
  have hraw := fp81s21_raw_integrable_of_bounded
    (d := d) hd hs0 hs1 g hgm hg1 hbound x
  simpa [fp81s21_localConv, fp81s21_farConv] using
    (fp81s21_conv_split (d := d) hd hs0 hs1 g hg1 hg2 x hraw)

/-- The local convolution is bounded on `L²` by the `L¹` norm of the local
kernel. The constant depends only on the dimension and the kernel parameter. -/
theorem fp81s21_localConv_L2
    (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s + 1 < d) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧
      ∀ (g : Euc d → ℝ), Measurable g →
        (∃ M : ℝ, ∀ y, ‖g y‖ ≤ M) → MemLp g 2 (volume : Measure (Euc d)) →
        eLpNorm (fp81s21_localConv (d := d) s g) 2 (volume : Measure (Euc d)) ≤
          ENNReal.ofReal C₁ * eLpNorm g 2 (volume : Measure (Euc d)) := by
  let k : Euc d → ℝ := fp81s21_localKernel (d := d) s
  let K : Euc d → Euc d := fun z =>
    Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4))
      (rieszKernelGrad d s) z
  have hfacts := fp81s21_kernel_facts (d := d) hd hs0 hs1
  have hkI : Integrable k := by
    simpa [k] using hfacts.2.2.1
  have hk0 : ∀ z, 0 ≤ k z := by
    intro z
    unfold k fp81s21_localKernel
    split_ifs <;> positivity
  have hkSet : MeasurableSet {z : Euc d | ‖z‖ ≤ 1 / 4} :=
    measurableSet_le measurable_norm measurable_const
  have hGm : Measurable (rieszKernelGrad d s) := HRS.MS.S111X1.kG_measurable s
  have hkm : Measurable k := by
    dsimp [k, fp81s21_localKernel]
    exact Measurable.ite hkSet (measurable_norm.comp hGm) measurable_const
  have hKm : Measurable K := by
    dsimp [K]
    exact hGm.indicator Metric.isClosed_closedBall.measurableSet
  have hKnorm : ∀ z, ‖K z‖ = k z := by
    intro z
    by_cases hz : z ∈ Metric.closedBall (0 : Euc d) (1 / 4)
    · have hz' : ‖z‖ ≤ 1 / 4 := mem_closedBall_zero_iff.mp hz
      change ‖Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4))
        (rieszKernelGrad d s) z‖ =
        (if ‖z‖ ≤ 1 / 4 then ‖rieszKernelGrad d s z‖ else 0)
      rw [Set.indicator_of_mem hz, if_pos hz']
    · have hz' : ¬ ‖z‖ ≤ 1 / 4 := fun hh => hz (mem_closedBall_zero_iff.mpr hh)
      change ‖Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4))
        (rieszKernelGrad d s) z‖ =
        (if ‖z‖ ≤ 1 / 4 then ‖rieszKernelGrad d s z‖ else 0)
      rw [Set.indicator_of_notMem hz, norm_zero, if_neg hz']
  let C₁ : ℝ := ∫ z, k z
  have hC₁ : 0 ≤ C₁ := by
    dsimp [C₁]
    exact integral_nonneg (fun z => hk0 z)
  have hlin : ∫⁻ z, ‖k z‖ₑ = ENNReal.ofReal C₁ := by
    calc
      ∫⁻ z, ‖k z‖ₑ = ∫⁻ z, ENNReal.ofReal (k z) := by
        refine lintegral_congr_ae ?_
        exact Filter.Eventually.of_forall fun z => by
          change ‖k z‖ₑ = ENNReal.ofReal (k z)
          rw [Real.enorm_eq_ofReal (hk0 z)]
      _ = ENNReal.ofReal (∫ z, k z) :=
        (ofReal_integral_eq_lintegral_ofReal hkI
          (Filter.Eventually.of_forall fun z => hk0 z)).symm
      _ = ENNReal.ofReal C₁ := by simp [C₁]
  refine ⟨C₁, hC₁, fun g hgm hbound hg2 => ?_⟩
  obtain ⟨M, hM⟩ := hbound
  have hM0 : 0 ≤ M := (norm_nonneg (g 0)).trans (hM 0)
  have hmajor : Integrable (fun z : Euc d => M * k z) := hkI.const_mul M
  have hHmeas : Measurable (fun x : Euc d =>
      ∫ z, k z * |g (x - z)|) := by
    have hprod : Measurable (fun p : Euc d × Euc d =>
        k p.2 * |g (p.1 - p.2)|) :=
      (hkm.comp measurable_snd).mul ((hgm.comp (measurable_fst.sub measurable_snd)).abs)
    exact (hprod.stronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure (Euc d)))).measurable
  let H : Euc d → ℝ := fun x => ∫ z, k z * |g (x - z)|
  have hH0 : ∀ x, 0 ≤ H x := by
    intro x
    exact integral_nonneg fun z => mul_nonneg (hk0 z) (abs_nonneg _)
  have hpt : ∀ x, ‖fp81s21_localConv (d := d) s g x‖ ≤ H x := by
    intro x
    have hFmeas : Measurable (fun z : Euc d => g (x - z) • K z) :=
      (hgm.comp (measurable_const.sub measurable_id)).smul hKm
    have hFI : Integrable (fun z : Euc d => g (x - z) • K z) := by
      refine hmajor.mono' hFmeas.aestronglyMeasurable ?_
      filter_upwards with z
      rw [norm_smul, Real.norm_eq_abs]
      calc |g (x - z)| * ‖K z‖
          ≤ M * ‖K z‖ :=
            mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hM (x - z))
              (norm_nonneg (K z))
        _ = M * k z := by rw [hKnorm z]
    have hRmeas : Measurable (fun z : Euc d => k z * |g (x - z)|) :=
      hkm.mul ((hgm.comp (measurable_const.sub measurable_id)).abs)
    have hRI : Integrable (fun z : Euc d => k z * |g (x - z)|) := by
      refine hmajor.mono' hRmeas.aestronglyMeasurable ?_
      filter_upwards with z
      rw [Real.norm_of_nonneg (mul_nonneg (hk0 z) (abs_nonneg _))]
      calc k z * |g (x - z)| ≤ k z * M :=
            mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hM (x - z)) (hk0 z)
        _ = M * k z := by ring
    have hlocEq : fp81s21_localConv (d := d) s g x =
        ∫ z, g (x - z) • K z := by
      unfold fp81s21_localConv
      calc
        (∫ y, (if ‖x - y‖ ≤ 1 / 4 then
            g y • rieszKernelGrad d s (x - y) else 0)) =
            ∫ y, g y • K (x - y) := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
              by_cases hy : ‖x - y‖ ≤ 1 / 4
              · change (if ‖x - y‖ ≤ 1 / 4 then
                  g y • rieszKernelGrad d s (x - y) else 0) =
                  g y • Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4))
                    (rieszKernelGrad d s) (x - y)
                rw [if_pos hy, Set.indicator_of_mem (mem_closedBall_zero_iff.mpr hy)]
              · have hnot : x - y ∉ Metric.closedBall (0 : Euc d) (1 / 4) :=
                  fun hh => hy (mem_closedBall_zero_iff.mp hh)
                change (if ‖x - y‖ ≤ 1 / 4 then
                  g y • rieszKernelGrad d s (x - y) else 0) =
                  g y • Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4))
                    (rieszKernelGrad d s) (x - y)
                rw [if_neg hy, Set.indicator_of_notMem hnot]
                simp
        _ = ∫ y, (fun z : Euc d => g (x - z) • K z) (x - y) := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
              simp [sub_sub_cancel]
        _ = ∫ z, g (x - z) • K z :=
              integral_sub_left_eq_self (fun z : Euc d => g (x - z) • K z)
                (volume : Measure (Euc d)) x
    have hnorm := norm_integral_le_integral_norm
      (μ := (volume : Measure (Euc d))) (fun z : Euc d => g (x - z) • K z)
    calc
      ‖fp81s21_localConv (d := d) s g x‖ =
          ‖∫ z, g (x - z) • K z‖ := by rw [hlocEq]
      _ ≤ ∫ z, ‖g (x - z) • K z‖ := hnorm
      _ ≤ ∫ z, k z * |g (x - z)| :=
          integral_mono hFI.norm hRI (fun z => by
            rw [norm_smul, Real.norm_eq_abs, hKnorm z]
            exact le_of_eq (by ring))
      _ = H x := rfl
  have hHYoung := HRS.Whole.AppendixA.Phase2SA16R.sa16y3_young_eLp
    (d := d) (p := 2) (by norm_num : 1 ≤ (2 : ℝ)) k (fun y => |g y|) hkm
      (hgm.abs)
  have hHYoung' : eLpNorm H 2 (volume : Measure (Euc d)) ≤
      (∫⁻ z, ‖k z‖ₑ) *
        eLpNorm (fun y : Euc d => |g y|) 2 (volume : Measure (Euc d)) := by
    simpa [H] using hHYoung
  have hAbsEq : (fun y : Euc d => |g y|) = fun y => ‖g y‖ := by
    funext y
    exact (Real.norm_eq_abs _).symm
  rw [hlin, hAbsEq, eLpNorm_norm _ hg2.aestronglyMeasurable] at hHYoung'
  have hAm : Measurable (fp81s21_localConv (d := d) s g) :=
    fp81s21_localConv_measurable (d := d) (s := s) g hgm
  have hmono : eLpNorm (fun x => ‖fp81s21_localConv (d := d) s g x‖) 2
      (volume : Measure (Euc d)) ≤ eLpNorm H 2 (volume : Measure (Euc d)) :=
    eLpNorm_mono_ae_real hAm.norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
          abs_of_nonneg (hH0 x)] using hpt x)
  have hnormEq : eLpNorm (fun x => ‖fp81s21_localConv (d := d) s g x‖) 2
      (volume : Measure (Euc d)) = eLpNorm (fp81s21_localConv (d := d) s g) 2
        (volume : Measure (Euc d)) := by
    rw [eLpNorm_norm _ hAm.aestronglyMeasurable]
  calc
    eLpNorm (fp81s21_localConv (d := d) s g) 2 (volume : Measure (Euc d)) =
        eLpNorm (fun x => ‖fp81s21_localConv (d := d) s g x‖) 2
          (volume : Measure (Euc d)) := hnormEq.symm
    _ ≤ eLpNorm H 2 (volume : Measure (Euc d)) := hmono
    _ ≤ ENNReal.ofReal C₁ * eLpNorm g 2 (volume : Measure (Euc d)) := hHYoung'

/-- The combined local/far convolution estimate for bounded `L¹ ∩ L²` data. -/
theorem fp81s21_conv_split_bound
    (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s + 1 < d) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ (g : Euc d → ℝ), Measurable g →
        (∃ M : ℝ, ∀ y, ‖g y‖ ≤ M) → Integrable g →
        MemLp g 2 (volume : Measure (Euc d)) →
        (∀ x, convGradConvW (rieszKernelGrad d s) g x =
          fp81s21_localConv (d := d) s g x + fp81s21_farConv (d := d) s g x) ∧
        eLpNorm (fp81s21_localConv (d := d) s g) 2 (volume : Measure (Euc d)) ≤
          ENNReal.ofReal C₁ * eLpNorm g 2 (volume : Measure (Euc d)) ∧
        (∀ x, ‖fp81s21_farConv (d := d) s g x‖ ≤ C₂ * ∫ y, ‖g y‖) := by
  obtain ⟨C₁, hC₁, hlocal⟩ := fp81s21_localConv_L2 (d := d) hd hs0 hs1
  obtain ⟨C₂, hC₂, hfar⟩ := fp81s21_farConv_bound (d := d) hd hs0 hs1
  refine ⟨C₁, C₂, hC₁, hC₂, fun g hgm hbound hg1 hg2 => ?_⟩
  refine ⟨fp81s21_conv_split_bdd (d := d) hd hs0 hs1 g hgm hg1 hbound,
    hlocal g hgm hbound hg2, ?_⟩
  exact hfar g hg1 hgm

#print axioms fp81s21_conv_split_bdd
#print axioms fp81s21_localConv_L2
#print axioms fp81s21_conv_split_bound

end HRS.Fp81.S21
