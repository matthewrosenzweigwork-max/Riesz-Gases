import HRS.MS.SA16CutDefs
import HRS.MS.CzElemAux4

/-!
# S.A.16 K5: `splice_commutator_bound`

The blend `(1-b) rawOdd + b spliceOdd` is convolution with the odd kernel `Kb`, `|Kb z| ≤ |z|^(1-d-θ)`
(the splice kernel inside the ball is `δ^(-θ)|z|^(1-d) ≤ |z|^(1-d-θ)`).  The commutator with `a ∈ C_b¹` is
convolution with `Kb(z)(a(x-z)-a(x))`, majorized by the integrable kernel `elema_kk` (`θ ∈ (1,2)`); Young.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv HRS.CZ.ElemA

section K5
variable {d : ℕ}

/-- the raw odd kernel as a function of `z` -/
def sa16k5_kr (d : ℕ) (θ δ : ℝ) (i : Fin d) : Euc d → ℝ :=
  {z : Euc d | δ < ‖z‖}.indicator (fun z => z i / ‖z‖ ^ ((d : ℝ) + θ))

/-- the blend kernel -/
def sa16k5_Kb (d : ℕ) (θ δ b : ℝ) (i : Fin d) : Euc d → ℝ :=
  fun z => (1 - b) * sa16k5_kr d θ δ i z + b * spliceKernel d θ δ i z

lemma sa16k5_coord_le (i : Fin d) (z : Euc d) : |z i| ≤ ‖z‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le z i

lemma sa16k5_big_bound {θ : ℝ} (i : Fin d) {z : Euc d} (hz : 0 < ‖z‖) :
    |z i / ‖z‖ ^ ((d : ℝ) + θ)| ≤ ‖z‖ ^ (1 - ((d : ℝ) + θ)) := by
  rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hz _), Real.rpow_sub hz, Real.rpow_one]
  exact div_le_div_of_nonneg_right (sa16k5_coord_le i z) (Real.rpow_pos_of_pos hz _).le

lemma sa16k5_kr_meas (θ δ : ℝ) (i : Fin d) : Measurable (sa16k5_kr d θ δ i) := by
  unfold sa16k5_kr
  exact (((EuclideanSpace.proj i).continuous.measurable).div
    (measurable_norm.pow_const _)).indicator (measurableSet_lt measurable_const measurable_norm)

lemma sa16k5_ks_meas (θ δ : ℝ) (i : Fin d) : Measurable (spliceKernel d θ δ i) := by
  unfold spliceKernel
  exact Measurable.ite (measurableSet_lt measurable_const measurable_norm)
    (((EuclideanSpace.proj i).continuous.measurable).div (measurable_norm.pow_const _))
    ((measurable_const.mul ((EuclideanSpace.proj i).continuous.measurable)).div
      (measurable_norm.pow_const _))

lemma sa16k5_Kb_meas (θ δ b : ℝ) (i : Fin d) : Measurable (sa16k5_Kb d θ δ b i) :=
  (measurable_const.mul (sa16k5_kr_meas θ δ i)).add (measurable_const.mul (sa16k5_ks_meas θ δ i))

lemma sa16k5_kr_bound {θ δ : ℝ} (hδ : 0 < δ) (i : Fin d) (z : Euc d) :
    |sa16k5_kr d θ δ i z| ≤ ‖z‖ ^ (1 - ((d : ℝ) + θ)) := by
  unfold sa16k5_kr
  by_cases hz : z ∈ {z : Euc d | δ < ‖z‖}
  · rw [Set.indicator_of_mem hz]
    exact sa16k5_big_bound i (hδ.trans hz)
  · rw [Set.indicator_of_notMem hz, abs_zero]
    exact Real.rpow_nonneg (norm_nonneg _) _

lemma sa16k5_ks_small {θ δ : ℝ} (hδ : 0 < δ) (hθ : 0 ≤ θ) (i : Fin d) {z : Euc d}
    (hz : ¬ δ < ‖z‖) :
    |spliceKernel d θ δ i z| ≤ δ ^ (-θ) * ‖z‖ ^ (-((d : ℝ) - 1)) := by
  unfold spliceKernel
  rw [if_neg hz]
  by_cases hz0 : ‖z‖ = 0
  · have : z = 0 := norm_eq_zero.1 hz0
    subst this
    simp only [PiLp.zero_apply, mul_zero, zero_div, abs_zero]
    exact mul_nonneg (Real.rpow_nonneg hδ.le _) (Real.rpow_nonneg (norm_nonneg _) _)
  · have hn : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz0)
    rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hn _), abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos hδ _)]
    have e : ‖z‖ ^ (-((d : ℝ) - 1)) = ‖z‖ / ‖z‖ ^ (d : ℝ) := by
      rw [show -((d : ℝ) - 1) = 1 - (d : ℝ) by ring, Real.rpow_sub hn, Real.rpow_one]
    rw [e, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (sa16k5_coord_le i z)
      (Real.rpow_pos_of_pos hn _).le) (Real.rpow_nonneg hδ.le _)

lemma sa16k5_ks_bound {θ δ : ℝ} (hδ : 0 < δ) (hθ : 0 ≤ θ) (i : Fin d) (z : Euc d) :
    |spliceKernel d θ δ i z| ≤ ‖z‖ ^ (1 - ((d : ℝ) + θ)) := by
  by_cases hz : δ < ‖z‖
  · unfold spliceKernel
    rw [if_pos hz]
    exact sa16k5_big_bound i (hδ.trans hz)
  · by_cases hz0 : ‖z‖ = 0
    · have : z = 0 := norm_eq_zero.1 hz0
      subst this
      unfold spliceKernel
      simp only [if_neg hz, PiLp.zero_apply, mul_zero, zero_div, abs_zero]
      exact Real.rpow_nonneg (norm_nonneg _) _
    · have hn : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz0)
      refine (sa16k5_ks_small hδ hθ i hz).trans ?_
      have h1 : δ ^ (-θ) ≤ ‖z‖ ^ (-θ) :=
        Real.rpow_le_rpow_of_nonpos hn (not_lt.1 hz) (by linarith)
      calc δ ^ (-θ) * ‖z‖ ^ (-((d : ℝ) - 1)) ≤ ‖z‖ ^ (-θ) * ‖z‖ ^ (-((d : ℝ) - 1)) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (norm_nonneg _) _)
        _ = ‖z‖ ^ (1 - ((d : ℝ) + θ)) := by
            rw [← Real.rpow_add hn]; congr 1; ring

lemma sa16k5_Kb_bound {θ δ b : ℝ} (hδ : 0 < δ) (hθ : 0 ≤ θ) (hb : b ∈ Icc (0 : ℝ) 1) (i : Fin d)
    (z : Euc d) : |sa16k5_Kb d θ δ b i z| ≤ ‖z‖ ^ (1 - ((d : ℝ) + θ)) := by
  unfold sa16k5_Kb
  have h1 := sa16k5_kr_bound (θ := θ) hδ i z
  have h2 := sa16k5_ks_bound hδ hθ i z
  calc |(1 - b) * sa16k5_kr d θ δ i z + b * spliceKernel d θ δ i z|
      ≤ |(1 - b) * sa16k5_kr d θ δ i z| + |b * spliceKernel d θ δ i z| := abs_add_le _ _
    _ = (1 - b) * |sa16k5_kr d θ δ i z| + b * |spliceKernel d θ δ i z| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [hb.2] : 0 ≤ 1 - b), abs_of_nonneg hb.1]
    _ ≤ (1 - b) * ‖z‖ ^ (1 - ((d : ℝ) + θ)) + b * ‖z‖ ^ (1 - ((d : ℝ) + θ)) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (by linarith [hb.2]))
          (mul_le_mul_of_nonneg_left h2 hb.1)
    _ = ‖z‖ ^ (1 - ((d : ℝ) + θ)) := by ring

/-- an integrable majorant of both odd kernels -/
def sa16k5_D (d : ℕ) (θ δ : ℝ) : Euc d → ℝ := fun z =>
  {z : Euc d | δ < ‖z‖}.indicator (fun z => ‖z‖ ^ (-((d : ℝ) + θ - 1))) z +
    (closedBall (0 : Euc d) δ).indicator (fun z => δ ^ (-θ) * ‖z‖ ^ (-((d : ℝ) - 1))) z

lemma sa16k5_D_int (hd : 1 ≤ d) {θ δ : ℝ} (hθ1 : 1 < θ) (hδ : 0 < δ) :
    Integrable (sa16k5_D d θ δ) := by
  have hS : MeasurableSet {z : Euc d | δ < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  refine Integrable.add ?_ ?_
  · rw [integrable_indicator_iff hS]
    exact pvapi_integrableOn_rpow_outside hd (s := (d : ℝ) + θ - 1) (by linarith) hδ
  · rw [integrable_indicator_iff measurableSet_closedBall]
    have : IntegrableOn (fun z : Euc d => ‖z‖ ^ (-((d : ℝ) - 1))) (ball 0 (2 * δ)) :=
      pvapi_integrableOn_ball_rpow hd (α := (d : ℝ) - 1) (by linarith) (2 * δ)
    exact (this.mono_set (closedBall_subset_ball (by linarith))).const_mul _

lemma sa16k5_D_nonneg {θ δ : ℝ} (hδ : 0 < δ) (z : Euc d) : 0 ≤ sa16k5_D d θ δ z := by
  unfold sa16k5_D
  refine add_nonneg (Set.indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg _) _) z)
    (Set.indicator_nonneg (fun z _ => mul_nonneg (Real.rpow_nonneg hδ.le _)
      (Real.rpow_nonneg (norm_nonneg _) _)) z)

lemma sa16k5_kr_le_D {θ δ : ℝ} (hδ : 0 < δ) (i : Fin d) (z : Euc d) :
    |sa16k5_kr d θ δ i z| ≤ sa16k5_D d θ δ z := by
  unfold sa16k5_D sa16k5_kr
  by_cases hz : z ∈ {z : Euc d | δ < ‖z‖}
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    have h2 : 0 ≤ (closedBall (0 : Euc d) δ).indicator
        (fun z => δ ^ (-θ) * ‖z‖ ^ (-((d : ℝ) - 1))) z :=
      Set.indicator_nonneg (fun z _ => mul_nonneg (Real.rpow_nonneg hδ.le _)
        (Real.rpow_nonneg (norm_nonneg _) _)) z
    have h1 := sa16k5_big_bound (θ := θ) i (hδ.trans hz)
    have e : (1 : ℝ) - ((d : ℝ) + θ) = -((d : ℝ) + θ - 1) := by ring
    rw [e] at h1
    linarith
  · rw [Set.indicator_of_notMem hz, abs_zero]
    refine add_nonneg ?_ ?_
    · rw [Set.indicator_of_notMem hz]
    · exact Set.indicator_nonneg (fun z _ => mul_nonneg (Real.rpow_nonneg hδ.le _)
        (Real.rpow_nonneg (norm_nonneg _) _)) z

lemma sa16k5_ks_le_D {θ δ : ℝ} (hδ : 0 < δ) (hθ : 0 ≤ θ) (i : Fin d) (z : Euc d) :
    |spliceKernel d θ δ i z| ≤ sa16k5_D d θ δ z := by
  unfold sa16k5_D
  by_cases hz : δ < ‖z‖
  · have hzS : z ∈ {z : Euc d | δ < ‖z‖} := hz
    rw [Set.indicator_of_mem hzS]
    have h2 : 0 ≤ (closedBall (0 : Euc d) δ).indicator
        (fun z => δ ^ (-θ) * ‖z‖ ^ (-((d : ℝ) - 1))) z :=
      Set.indicator_nonneg (fun z _ => mul_nonneg (Real.rpow_nonneg hδ.le _)
        (Real.rpow_nonneg (norm_nonneg _) _)) z
    have h1 := sa16k5_ks_bound hδ hθ i z
    have e : (1 : ℝ) - ((d : ℝ) + θ) = -((d : ℝ) + θ - 1) := by ring
    rw [e] at h1
    linarith
  · have hzS : z ∉ {z : Euc d | δ < ‖z‖} := hz
    rw [Set.indicator_of_notMem hzS, zero_add]
    have hzb : z ∈ closedBall (0 : Euc d) δ := by
      rw [mem_closedBall, dist_zero_right]; exact not_lt.1 hz
    rw [Set.indicator_of_mem hzb]
    exact sa16k5_ks_small hδ hθ i hz

lemma sa16k5_Kb_le_D {θ δ b : ℝ} (hδ : 0 < δ) (hθ : 0 ≤ θ) (hb : b ∈ Icc (0 : ℝ) 1) (i : Fin d)
    (z : Euc d) : |sa16k5_Kb d θ δ b i z| ≤ sa16k5_D d θ δ z := by
  unfold sa16k5_Kb
  have h1 := sa16k5_kr_le_D (θ := θ) hδ i z
  have h2 := sa16k5_ks_le_D hδ hθ i z
  calc |(1 - b) * sa16k5_kr d θ δ i z + b * spliceKernel d θ δ i z|
      ≤ |(1 - b) * sa16k5_kr d θ δ i z| + |b * spliceKernel d θ δ i z| := abs_add_le _ _
    _ = (1 - b) * |sa16k5_kr d θ δ i z| + b * |spliceKernel d θ δ i z| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [hb.2] : 0 ≤ 1 - b), abs_of_nonneg hb.1]
    _ ≤ (1 - b) * sa16k5_D d θ δ z + b * sa16k5_D d θ δ z :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (by linarith [hb.2]))
          (mul_le_mul_of_nonneg_left h2 hb.1)
    _ = sa16k5_D d θ δ z := by ring

/-- the blend kernel against a bounded continuous function is integrable -/
lemma sa16k5_Kb_int_mul (hd : 1 ≤ d) {θ δ b : ℝ} (hθ1 : 1 < θ) (hδ : 0 < δ)
    (hb : b ∈ Icc (0 : ℝ) 1) (i : Fin d) {u : Euc d → ℝ} (hu : Continuous u) {Bu : ℝ}
    (hub : ∀ y, |u y| ≤ Bu) (x : Euc d) :
    Integrable (fun z => sa16k5_Kb d θ δ b i z * u (x - z)) := by
  refine Integrable.mono' ((sa16k5_D_int hd hθ1 hδ).mul_const Bu)
    (((sa16k5_Kb_meas θ δ b i).mul
      (hu.measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable) ?_
  refine Eventually.of_forall fun z => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (sa16k5_Kb_le_D hδ (by linarith) hb i z) (hub _) (abs_nonneg _)
    (sa16k5_D_nonneg hδ z)

/-- `oddBlend` is convolution with `Kb` -/
lemma sa16k5_oddBlend_eq (hd : 1 ≤ d) {θ δ b : ℝ} (hθ1 : 1 < θ) (hδ : 0 < δ)
    (hb : b ∈ Icc (0 : ℝ) 1) (i : Fin d) {u : Euc d → ℝ} (hu : Continuous u) {Bu : ℝ}
    (hub : ∀ y, |u y| ≤ Bu) (x : Euc d) :
    oddBlend d θ δ b i u x = ∫ z, sa16k5_Kb d θ δ b i z * u (x - z) := by
  have hS : MeasurableSet {z : Euc d | δ < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have hmeas : Measurable (fun z : Euc d => u (x - z)) :=
    hu.measurable.comp (measurable_const.sub measurable_id)
  have iKr : Integrable (fun z => sa16k5_kr d θ δ i z * u (x - z)) := by
    refine Integrable.mono' ((sa16k5_D_int hd hθ1 hδ).mul_const Bu)
      (((sa16k5_kr_meas θ δ i).mul hmeas).aestronglyMeasurable) ?_
    refine Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (sa16k5_kr_le_D hδ i z) (hub _) (abs_nonneg _) (sa16k5_D_nonneg hδ z)
  have iKs : Integrable (fun z => spliceKernel d θ δ i z * u (x - z)) := by
    refine Integrable.mono' ((sa16k5_D_int hd hθ1 hδ).mul_const Bu)
      (((sa16k5_ks_meas θ δ i).mul hmeas).aestronglyMeasurable) ?_
    refine Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (sa16k5_ks_le_D hδ (by linarith) i z) (hub _) (abs_nonneg _)
      (sa16k5_D_nonneg hδ z)
  have hraw : rawOdd d θ δ i u x = ∫ z, sa16k5_kr d θ δ i z * u (x - z) := by
    unfold rawOdd sa16k5_kr
    rw [← integral_indicator hS]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [Set.indicator_mul_left]
  have hspl : spliceOdd d θ δ i u x = ∫ z, spliceKernel d θ δ i z * u (x - z) := rfl
  have e : ∀ z : Euc d, sa16k5_Kb d θ δ b i z * u (x - z) =
      (1 - b) * (sa16k5_kr d θ δ i z * u (x - z)) + b * (spliceKernel d θ δ i z * u (x - z)) := by
    intro z; unfold sa16k5_Kb; ring
  simp_rw [e]
  rw [integral_add (iKr.const_mul _) (iKs.const_mul _), integral_const_mul, integral_const_mul]
  unfold oddBlend
  rw [hraw, hspl]
  ring

lemma sa16k5_conv_aesm {k : Euc d → ℝ} (hk : Measurable k) {u : Euc d → ℝ} (hu : Continuous u) :
    AEStronglyMeasurable (fun x => ∫ z, k z * u (x - z)) volume := by
  have hm : Measurable (fun q : Euc d × Euc d => k q.2 * u (q.1 - q.2)) :=
    (hk.comp measurable_snd).mul (hu.measurable.comp (measurable_fst.sub measurable_snd))
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable

end K5

theorem splice_commutator_bound (d : ℕ) (hd : 1 ≤ d) (θ p : ℝ)
    (hθ1 : 1 < θ) (hθ2 : θ < 2) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1,
      ∀ blend ∈ Icc (0 : ℝ) 1, ∀ i : Fin d,
      ∀ a : Euc d → ℝ, MemCb 1 a →
      ∀ W : SchwartzMap (Euc d) ℝ,
      eLpNorm (fun x => oddBlend d θ δ blend i (fun y => a y*W y) x-
          a x*oddBlend d θ δ blend i W x) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C*cbNorm 1 a)*eLpNorm W (ENNReal.ofReal p) volume := by
  obtain ⟨C0, hC0, hkk⟩ := elema_kk_lintegral hd hθ1 hθ2 (B := 1) zero_le_one
  refine ⟨C0 + 1, by linarith, fun δ hδ b hb i a ha W => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  obtain ⟨Ba, La, hBa, hLa, hcb, hab, halip⟩ := elema_cb1_data ha
  have hac : Continuous a := (ha.1.continuous)
  obtain ⟨BW, hBW⟩ : ∃ BW : ℝ, ∀ y, |W y| ≤ BW :=
    ⟨‖W.toBoundedContinuousFunction‖, fun y => by
      have := W.toBoundedContinuousFunction.norm_coe_le_norm y
      simpa [Real.norm_eq_abs] using this⟩
  have haW : Continuous (fun y => a y * W y) := hac.mul W.continuous
  have haWb : ∀ y, |a y * W y| ≤ Ba * BW := fun y => by
    rw [abs_mul]; exact mul_le_mul (hab y) (hBW y) (abs_nonneg _) hBa
  have hFeq : (fun x => oddBlend d θ δ b i (fun y => a y * W y) x -
        a x * oddBlend d θ δ b i W x) =
      fun x => (∫ z, sa16k5_Kb d θ δ b i z * (a (x - z) * W (x - z))) -
        a x * ∫ z, sa16k5_Kb d θ δ b i z * W (x - z) := by
    funext x
    rw [sa16k5_oddBlend_eq hd hθ1 hδ0 hb i haW haWb x,
      sa16k5_oddBlend_eq hd hθ1 hδ0 hb i W.continuous hBW x]
  rw [hFeq]
  have hFm : AEStronglyMeasurable (fun x => (∫ z, sa16k5_Kb d θ δ b i z * (a (x - z) * W (x - z))) -
        a x * ∫ z, sa16k5_Kb d θ δ b i z * W (x - z)) volume :=
    (sa16k5_conv_aesm (sa16k5_Kb_meas θ δ b i) haW).sub
      (hac.aestronglyMeasurable.mul (sa16k5_conv_aesm (sa16k5_Kb_meas θ δ b i) W.continuous))
  have hpt : ∀ x, (∫ z, sa16k5_Kb d θ δ b i z * (a (x - z) * W (x - z))) -
        a x * ∫ z, sa16k5_Kb d θ δ b i z * W (x - z) =
      ∫ z, sa16k5_Kb d θ δ b i z * (a (x - z) - a x) * W (x - z) := by
    intro x
    have i1 := sa16k5_Kb_int_mul hd hθ1 hδ0 hb i haW haWb x
    have i2 := sa16k5_Kb_int_mul hd hθ1 hδ0 hb i W.continuous hBW x
    rw [← integral_const_mul, ← integral_sub i1 (i2.const_mul _)]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    ring
  refine (elema_young (elema_kk_measurable θ 1 La Ba) W.continuous.measurable hFm
    (by linarith) (fun x => ?_)).trans (mul_le_mul_left ?_ _)
  · rw [hpt x]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun z => ?_)
    rw [enorm_mul]
    refine mul_le_mul_left ?_ _
    refine pvapi_enorm_le ?_
    have hKb := sa16k5_Kb_bound (θ := θ) hδ0 (by linarith) hb i z
    have hKb0 : 0 ≤ ‖z‖ ^ (1 - ((d : ℝ) + θ)) := Real.rpow_nonneg (norm_nonneg _) _
    rw [abs_mul]
    by_cases hz0 : ‖z‖ = 0
    · have hz : z = 0 := norm_eq_zero.1 hz0
      subst hz
      have : sa16k5_Kb d θ δ b i 0 = 0 := by
        have h0 : |sa16k5_Kb d θ δ b i 0| ≤ 0 := by
          refine hKb.trans (le_of_eq ?_)
          rw [norm_zero]
          exact Real.zero_rpow (by linarith)
        exact abs_nonpos_iff.1 h0
      rw [this, abs_zero, zero_mul]
      exact elema_kk_nonneg θ 1 La Ba zero_le_one hLa hBa 0
    · have hn : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz0)
      unfold elema_kk
      by_cases hz1 : ‖z‖ ≤ 1
      · rw [if_pos hz1]
        have hlip : |a (x - z) - a x| ≤ La * ‖z‖ := by
          have := halip (x - z) x
          rwa [sub_sub_cancel_left, norm_neg] at this
        calc |sa16k5_Kb d θ δ b i z| * |a (x - z) - a x|
            ≤ ‖z‖ ^ (1 - ((d : ℝ) + θ)) * (La * ‖z‖) :=
              mul_le_mul hKb hlip (abs_nonneg _) hKb0
          _ = 1 * La * ‖z‖ ^ (2 - ((d : ℝ) + θ)) := by
              have : ‖z‖ ^ (2 - ((d : ℝ) + θ)) = ‖z‖ ^ (1 - ((d : ℝ) + θ)) * ‖z‖ := by
                rw [show 2 - ((d : ℝ) + θ) = (1 - ((d : ℝ) + θ)) + 1 by ring,
                  Real.rpow_add hn, Real.rpow_one]
              rw [this]; ring
      · rw [if_neg hz1]
        have hlip : |a (x - z) - a x| ≤ 2 * Ba := by
          calc |a (x - z) - a x| ≤ |a (x - z)| + |a x| := abs_sub _ _
            _ ≤ Ba + Ba := add_le_add (hab _) (hab _)
            _ = 2 * Ba := by ring
        calc |sa16k5_Kb d θ δ b i z| * |a (x - z) - a x|
            ≤ ‖z‖ ^ (1 - ((d : ℝ) + θ)) * (2 * Ba) :=
              mul_le_mul hKb hlip (abs_nonneg _) hKb0
          _ = 1 * (2 * Ba) * ‖z‖ ^ (1 - ((d : ℝ) + θ)) := by ring
  · refine (hkk La Ba hLa hBa).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hcb]
    have : 0 ≤ Ba + La := by linarith
    nlinarith [mul_nonneg hC0 this]

end HRS.Whole.AppendixA.Phase2SA16Cutoff
