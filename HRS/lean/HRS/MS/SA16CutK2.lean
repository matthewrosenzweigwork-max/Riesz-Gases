import HRS.MS.SA16StrongSL2
import HRS.MS.SA16CutDefs

/-!
# S.A.16 K2: `splice_correction_bound`

`spliceOdd - rawOdd` is the convolution with the odd kernel `δ^(-θ) z_i |z|^(-d)` supported in the ball of radius
`δ`; its first moment is `≲ δ^(2-θ)` (the scaled moment lemma with `θ = 0`), and `sa16j_odd_wnorm` gives the bound
with one derivative lost.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv Phase2SA16

section K2
variable {d : ℕ}

/-- the added core: `spliceKernel` minus the raw odd kernel -/
def sa16k2_k (d : ℕ) (θ δ : ℝ) (i : Fin d) : Euc d → ℝ :=
  fun z => spliceKernel d θ δ i z - sa16s_kr d θ δ i z

lemma sa16k2_ks_meas (θ δ : ℝ) (i : Fin d) : Measurable (spliceKernel d θ δ i) := by
  unfold spliceKernel
  exact Measurable.ite (measurableSet_lt measurable_const measurable_norm)
    (((EuclideanSpace.proj i).continuous.measurable).div (measurable_norm.pow_const _))
    ((measurable_const.mul ((EuclideanSpace.proj i).continuous.measurable)).div
      (measurable_norm.pow_const _))

lemma sa16k2_k_meas (θ δ : ℝ) (i : Fin d) : Measurable (sa16k2_k d θ δ i) :=
  (sa16k2_ks_meas θ δ i).sub (sa16s_kr_meas θ δ i)

lemma sa16k2_k_supp (θ δ : ℝ) (i : Fin d) {z : Euc d} (hz : δ < ‖z‖) : sa16k2_k d θ δ i z = 0 := by
  have h1 : z ∈ {z : Euc d | δ < ‖z‖} := hz
  simp [sa16k2_k, spliceKernel, sa16s_kr, sa16s_g, hz, Set.indicator_of_mem h1]

lemma sa16k2_k_in (θ δ : ℝ) (i : Fin d) {z : Euc d} (hz : ¬ δ < ‖z‖) :
    sa16k2_k d θ δ i z = δ ^ (-θ) * z i / ‖z‖ ^ (d : ℝ) := by
  have h1 : z ∉ {z : Euc d | δ < ‖z‖} := hz
  simp [sa16k2_k, spliceKernel, sa16s_kr, hz, Set.indicator_of_notMem h1]

lemma sa16k2_k_odd (θ δ : ℝ) (i : Fin d) (z : Euc d) :
    sa16k2_k d θ δ i (-z) = -sa16k2_k d θ δ i z := by
  unfold sa16k2_k spliceKernel sa16s_kr
  simp only [Set.indicator, Set.mem_setOf_eq, norm_neg, sa16s_g_neg]
  split_ifs <;> simp [sa16s_g, neg_div, mul_neg]

/-- the core is bounded by `δ^(-θ) |z|^(1-d)` -/
lemma sa16k2_k_abs {θ δ : ℝ} (hδ : 0 < δ) (i : Fin d) {z : Euc d} (hn : 0 < ‖z‖) (hz : ¬ δ < ‖z‖) :
    |sa16k2_k d θ δ i z| ≤ δ ^ (-θ) * ‖z‖ ^ (1 - (d : ℝ)) := by
  rw [sa16k2_k_in θ δ i hz, abs_div, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hδ _),
    abs_of_pos (Real.rpow_pos_of_pos hn _), mul_div_assoc, Real.rpow_sub hn, Real.rpow_one]
  have : |z i| ≤ ‖z‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le z i
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right this (Real.rpow_pos_of_pos hn _).le)
    (Real.rpow_nonneg hδ.le _)

lemma sa16k2_k_int (hd : 1 ≤ d) {θ δ : ℝ} (hδ : 0 < δ) (i : Fin d) :
    Integrable (sa16k2_k d θ δ i) := by
  have hsupp : sa16k2_k d θ δ i = (closedBall (0 : Euc d) δ).indicator (sa16k2_k d θ δ i) := by
    funext z
    by_cases hz : z ∈ closedBall (0 : Euc d) δ
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, sa16k2_k_supp θ δ i (by simpa using hz)]
  rw [hsupp, integrable_indicator_iff measurableSet_closedBall]
  have hi : IntegrableOn (fun z : Euc d => ‖z‖ ^ (-((d : ℝ) - 1))) (ball 0 (2 * δ)) :=
    pvapi_integrableOn_ball_rpow hd (α := (d : ℝ) - 1) (by linarith) (2 * δ)
  refine Integrable.mono' ((hi.mono_set (closedBall_subset_ball (by linarith))).const_mul (δ ^ (-θ)))
    (sa16k2_k_meas θ δ i).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun z hz => ?_)
  rw [Real.norm_eq_abs]
  have hz' : ¬ δ < ‖z‖ := by simpa using hz
  by_cases hn : ‖z‖ = 0
  · have : z = 0 := norm_eq_zero.1 hn
    subst this
    have : sa16k2_k d θ δ i 0 = 0 := by rw [sa16k2_k_in θ δ i hz']; simp
    rw [this, abs_zero]
    exact mul_nonneg (Real.rpow_nonneg hδ.le _) (Real.rpow_nonneg (norm_nonneg _) _)
  · have hn' : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    refine (sa16k2_k_abs hδ i hn' hz').trans (le_of_eq ?_)
    congr 2; ring

lemma sa16k2_moment_le {θ δ : ℝ} (hδ : 0 < δ) (i : Fin d) (z : Euc d) :
    |sa16k2_k d θ δ i z| * ‖z‖ ≤ δ ^ (-θ) * (closedBall (0 : Euc d) δ).indicator
      (fun z => ‖z‖ ^ (2 - ((d : ℝ) + 0))) z := by
  by_cases hz : z ∈ closedBall (0 : Euc d) δ
  · rw [Set.indicator_of_mem hz]
    have hz' : ¬ δ < ‖z‖ := by simpa using hz
    by_cases hn : ‖z‖ = 0
    · have : z = 0 := norm_eq_zero.1 hn
      subst this
      have : sa16k2_k d θ δ i 0 = 0 := by rw [sa16k2_k_in θ δ i hz']; simp
      rw [this]
      simp only [abs_zero, zero_mul, norm_zero]
      exact mul_nonneg (Real.rpow_nonneg hδ.le _) (Real.rpow_nonneg le_rfl _)
    · have hn' : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
      calc |sa16k2_k d θ δ i z| * ‖z‖ ≤ (δ ^ (-θ) * ‖z‖ ^ (1 - (d : ℝ))) * ‖z‖ :=
            mul_le_mul_of_nonneg_right (sa16k2_k_abs hδ i hn' hz') hn'.le
        _ = δ ^ (-θ) * ‖z‖ ^ (2 - ((d : ℝ) + 0)) := by
            rw [mul_assoc, show 2 - ((d : ℝ) + 0) = (1 - (d : ℝ)) + 1 by ring, Real.rpow_add hn',
              Real.rpow_one]
  · rw [Set.indicator_of_notMem hz, sa16k2_k_supp θ δ i (by simpa using hz)]
    simp

lemma sa16k2_repr {θ δ : ℝ} (hd : 1 ≤ d) (hδ : 0 < δ) (hθ : 0 < θ) (i : Fin d)
    (u : 𝓢(Euc d, ℝ)) (x : Euc d) :
    spliceOdd d θ δ i u x - rawOdd d θ δ i u x = ∫ z, sa16k2_k d θ δ i z * u (x - z) := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ y, |u y| ≤ B := sa16j_schwartz_bdd u
  have hint2 : Integrable (fun z => sa16k2_k d θ δ i z * u (x - z)) := by
    refine Integrable.mono' ((sa16k2_k_int (θ := θ) hd hδ i).norm.mul_const B)
      ((sa16k2_k_meas θ δ i).aestronglyMeasurable.mul
        (u.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((Real.norm_eq_abs _).le.trans (hB _)) (norm_nonneg _)
  have hint1 := sa16s_kr_int hd hδ hθ i u x
  have hS : MeasurableSet {z : Euc d | δ < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have hraw : rawOdd d θ δ i u x = ∫ z, sa16s_kr d θ δ i z * u (x - z) := by
    unfold rawOdd sa16s_kr sa16s_g
    rw [← integral_indicator hS]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [Set.indicator_mul_left]
  have hspl : spliceOdd d θ δ i u x = ∫ z, (sa16k2_k d θ δ i z * u (x - z) +
      sa16s_kr d θ δ i z * u (x - z)) := by
    unfold spliceOdd
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [sa16k2_k]
    ring
  rw [hspl, hraw, integral_add hint2 hint1]
  ring

theorem splice_correction_bound (d m : ℕ) (hd : 1 ≤ d) (θ p : ℝ)
    (hθ0 : 0 < θ) (hθ2 : θ < 2) [Fact (2 ≤ p)] :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ i : Fin d,
      ∀ u : SchwartzMap (Euc d) ℝ,
      wNormE m p (fun x => spliceOdd d θ δ i u x-rawOdd d θ δ i u x) ≤
        ENNReal.ofReal (C*δ^(2-θ))*wNormE (m+1) p u := by
  obtain ⟨I₀, hI₀, hmom⟩ := sa16s_moment (d := d) hd (θ := 0) (by norm_num)
  set N : ℝ := (Fintype.card (WIndex d m) : ℝ) * ((d : ℝ) ^ (m + 1)) with hN
  have hN0 : 0 ≤ N := by positivity
  refine ⟨N * I₀ + 1, by positivity, fun δ hδ i u => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hfun : (fun x => spliceOdd d θ δ i u x - rawOdd d θ δ i u x) =
      sa16j_conv (sa16k2_k d θ δ i) (⇑u) := by
    funext x
    exact sa16k2_repr hd hδ0 hθ0 i u x
  rw [hfun]
  obtain ⟨hBint, hBval⟩ := hmom δ hδ0
  have hkm : Integrable (fun z => |sa16k2_k d θ δ i z| * ‖z‖) := by
    refine Integrable.mono' (hBint.const_mul (δ ^ (-θ))) ?_ (Eventually.of_forall fun z => ?_)
    · exact ((sa16k2_k_meas θ δ i).abs.mul measurable_norm).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact sa16k2_moment_le hδ0 i z
  have hMk : ∫ z, |sa16k2_k d θ δ i z| * ‖z‖ ≤ δ ^ (2 - θ) * I₀ := by
    have h1 : ∫ z, |sa16k2_k d θ δ i z| * ‖z‖ ≤ ∫ z, δ ^ (-θ) * (closedBall (0 : Euc d) δ).indicator
        (fun z => ‖z‖ ^ (2 - ((d : ℝ) + 0))) z :=
      integral_mono hkm (hBint.const_mul (δ ^ (-θ))) (fun z => sa16k2_moment_le hδ0 i z)
    rw [integral_const_mul, hBval] at h1
    refine h1.trans (le_of_eq ?_)
    have : δ ^ (-θ) * δ ^ (2 - 0 : ℝ) = δ ^ (2 - θ) := by
      rw [← Real.rpow_add hδ0]; congr 1; ring
    rw [← mul_assoc, this]
  have hmain := sa16j_odd_wnorm d hd m p (R := δ) hδ0.le (sa16k2_k_meas θ δ i)
    (fun z hz => sa16k2_k_supp θ δ i hz) (sa16k2_k_int (θ := θ) hd hδ0 i) hkm (sa16k2_k_odd θ δ i) u
  refine hmain.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  have hpos : 0 ≤ δ ^ (2 - θ) := Real.rpow_nonneg hδ0.le _
  calc (Fintype.card (WIndex d m) : ℝ) * ((∫ z, |sa16k2_k d θ δ i z| * ‖z‖) * (d : ℝ) ^ (m + 1))
      = N * (∫ z, |sa16k2_k d θ δ i z| * ‖z‖) := by rw [hN]; ring
    _ ≤ N * (δ ^ (2 - θ) * I₀) := mul_le_mul_of_nonneg_left hMk hN0
    _ ≤ (N * I₀ + 1) * δ ^ (2 - θ) := by nlinarith

end K2

end HRS.Whole.AppendixA.Phase2SA16Cutoff
