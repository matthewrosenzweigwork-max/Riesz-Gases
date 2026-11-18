import HRS.MS.SA16QApp2

/-!
# S.A.16 (SA16Q), E6 part 15: linearity and pointwise convergence of `eucNonlocal` in the coefficient

For `C¹_b` coefficients `a, b` (`d ≥ 2`, `0 ≤ s ≤ d-2`, `u ∈ 𝓢`):

* `sa16q_F_sub`: `eucNonlocal s M (a - b) u = eucNonlocal s M a u - eucNonlocal s M b u`;
* `sa16q_F_tendsto`: if `a_N → a` pointwise with `|a_N| ≤ B`, then `eucNonlocal s M a_N u x → eucNonlocal s M a u x`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section Fin1
variable {d : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2)
include hd hs hs2

lemma sa16q_K1E_WI (i : Fin d) : sa16q_WI (sa16q_K1E s 0 i) := by
  have h := sa16q_m1_WI hd hs hs2
  unfold sa16q_WI at h ⊢
  refine h.mono' ?_ ?_
  · exact (((sa16q_K1E_meas s 0 i).norm).mul
      ((measurable_const.add measurable_norm).pow_const _)).aestronglyMeasurable
  · filter_upwards [sa16q_ae_ne (d := d) (by omega)] with y hy
    have hw : 0 ≤ (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ)) := Real.rpow_nonneg (by positivity) _
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hw)]
    have h1 : ‖sa16q_K1E s 0 i y‖ ≤ ‖sa16q_m1 d s y‖ := by
      rw [Real.norm_eq_abs, Real.norm_of_nonneg (sa16q_m1_nonneg hs y)]
      exact sa16q_K1E_bound hs 0 i hy
    exact mul_le_mul_of_nonneg_right h1 hw

lemma sa16q_Fint_integrable {a : Euc d → ℝ} (ha1 : ContDiff ℝ 1 a) {B0 B1 : ℝ} (hB0 : ∀ x, |a x| ≤ B0)
    (hB1 : ∀ x, ‖fderiv ℝ a x‖ ≤ B1) (u : 𝓢(Euc d, ℝ)) (i j : Fin d) (x : Euc d) :
    Integrable (fun y => sa16q_K1E s 0 i y *
      (a (x - y) * fderiv ℝ u (x - y) (EuclideanSpace.single j (1 : ℝ)))) := by
  obtain ⟨C, hC, hdiff, hcont, hD, hD'⟩ :=
    sa16q_prod_hyp ha1 hB0 hB1 (sa16q_dS (EuclideanSpace.single j (1 : ℝ)) u)
  have := sa16q_conv_integrable (sa16q_K1E_meas s 0 i) (sa16q_K1E_WI hd hs hs2 i) hC hdiff.continuous hD x
  refine this.congr (Eventually.of_forall fun y => ?_)
  simp only [sa16q_dS_apply]

theorem sa16q_F_sub (M : Matrix (Fin d) (Fin d) ℝ) {a b : Euc d → ℝ} (ha1 : ContDiff ℝ 1 a)
    (hb1 : ContDiff ℝ 1 b) {B0 B1 B0' B1' : ℝ} (hB0 : ∀ x, |a x| ≤ B0) (hB1 : ∀ x, ‖fderiv ℝ a x‖ ≤ B1)
    (hB0' : ∀ x, |b x| ≤ B0') (hB1' : ∀ x, ‖fderiv ℝ b x‖ ≤ B1') (u : 𝓢(Euc d, ℝ)) (x : Euc d) :
    HRS.MH.AdjointRd.eucNonlocal s M (fun y => a y - b y) ⇑u x =
      HRS.MH.AdjointRd.eucNonlocal s M a ⇑u x - HRS.MH.AdjointRd.eucNonlocal s M b ⇑u x := by
  have hab : ContDiff ℝ 1 (fun y => a y - b y) := ha1.sub hb1
  have had : Differentiable ℝ a := ha1.differentiable (by simp)
  have hbd : Differentiable ℝ b := hb1.differentiable (by simp)
  rw [sa16q_F_pointwise hd hs hs2 M hab (B0 := B0 + B0') (B1 := B1 + B1')
      (fun y => (abs_sub _ _).trans (add_le_add (hB0 y) (hB0' y)))
      (fun y => by
        rw [fderiv_fun_sub (had y) (hbd y)]
        exact (norm_sub_le _ _).trans (add_le_add (hB1 y) (hB1' y))) u x,
    sa16q_F_pointwise hd hs hs2 M ha1 hB0 hB1 u x, sa16q_F_pointwise hd hs hs2 M hb1 hB0' hB1' u x,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_sub, ← integral_sub (sa16q_Fint_integrable hd hs hs2 ha1 hB0 hB1 u i j x)
    (sa16q_Fint_integrable hd hs hs2 hb1 hB0' hB1' u i j x)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  ring

theorem sa16q_F_tendsto (M : Matrix (Fin d) (Fin d) ℝ) {a : Euc d → ℝ} (ha1 : ContDiff ℝ 1 a)
    {B0 B1 : ℝ} (hB0 : ∀ x, |a x| ≤ B0) (hB1 : ∀ x, ‖fderiv ℝ a x‖ ≤ B1)
    (aN : ℕ → Euc d → ℝ) (haN1 : ∀ N, ContDiff ℝ 1 (aN N)) (hbd : ∀ N x, |aN N x| ≤ B0)
    (hbd1 : ∀ N, ∃ B1 : ℝ, ∀ x, ‖fderiv ℝ (aN N) x‖ ≤ B1)
    (hlim : ∀ y, Tendsto (fun N => aN N y) atTop (𝓝 (a y))) (u : 𝓢(Euc d, ℝ)) (x : Euc d) :
    Tendsto (fun N => HRS.MH.AdjointRd.eucNonlocal s M (aN N) ⇑u x) atTop
      (𝓝 (HRS.MH.AdjointRd.eucNonlocal s M a ⇑u x)) := by
  have hB00 : 0 ≤ B0 := (abs_nonneg _).trans (hB0 0)
  have h1 : ∀ N, HRS.MH.AdjointRd.eucNonlocal s M (aN N) ⇑u x = ∑ i : Fin d, ∑ j : Fin d, M j i *
      ∫ y, sa16q_K1E s 0 i y * (aN N (x - y) * fderiv ℝ u (x - y) (EuclideanSpace.single j (1 : ℝ))) :=
    fun N => by
      obtain ⟨B1N, hB1N⟩ := hbd1 N
      exact sa16q_F_pointwise hd hs hs2 M (haN1 N) (hbd N) hB1N u x
  simp_rw [h1]
  rw [sa16q_F_pointwise hd hs hs2 M ha1 hB0 hB1 u x]
  refine tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => ?_
  refine Tendsto.const_mul _ ?_
  set e : Euc d := EuclideanSpace.single j (1 : ℝ) with he
  have hfdc : Continuous (fun y : Euc d => fderiv ℝ (⇑u) (x - y) e) :=
    ((u.smooth'.continuous_fderiv (by simp)).comp (continuous_const.sub continuous_id)).clm_apply
      continuous_const
  -- the dominating function `‖K1_i(y) ∂_j u (x-y)‖ B0`
  have hhj : Integrable (fun y => sa16q_K1E s 0 i y * fderiv ℝ (⇑u) (x - y) e) := by
    obtain ⟨C2, hC2, hd2, hc2, hD2, hD2'⟩ := sa16q_schwartz_hyp (sa16q_dS e u)
    have := sa16q_conv_integrable (sa16q_K1E_meas s 0 i) (sa16q_K1E_WI hd hs hs2 i) hC2
      (sa16q_dS e u).continuous hD2 x
    exact this.congr (Eventually.of_forall fun y => by simp only [sa16q_dS_apply])
  refine tendsto_integral_of_dominated_convergence
    (fun y => ‖sa16q_K1E s 0 i y * fderiv ℝ (⇑u) (x - y) e‖ * B0)
    (fun N => ?_) (hhj.norm.mul_const B0) (fun N => ?_) ?_
  · exact (sa16q_K1E_meas s 0 i).aestronglyMeasurable.mul
      (((haN1 N).continuous.comp (continuous_const.sub continuous_id)).mul hfdc).aestronglyMeasurable
  · refine Eventually.of_forall fun y => ?_
    calc ‖sa16q_K1E s 0 i y * (aN N (x - y) * fderiv ℝ (⇑u) (x - y) e)‖
        = ‖sa16q_K1E s 0 i y‖ * (‖aN N (x - y)‖ * ‖fderiv ℝ (⇑u) (x - y) e‖) := by
          rw [norm_mul, norm_mul]
      _ ≤ ‖sa16q_K1E s 0 i y‖ * (B0 * ‖fderiv ℝ (⇑u) (x - y) e‖) := by
          gcongr
          simpa [Real.norm_eq_abs] using hbd N (x - y)
      _ = ‖sa16q_K1E s 0 i y * fderiv ℝ (⇑u) (x - y) e‖ * B0 := by
          rw [norm_mul]; ring
  · refine Eventually.of_forall fun y => ?_
    exact ((hlim (x - y)).mul_const _).const_mul _

end Fin1

end HRS.Whole.AppendixA.Phase2SA16Q
