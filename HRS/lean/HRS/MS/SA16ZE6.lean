import HRS.MS.SA16ZE5

/-!
# S.A.16 (SA16Z) E6: integrability of the pairing integrands
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section E6
variable {d : ℕ} {s : ℝ}

lemma sa16z_pv_cont (hd : 1 ≤ d) {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) {φ : Euc d → ℝ} (hφ : IsCcInfty φ)
    (l : Fin d) {j : ℕ} (κ : Fin j → Fin d) : Continuous (sa16z_pv d θ l (partialDeriv κ φ)) :=
  HRS.CZ.Asm15.asm15_pvOdd_continuous hd hθ1 hθ2 l (sa16z_Wt hφ j κ)

lemma sa16z_cc_mul_int {f g h : Euc d → ℝ} (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hgs : HasCompactSupport g) : Integrable (fun x => f x * (g x * h x)) := by
  refine (hf.mul (hg.mul hh)).integrable_of_hasCompactSupport ?_
  exact (hgs.mul_right (f' := h)).mul_left

lemma sa16z_I_int (hs0 : 0 ≤ s) (hsd : s < d) {μ φ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) (hφ : IsCcInfty φ)
    {p : ℝ} (hp : 2 ≤ p) (j : ℕ) :
    Integrable (fun x => sa16sz_vn φ j x ^ (p - 2) *
      ∑ idx : Fin j → Fin d, partialDeriv idx φ x * partialDeriv idx (sa16z_P s μ φ) x) := by
  simp_rw [Finset.mul_sum]
  refine integrable_finset_sum _ fun idx _ => ?_
  exact sa16z_cc_mul_int (sa16sz_vn_pow_cont φ hφ.1 j (by linarith)) (sa16j_pd_smooth hφ.1 idx).continuous
    (sa16j_pd_smooth (sa16z_P_smooth hs0 hsd hμ hφ) idx).continuous (sa16s_cc_partialDeriv hφ idx).2

lemma sa16z_IBd_int (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) {μ φ : Euc d → ℝ}
    (hμ : ContDiff ℝ ∞ μ) (hφ : IsCcInfty φ) {p : ℝ} (hp : 2 ≤ p) (cA cs : ℝ) (l : Fin d) (j : ℕ) :
    Integrable (sa16z_IBd cA cs μ φ p (s + 2 - d) l j) := by
  have hθ2 : s + 2 - (d : ℝ) < 2 := by linarith
  unfold sa16z_IBd
  simp_rw [Finset.mul_sum]
  refine integrable_finset_sum _ fun idx _ => ?_
  refine sa16z_cc_mul_int (sa16sz_vn_pow_cont φ hφ.1 j (by linarith)) (sa16j_pd_smooth hφ.1 idx).continuous
    ?_ (sa16s_cc_partialDeriv hφ idx).2
  have hdm : ∀ a : Fin d, Continuous (sa16z_dm μ a) := fun a => (sa16z_dm_smooth hμ a).continuous
  refine (continuous_const.mul ((hdm l).mul (sa16z_pv_cont hd hθ1 hθ2 hφ l idx))).sub
    (continuous_const.mul ?_)
  cases j with
  | zero => simp only [sa16z_Q]; exact continuous_const
  | succ n =>
    simp only [sa16z_Q]
    exact continuous_finsetSum _ fun q _ => (hdm _).mul (sa16z_pv_cont hd hθ1 hθ2 hφ l _)

end E6

end HRS.Whole.AppendixA.Phase2SA16R
