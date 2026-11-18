import HRS.MS.SA16ZL7

/-!
# S.A.16 (SA16Z) B1: `P_a ψ` in principal value form and its `L^p` bound by `W^{2,p}`-jets (`1 < θ < 2`)

`sa16z_P_pv`: `P_a ψ = -c_s ∑_i pvOdd_i (a ∂_i ψ)`;
`sa16z_P_Lp`: `‖P_a ψ‖_p ≤ C (B_a + L_a) ∑_{i} (‖∂_i ψ‖_p + ∑_l ‖∂_l ∂_i ψ‖_p)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA

section B1
variable {d : ℕ} {s : ℝ}

theorem sa16z_P_pv (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {a ψ : Euc d → ℝ} (ha : ContDiff ℝ ∞ a)
    (hψ : IsCcInfty ψ) (x : Euc d) :
    sa16z_P s a ψ x = -(HRS.CZ.Hls.hlsg_c s) *
      ∑ i : Fin d, pvOdd d (s + 2 - d) (fun u : Euc d => u i) (sa16z_src a ψ i) x := by
  unfold sa16z_P
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact sa16z_conv_fderiv_pvOdd hd hs0 hsd (sa16z_src_cc ha hψ i) i x

lemma sa16z_fderiv_src_bound {a ψ : Euc d → ℝ} (ha : ContDiff ℝ ∞ a) (hψ : IsCcInfty ψ) {Ba La : ℝ}
    (hab : ∀ y, |a y| ≤ Ba) (hLa : ∀ y, ‖fderiv ℝ a y‖ ≤ La) (i : Fin d) (y : Euc d) :
    ‖fderiv ℝ (sa16z_src a ψ i) y‖ ≤
      La * ‖fderiv ℝ ψ y (sa16z_e i)‖ + Ba * ‖fderiv ℝ (fun z => fderiv ℝ ψ z (sa16z_e i)) y‖ := by
  have hd1 : DifferentiableAt ℝ a y := (ha.differentiable (by simp)) y
  have hd2 : DifferentiableAt ℝ (fun z => fderiv ℝ ψ z (sa16z_e i)) y :=
    ((sa16so_dir_smooth hψ.1 (sa16z_e i)).differentiable (by simp)) y
  have : sa16z_src a ψ i = fun z => a z * fderiv ℝ ψ z (sa16z_e i) := rfl
  rw [this, fderiv_fun_mul hd1 hd2]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm (|fderiv ℝ ψ y (sa16z_e i)|)]
  have h1 := hab y
  have h2 := hLa y
  have hn1 : 0 ≤ ‖fderiv ℝ a y‖ := norm_nonneg _
  have hn2 : 0 ≤ ‖fderiv ℝ (fun z => fderiv ℝ ψ z (sa16z_e i)) y‖ := norm_nonneg _
  have hn3 := abs_nonneg (fderiv ℝ ψ y (sa16z_e i))
  have hn4 := abs_nonneg (a y)
  nlinarith [mul_le_mul_of_nonneg_right h2 hn3, mul_le_mul_of_nonneg_right h1 hn2]

end B1

end HRS.Whole.AppendixA.Phase2SA16R
