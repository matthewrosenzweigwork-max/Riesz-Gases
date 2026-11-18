import HRS.MS.SA16ZL4

/-!
# S.A.16 (SA16Z) L5: `‖pvOdd_i f‖_p ≤ C (‖f‖_p + ‖∇f‖_p)` for `1 < θ < 2`, `f ∈ C_c^∞`

The pointwise difference representation (`pvOdd_eq_of_C1`) splits `pvOdd f = near + far`; the far kernel is in `L^1`
(`θ > 1`), the near part is estimated by `sa16z_near_Lp`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA

section L5
variable {d : ℕ}

open HRS.CZ.Pv in
lemma sa16z_kappa_fin (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) (i : Fin d) :
    ∫⁻ z, (closedBall (0 : Euc d) 1).indicator (fun z => ‖pvK d θ (fun u : Euc d => u i) z‖ₑ * ‖z‖ₑ) z ≠ ⊤ := by
  have hK := isPvKernel_coord (d := d) i
  have hint := HRS.S16Frac.s16frac_integrableOn_ball_rpow (d := d) hd (α := (d : ℝ) + θ - 2)
    (by linarith) 2
  have hfin : ∫⁻ z in ball (0 : Euc d) 2, ‖‖z‖ ^ (-((d : ℝ) + θ - 2))‖ₑ < ⊤ := hint.2
  refine ne_top_of_le_ne_top hfin.ne ?_
  rw [← lintegral_indicator measurableSet_ball]
  refine lintegral_mono fun z => ?_
  by_cases hz : z ∈ closedBall (0 : Euc d) 1
  · have hz2 : z ∈ ball (0 : Euc d) 2 := by
      simp only [mem_closedBall, mem_ball, dist_zero_right] at hz ⊢; linarith
    rw [indicator_of_mem hz, indicator_of_mem hz2]
    by_cases hz0 : z = 0
    · subst hz0; simp [pvK_zero hd hθ0]
    · have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
      have h1 := pvK_abs_le hd hθ0 hK z
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, ← ofReal_norm_eq_enorm z,
        ← ENNReal.ofReal_mul (abs_nonneg _), abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc |pvK d θ (fun u : Euc d => u i) z| * ‖z‖ ≤ (1 * ‖z‖ ^ (1 - ((d : ℝ) + θ))) * ‖z‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖z‖ ^ (-((d : ℝ) + θ - 2)) := by
            rw [one_mul, ← Real.rpow_add_one hzpos.ne']; congr 1; ring
  · rw [indicator_of_notMem hz]; exact zero_le

open HRS.CZ.Pv in
lemma sa16z_kf_fin (hd : 1 ≤ d) {θ : ℝ} (hθ1 : 1 < θ) (i : Fin d) :
    ∫⁻ z, {z : Euc d | 1 < ‖z‖}.indicator (fun z => ‖pvK d θ (fun u : Euc d => u i) z‖ₑ) z ≠ ⊤ := by
  have hK := isPvKernel_coord (d := d) i
  have hint := pvapi_integrableOn_tail_rpow (d := d) hd (s := (d : ℝ) + θ - 1) (by linarith)
  have hfin : ∫⁻ z in {z : Euc d | 1 < ‖z‖}, ‖‖z‖ ^ (-((d : ℝ) + θ - 1))‖ₑ < ⊤ := hint.2
  have hS : MeasurableSet {z : Euc d | 1 < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  refine ne_top_of_le_ne_top hfin.ne ?_
  rw [← lintegral_indicator hS]
  refine lintegral_mono fun z => ?_
  by_cases hz : z ∈ {z : Euc d | 1 < ‖z‖}
  · rw [indicator_of_mem hz, indicator_of_mem hz]
    have hz1 : 1 < ‖z‖ := hz
    have hzpos : 0 < ‖z‖ := by linarith
    have h1 := pvK_abs_le hd (by linarith : 0 < θ) hK z
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc |pvK d θ (fun u : Euc d => u i) z| ≤ 1 * ‖z‖ ^ (1 - ((d : ℝ) + θ)) := h1
      _ = _ := by rw [one_mul]; congr 1; ring
  · rw [indicator_of_notMem hz]; exact zero_le

end L5

end HRS.Whole.AppendixA.Phase2SA16R
