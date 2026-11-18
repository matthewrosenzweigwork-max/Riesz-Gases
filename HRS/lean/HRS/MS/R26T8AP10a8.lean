import HRS.MS.R26T8AP10a7

/-!
# S8.2 T8A P10a (part 8): integrability of `|x-u|^(-s) div h(u)` (two poles)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_p10a_divh_gp {y : Euc d} {τ : ℝ} {h : Euc d → Euc d} (H : R26P10Hyp d y τ h) :
    R26P10GP y (τ + 1) (r26t8a_divh h) :=
  r26t8a_p10a_gp_of_bound (B := d) H.hdb (by positivity) (fun u _ => by
    rw [abs_of_nonneg (norm_nonneg _)]; exact r26t8a_divh_le h u)

theorem r26t8a_p10a_divh_int {y : Euc d} {τ : ℝ} {h : Euc d → Euc d} (H : R26P10Hyp d y τ h) :
    Integrable (r26t8a_divh h) :=
  r26t8a_p10a_gp_integrable (y := y) (τ := τ + 1) H.hd (by linarith [H.τ0]) (by linarith [H.τd])
    (r26t8a_p10a_divh_gp H) (r26t8a_p10a_aesm H.hd y (r26t8a_divh_continuousOn H.C1))

theorem r26t8a_p10a_xpole_int {y : Euc d} {τ : ℝ} {h : Euc d → Euc d} (H : R26P10Hyp d y τ h)
    {s : ℝ} (hs : 0 < s) (hsd : s < d) {x : Euc d} (hxy : x ≠ y) :
    Integrable (fun u => ‖x - u‖ ^ (-s) * r26t8a_divh h u) := by
  have hd := H.hd
  have hn : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  obtain ⟨r0, hr0⟩ : ∃ r0 : ℝ, r0 = ‖x - y‖ / 2 := ⟨_, rfl⟩
  have hr0p : 0 < r0 := by rw [hr0]; positivity
  have hmeas : AEStronglyMeasurable (fun u => ‖x - u‖ ^ (-s) * r26t8a_divh h u) volume := by
    have h1 : Measurable fun u : Euc d => ‖x - u‖ ^ (-s) := (measurable_const.sub measurable_id).norm.pow_const _
    exact h1.aestronglyMeasurable.mul (r26t8a_p10a_aesm hd y (r26t8a_divh_continuousOn H.C1))
  have hint := r26t8a_p10a_divh_int H
  obtain ⟨C, c, hC0, hc, hh⟩ := H.hdb
  -- near `x`
  have hnear : IntegrableOn (fun u => ‖x - u‖ ^ (-s) * r26t8a_divh h u) (ball x r0) := by
    have hp := (r26t8a_p10a_pole_on hd hs hsd x hr0p).const_mul (d * C * (1 + r0 ^ (-(τ + 1))))
    refine Integrable.mono' hp hmeas.restrict ?_
    refine (ae_restrict_iff' measurableSet_ball).2 (Filter.Eventually.of_forall fun u hu => ?_)
    have hu' : ‖u - x‖ < r0 := by simpa [mem_ball_iff_norm, dist_eq_norm] using hu
    have hne : u ≠ y := by
      intro e; subst e
      rw [norm_sub_rev] at hu'; linarith
    have h1 : r0 ≤ ‖u - y‖ := by
      have := norm_sub_norm_le (x - y) (x - u)
      have e2 : x - y - (x - u) = u - y := by abel
      rw [e2] at this
      rw [norm_sub_rev x u] at this
      rw [hr0]; linarith
    have h2 : ‖u - y‖ ^ (-(τ + 1)) ≤ r0 ^ (-(τ + 1)) :=
      Real.rpow_le_rpow_of_nonpos hr0p h1 (by linarith [H.τ0])
    have hE : Real.exp (-c * ‖u‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖u‖])
    have hdv : |r26t8a_divh h u| ≤ d * C * (1 + r0 ^ (-(τ + 1))) := by
      refine (r26t8a_divh_le h u).trans ?_
      have := hh u hne
      rw [abs_of_nonneg (norm_nonneg _)] at this
      have h3 : C * Real.exp (-c * ‖u‖ ^ 2) * (1 + ‖u - y‖ ^ (-(τ + 1))) ≤ C * (1 + r0 ^ (-(τ + 1))) := by
        have := mul_le_mul_of_nonneg_left hE hC0
        have h4 : 0 ≤ 1 + ‖u - y‖ ^ (-(τ + 1)) := by positivity
        calc C * Real.exp (-c * ‖u‖ ^ 2) * (1 + ‖u - y‖ ^ (-(τ + 1))) ≤ C * 1 * (1 + ‖u - y‖ ^ (-(τ + 1))) :=
              mul_le_mul_of_nonneg_right this h4
          _ ≤ C * (1 + r0 ^ (-(τ + 1))) := by nlinarith
      calc (d : ℝ) * ‖fderiv ℝ h u‖ ≤ d * (C * Real.exp (-c * ‖u‖ ^ 2) * (1 + ‖u - y‖ ^ (-(τ + 1)))) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ ≤ d * (C * (1 + r0 ^ (-(τ + 1)))) := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = _ := by ring
    rw [Real.norm_eq_abs, abs_mul, norm_sub_rev x u]
    rw [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    calc ‖u - x‖ ^ (-s) * |r26t8a_divh h u| ≤ ‖u - x‖ ^ (-s) * (d * C * (1 + r0 ^ (-(τ + 1)))) :=
          mul_le_mul_of_nonneg_left hdv (Real.rpow_nonneg (norm_nonneg _) _)
      _ = _ := by ring
  -- away from `x`
  have hfar : IntegrableOn (fun u => ‖x - u‖ ^ (-s) * r26t8a_divh h u) (ball x r0)ᶜ := by
    refine Integrable.mono' (hint.norm.const_mul (r0 ^ (-s))).integrableOn hmeas.restrict ?_
    refine (ae_restrict_iff' measurableSet_ball.compl).2 (Filter.Eventually.of_forall fun u hu => ?_)
    have hu' : r0 ≤ ‖x - u‖ := by
      simpa [mem_ball_iff_norm, dist_eq_norm, not_lt, norm_sub_rev] using hu
    have h2 : ‖x - u‖ ^ (-s) ≤ r0 ^ (-s) := Real.rpow_le_rpow_of_nonpos hr0p hu' (by linarith)
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  have := hnear.union hfar
  rwa [Set.union_compl_self, integrableOn_univ] at this

end HRS.MS.R26T8A
