import HRS.MS.R26T8AP10a10

/-!
# S8.2 T8A P10a (part 11): the principal-value form of `∫ |x-u|^(-s) div h`
`r26t8a_p10a_core`: for `h` as in `R26P10Hyp`, `0 < s < d`, `x ≠ y`:
`|x-u|^(-s) div h(u)` is integrable and its integral equals `∫ Ecan0 s h x u`, the cancellation form of `∫ ∇g(x-u)·h(u) du`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_p10a_hnorm_int {y : Euc d} {τ : ℝ} {h : Euc d → Euc d} (H : R26P10Hyp d y τ h) :
    Integrable (fun u => ‖h u‖) := by
  have hm : AEStronglyMeasurable (fun u => ‖h u‖) volume :=
    r26t8a_p10a_aesm H.hd y (H.C1.continuousOn.norm)
  exact r26t8a_p10a_gp_integrable (y := y) (τ := τ) H.hd H.τ0 (by linarith [H.τd]) H.hb hm

theorem r26t8a_p10a_F2_int {y : Euc d} {τ : ℝ} {h : Euc d → Euc d} (H : R26P10Hyp d y τ h)
    {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) (x : Euc d) :
    Integrable (fun u => ∑ j : Fin d, r26t8a_dkeps s ε (x - u) j * h u j) := by
  have hd := H.hd
  have hD : ∀ (w : Euc d) (j : Fin d), |r26t8a_dkeps s ε w j| ≤ s * (ε ^ 2) ^ (-s / 2 - 1 / 2) :=
    fun w j => r26t8a_dkeps_le_const hs hε w j
  have gF2 : R26P10GP y τ (fun u => ∑ j : Fin d, r26t8a_dkeps s ε (x - u) j * h u j) :=
    r26t8a_p10a_gp_of_bound (B := s * (ε ^ 2) ^ (-s / 2 - 1 / 2) * d) H.hb (by positivity)
      (fun u _ => by
        rw [abs_of_nonneg (norm_nonneg _)]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ j : Fin d, |r26t8a_dkeps s ε (x - u) j * h u j|
            ≤ ∑ j : Fin d, s * (ε ^ 2) ^ (-s / 2 - 1 / 2) * ‖h u‖ := by
              refine Finset.sum_le_sum fun j _ => ?_
              rw [abs_mul]
              exact mul_le_mul (hD _ j) (r26t8a_abs_coord_le _ _) (abs_nonneg _) (by positivity)
          _ = _ := by simp; ring)
  have F2meas : AEStronglyMeasurable
      (fun u => ∑ j : Fin d, r26t8a_dkeps s ε (x - u) j * h u j) volume := by
    refine r26t8a_p10a_aesm hd y ?_
    refine continuousOn_finset_sum _ fun j _ => ?_
    have hdc : Continuous fun u : Euc d => r26t8a_dkeps s ε (x - u) j :=
      (r26t8a_dkeps_continuous s ε hε j).comp (continuous_const.sub continuous_id)
    have hj : Continuous fun v : Euc d => v j := (EuclideanSpace.proj j).continuous
    exact hdc.continuousOn.mul (hj.comp_continuousOn H.C1.continuousOn)
  exact r26t8a_p10a_gp_integrable (y := y) (τ := τ) hd H.τ0 (by linarith [H.τd]) gF2 F2meas

/-- Oddness: the cancellation integral equals the plain one. -/
theorem r26t8a_p10a_Ecan_integral {y : Euc d} {τ : ℝ} {h : Euc d → Euc d} (H : R26P10Hyp d y τ h)
    {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) (x : Euc d) :
    Integrable (r26t8a_Ecan s ε h x) ∧
    ∫ u, r26t8a_Ecan s ε h x u = ∫ u, ∑ j : Fin d, r26t8a_dkeps s ε (x - u) j * h u j := by
  have hF2 := r26t8a_p10a_F2_int H hs hε x
  set T : Euc d → ℝ := fun u => ∑ j : Fin d, h x j * (closedBall (0 : Euc d) (1 / 4)).indicator
      (fun w => r26t8a_dkeps s ε w j) (x - u) with hT
  have hTi : Integrable T := integrable_finset_sum _ fun j _ =>
    ((r26t8a_p10a_odd s hε hs x j).1).const_mul (h x j)
  have hT0 : ∫ u, T u = 0 := by
    rw [hT, integral_finset_sum _ fun j _ => ((r26t8a_p10a_odd s hε hs x j).1).const_mul (h x j)]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_const_mul, (r26t8a_p10a_odd s hε hs x j).2, mul_zero]
  have hpt : ∀ u, r26t8a_Ecan s ε h x u = (∑ j : Fin d, r26t8a_dkeps s ε (x - u) j * h u j) - T u := by
    intro u
    unfold r26t8a_Ecan
    by_cases hc : ‖x - u‖ ≤ 1 / 4
    · have hm : x - u ∈ closedBall (0 : Euc d) (1 / 4) := by simpa using hc
      rw [if_pos hc, hT]
      simp only [Set.indicator_of_mem hm, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · have hm : x - u ∉ closedBall (0 : Euc d) (1 / 4) := by simpa using hc
      rw [if_neg hc, hT]
      simp only [Set.indicator_of_notMem hm, mul_zero, Finset.sum_const_zero, sub_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
  have hE : Integrable (r26t8a_Ecan s ε h x) := by
    have := hF2.sub hTi
    exact this.congr (Filter.Eventually.of_forall fun u => (hpt u).symm)
  refine ⟨hE, ?_⟩
  have : r26t8a_Ecan s ε h x = fun u => (∑ j : Fin d, r26t8a_dkeps s ε (x - u) j * h u j) - T u :=
    funext hpt
  rw [this, integral_sub hF2 hTi, hT0, sub_zero]

end HRS.MS.R26T8A
