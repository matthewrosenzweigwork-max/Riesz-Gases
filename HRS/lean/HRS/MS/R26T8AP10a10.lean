import HRS.MS.R26T8AP10a9

/-!
# S8.2 T8A P10a (part 10): the cancellation form of the force pairing and its `ε → 0` limit
`Ecan s ε`: `∑_j (h_j(u) - h_j(x) 1_{|x-u| ≤ 1/4}) ∂_j k_ε(x-u)`.  Dominated by an explicit integrable function.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

def r26t8a_Ecan (s ε : ℝ) (h : Euc d → Euc d) (x u : Euc d) : ℝ :=
  if ‖x - u‖ ≤ 1 / 4 then ∑ j : Fin d, (h u j - h x j) * r26t8a_dkeps s ε (x - u) j
  else ∑ j : Fin d, h u j * r26t8a_dkeps s ε (x - u) j

/-- The limit integrand (`ε = 0`, i.e. the actual force `-s (x-u)_j |x-u|^(-s-2)`). -/
def r26t8a_Ecan0 (s : ℝ) (h : Euc d → Euc d) (x u : Euc d) : ℝ :=
  if ‖x - u‖ ≤ 1 / 4 then ∑ j : Fin d, (h u j - h x j) * (-s * (x - u) j * ‖x - u‖ ^ (-s - 2))
  else ∑ j : Fin d, h u j * (-s * (x - u) j * ‖x - u‖ ^ (-s - 2))

theorem r26t8a_p10a_dot_le (a : Euc d) (c : Fin d → ℝ) {M : ℝ} (hc : ∀ j, |c j| ≤ M) :
    |∑ j : Fin d, a j * c j| ≤ d * (‖a‖ * M) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j : Fin d, |a j * c j| ≤ ∑ j : Fin d, ‖a‖ * M := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (r26t8a_abs_coord_le a j) (hc j) (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp

theorem r26t8a_p10a_aesm_ite {x : Euc d} {A B : Euc d → ℝ} (hA : AEStronglyMeasurable A volume)
    (hB : AEStronglyMeasurable B volume) :
    AEStronglyMeasurable (fun u => if ‖x - u‖ ≤ 1 / 4 then A u else B u) volume := by
  have hs : MeasurableSet {u : Euc d | ‖x - u‖ ≤ 1 / 4} :=
    measurableSet_le (measurable_const.sub measurable_id).norm measurable_const
  have := AEStronglyMeasurable.piecewise (s := {u : Euc d | ‖x - u‖ ≤ 1 / 4}) hs hA.restrict hB.restrict
  exact this

/-- Pointwise bound for `Ecan` by the three-term dominator. -/
theorem r26t8a_p10a_Ecan_bound {s : ℝ} (hs : 0 < s) {ε : ℝ} (hε : 0 < ε) {h : Euc d → Euc d} {x : Euc d}
    {r1 : ℝ} (hr1 : 0 < r1) (hr14 : r1 ≤ 1 / 4) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ u : Euc d, ‖u - x‖ < r1 → ‖h u - h x‖ ≤ L * ‖u - x‖) {u : Euc d} (hu : u ≠ x) :
    |r26t8a_Ecan s ε h x u| ≤
      (ball x r1).indicator (fun u => d * s * L * ‖u - x‖ ^ (-s)) u +
      d * s * r1 ^ (-s - 1) * ‖h u‖ +
      (ball x (1 / 2)).indicator (fun _ => d * s * r1 ^ (-s - 1) * ‖h x‖) u := by
  have hρ : 0 < ‖x - u‖ := norm_pos_iff.2 (sub_ne_zero.2 hu.symm)
  have hρ' : ‖x - u‖ = ‖u - x‖ := norm_sub_rev _ _
  have hdk : ∀ j, |r26t8a_dkeps s ε (x - u) j| ≤ s * ‖x - u‖ ^ (-s - 1) :=
    fun j => r26t8a_dkeps_le hs hε (sub_ne_zero.2 hu.symm) j
  have hp1 : 0 ≤ (ball x r1).indicator (fun u => d * s * L * ‖u - x‖ ^ (-s)) u :=
    Set.indicator_nonneg (fun v _ => by positivity) u
  have hp2 : 0 ≤ d * s * r1 ^ (-s - 1) * ‖h u‖ := by positivity
  have hp3 : 0 ≤ (ball x (1 / 2)).indicator (fun _ => d * s * r1 ^ (-s - 1) * ‖h x‖) u :=
    Set.indicator_nonneg (fun v _ => by positivity) u
  have hbig : ‖x - u‖ ^ (-s - 1) ≤ r1 ^ (-s - 1) ∨ ‖x - u‖ < r1 := by
    by_cases h' : r1 ≤ ‖x - u‖
    · exact Or.inl (Real.rpow_le_rpow_of_nonpos hr1 h' (by linarith))
    · exact Or.inr (not_le.1 h')
  unfold r26t8a_Ecan
  by_cases hc : ‖x - u‖ ≤ 1 / 4
  · rw [if_pos hc]
    have e1 : |∑ j : Fin d, (h u j - h x j) * r26t8a_dkeps s ε (x - u) j| ≤
        d * (‖h u - h x‖ * (s * ‖x - u‖ ^ (-s - 1))) := by
      have := r26t8a_p10a_dot_le (h u - h x) (fun j => r26t8a_dkeps s ε (x - u) j) hdk
      simpa using this
    rcases hbig with hb | hb
    · -- far from x inside the ball
      have hm : u ∈ ball x (1 / 2) := by
        simp only [mem_ball_iff_norm, dist_eq_norm]; rw [← hρ']; linarith [hc]
      rw [Set.indicator_of_mem hm]
      refine e1.trans ?_
      have h3 : ‖h u - h x‖ ≤ ‖h u‖ + ‖h x‖ := norm_sub_le _ _
      calc (d : ℝ) * (‖h u - h x‖ * (s * ‖x - u‖ ^ (-s - 1)))
          ≤ d * ((‖h u‖ + ‖h x‖) * (s * r1 ^ (-s - 1))) := by
            gcongr
        _ = d * s * r1 ^ (-s - 1) * ‖h u‖ + d * s * r1 ^ (-s - 1) * ‖h x‖ := by ring
        _ ≤ _ := by linarith
    · -- close to x: Lipschitz
      have hm : u ∈ ball x r1 := by
        simp only [mem_ball_iff_norm, dist_eq_norm]; rw [← hρ']; exact hb
      rw [Set.indicator_of_mem hm]
      refine e1.trans ?_
      have h3 := hlip u (by rw [← hρ']; exact hb)
      have h4 : ‖x - u‖ * ‖x - u‖ ^ (-s - 1) = ‖x - u‖ ^ (-s) := by
        rw [← Real.rpow_one_add' hρ.le (by linarith)]; congr 1; ring
      calc (d : ℝ) * (‖h u - h x‖ * (s * ‖x - u‖ ^ (-s - 1)))
          ≤ d * ((L * ‖u - x‖) * (s * ‖x - u‖ ^ (-s - 1))) := by gcongr
        _ = d * s * L * ‖u - x‖ ^ (-s) := by
            rw [← hρ', ← h4]; ring
        _ ≤ _ := by linarith
  · rw [if_neg hc]
    have hr : ‖x - u‖ ^ (-s - 1) ≤ r1 ^ (-s - 1) :=
      Real.rpow_le_rpow_of_nonpos hr1 (by linarith [not_le.1 hc]) (by linarith)
    have e1 : |∑ j : Fin d, h u j * r26t8a_dkeps s ε (x - u) j| ≤
        d * (‖h u‖ * (s * ‖x - u‖ ^ (-s - 1))) :=
      r26t8a_p10a_dot_le (h u) (fun j => r26t8a_dkeps s ε (x - u) j) hdk
    refine e1.trans ?_
    calc (d : ℝ) * (‖h u‖ * (s * ‖x - u‖ ^ (-s - 1))) ≤ d * (‖h u‖ * (s * r1 ^ (-s - 1))) := by gcongr
      _ = d * s * r1 ^ (-s - 1) * ‖h u‖ := by ring
      _ ≤ _ := by linarith

end HRS.MS.R26T8A
