import HRS.MS.R26T8AO00c

/-!
# S8.2 observed-time layer, packet T8A.O00 (helper d): singular integrals against a bounded density

`1_{|z|<1} |z|^(-s)` has finite Lebesgue integral for `0 < s < d`, and a bounded density `ρ` gives
`∫ ρ(y) (ind(x-y) + 2) dy ≤ M ∫ ind + 2` uniformly in `x`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole

theorem r26t8a_o00d_ball_lt_top {d : ℕ} {s : ℝ} (hsd : s < d) (hd1 : 1 ≤ d) :
    ∫⁻ z : Euc d, ENNReal.ofReal ((Metric.ball (0 : Euc d) 1).indicator (fun z => ‖z‖ ^ (-s)) z) < ⊤ := by
  have hfin : 1 ≤ Module.finrank ℝ (Euc d) := by
    rw [finrank_euclideanSpace_fin]; exact hd1
  have hα : s < (Module.finrank ℝ (Euc d) : ℝ) := by
    rw [finrank_euclideanSpace_fin]; exact hsd
  have hmeas : AEStronglyMeasurable (fun z : Euc d => ‖z‖ ^ (-s)) volume :=
    ((measurable_norm.pow_const (-s))).aestronglyMeasurable
  have hon : IntegrableOn (fun z : Euc d => ‖z‖ ^ (-s)) (Metric.ball (0 : Euc d) 1) volume :=
    integrableOn_ball_of_norm_le_rpow hfin hα
      (Filter.Eventually.of_forall fun x => by
        rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)])
      hmeas
  have hI : Integrable ((Metric.ball (0 : Euc d) 1).indicator (fun z => ‖z‖ ^ (-s))) volume :=
    (integrable_indicator_iff measurableSet_ball).2 hon
  exact hI.lintegral_lt_top

theorem r26t8a_o00d_dens_bound {d : ℕ} (ρ : Euc d → ℝ) (hρm : Measurable ρ) (M : ℝ)
    (hρM : ∀ y, ρ y ≤ M) (hρ1 : ∫⁻ y, ENNReal.ofReal (ρ y) = 1) (ind : Euc d → ℝ)
    (hindm : Measurable ind) (x : Euc d) :
    ∫⁻ y, ENNReal.ofReal (ρ y) * (ENNReal.ofReal (ind (x - y)) + 2) ≤
      ENNReal.ofReal M * (∫⁻ z, ENNReal.ofReal (ind z)) + 2 := by
  have hindx : Measurable (fun y : Euc d => ENNReal.ofReal (ind (x - y))) :=
    ENNReal.measurable_ofReal.comp (hindm.comp (measurable_const.sub measurable_id))
  have hρE : Measurable (fun y : Euc d => ENNReal.ofReal (ρ y)) :=
    ENNReal.measurable_ofReal.comp hρm
  calc ∫⁻ y, ENNReal.ofReal (ρ y) * (ENNReal.ofReal (ind (x - y)) + 2)
      ≤ ∫⁻ y, (ENNReal.ofReal M * ENNReal.ofReal (ind (x - y)) + 2 * ENNReal.ofReal (ρ y)) := by
        refine lintegral_mono fun y => ?_
        rw [mul_add]
        refine add_le_add (by gcongr; exact hρM y) ?_
        rw [mul_comm]
    _ = (∫⁻ y, ENNReal.ofReal M * ENNReal.ofReal (ind (x - y))) +
          ∫⁻ y, 2 * ENNReal.ofReal (ρ y) := by
        exact lintegral_add_left (measurable_const.mul hindx) _
    _ = ENNReal.ofReal M * (∫⁻ y, ENNReal.ofReal (ind (x - y))) + 2 * ∫⁻ y, ENNReal.ofReal (ρ y) := by
        rw [lintegral_const_mul _ hindx, lintegral_const_mul _ hρE]
    _ = ENNReal.ofReal M * (∫⁻ z, ENNReal.ofReal (ind z)) + 2 := by
        rw [lintegral_sub_left_eq_self (fun z => ENNReal.ofReal (ind z)) x, hρ1, mul_one]

end HRS.MS.R26T8A

end
