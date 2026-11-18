import HRS.MS.WadAux54

/-!
# S8.3, packet S8D-2 (essential spectral radius), part 1: decay of the thermal force

`s8d_force_decay`: for a density `ρ` with Gaussian bounds (`s84_GaussReg`) and `d ≥ 2`, the cancellation
convolution `D(x) = convGradConvW (∇g_{d/2}) ρ x` (the mean-field force `∇g*ρ`) tends to `0` as `‖x‖ → ∞`.
This is the decay of the coefficient `D` of the first order remainder `𝓑` of the generator, the input for the
bound `‖𝓑 h‖ ≤ ε ⟨x⟩^M + C_ε` at infinity.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.MS.Wad

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

theorem s8d_tail_tendsto (d : ℕ) :
    Tendsto (fun r : ℝ => ∫ y : Euc d, (if r ≤ ‖y‖ then (1 + ‖y‖) ^ (-((d : ℝ) + 1)) else 0)) atTop
      (𝓝 0) := by
  have := tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure (Euc d)))
    (l := atTop) (F := fun (r : ℝ) (y : Euc d) => if r ≤ ‖y‖ then (1 + ‖y‖) ^ (-((d : ℝ) + 1)) else 0)
    (f := fun _ => (0 : ℝ)) (fun y => (1 + ‖y‖) ^ (-((d : ℝ) + 1)))
    (Eventually.of_forall fun r => ?_) (Eventually.of_forall fun r => Eventually.of_forall fun y => ?_)
    (s84_int_far d) (Eventually.of_forall fun y => ?_)
  · simpa using this
  · refine Measurable.aestronglyMeasurable ?_
    refine Measurable.ite (measurableSet_le measurable_const measurable_norm) ?_ measurable_const
    exact (by fun_prop : Measurable fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1)))
  · by_cases h : r ≤ ‖y‖
    · simp only [h, ↓reduceIte, Real.norm_eq_abs]
      exact le_of_eq (abs_of_nonneg (Real.rpow_nonneg (by positivity) _))
    · simp only [h, ↓reduceIte, norm_zero]
      exact Real.rpow_nonneg (by positivity) _
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop ‖y‖] with r hr
    simp [not_le.2 hr]

end HRS.MS.Wad
