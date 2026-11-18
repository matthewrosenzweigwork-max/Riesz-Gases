import HRS.MS.S111TermAux10
import HRS.MS.R26T6CI07Response

/-!
# S11.1 I07: cubic moment bound for a centered Lipschitz observable

No prior integrability of f is assumed; it follows from Lipschitz
continuity and the third spatial moment of the probability measure.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
namespace HRS.MS.R26T6C
open HRS HRS.Whole
variable {d : ℕ}

theorem r26t6c_centered_lipschitz_third
    (mu : Measure (Euc d)) [IsProbabilityMeasure mu]
    (hm3 : Integrable (fun x : Euc d => ‖x‖ ^ 3) mu)
    (f : Euc d → ℝ) (L : ℝ≥0) (hL : LipschitzWith L f) :
    Integrable (fun x => |HRS.Whole.projMean mu f x| ^ 3) mu ∧
    (∫ x, |HRS.Whole.projMean mu f x| ^ 3 ∂mu) ≤
      8 * (L : ℝ) ^ 3 * ∫ x, ‖x‖ ^ 3 ∂mu := by
  have hnorm1 : Integrable (fun x : Euc d => ‖x‖) mu := by
    refine (hm3.add (integrable_const (1 : ℝ))).mono'
      (by fun_prop : Measurable fun x : Euc d => ‖x‖).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 1), sq_nonneg ‖x‖]
  have hfmeas : Measurable f := hL.continuous.measurable
  have hfi : Integrable f mu := by
    have hi := (integrable_const (|f 0| : ℝ)).add
      (hnorm1.const_mul (L : ℝ))
    refine hi.mono' hfmeas.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    have hdist := hL.dist_le_mul x 0
    have hfx : |f x| ≤ |f 0| + (L : ℝ) * ‖x‖ := by
      have hx : |f x| ≤ |f 0| + |f x - f 0| := by
        calc
          |f x| = |(f x - f 0) + f 0| := by congr 1; ring
          _ ≤ |f x - f 0| + |f 0| := abs_add_le _ _
          _ = _ := add_comm _ _
      have hy : |f x - f 0| ≤ (L : ℝ) * ‖x‖ := by
        simpa [Real.dist_eq, dist_eq_norm] using hdist
      linarith
    simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ |f 0| + (L : ℝ) * ‖x‖)] using hfx
  let p := HRS.Whole.projMean mu f
  have hpmeas : Measurable p := hfmeas.sub measurable_const
  have hpi : Integrable p mu := hfi.sub (integrable_const _)
  have hp0 : ∫ x, p x ∂mu = 0 := by
    simp [p, HRS.Whole.projMean, HRS.Whole.pair,
      integral_sub hfi (integrable_const _)]
  have hpLip : LipschitzWith L p := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    have hl := hL.dist_le_mul x y
    simpa [p, HRS.Whole.projMean, Real.dist_eq, sub_sub_sub_cancel_right] using hl
  exact HRS.MS.S111T.s111t_centered_lipschitz_third_moment
    mu hm3 p hpmeas hpi hp0 L hpLip

end HRS.MS.R26T6C
