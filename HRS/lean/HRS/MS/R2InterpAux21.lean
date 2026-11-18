import HRS.MS.R2InterpAux20

/-!
# S10.2 (worker S102), part 21 (packet B3): removal of the projection in the derivatives (norm convergence)

If `P_L → id` strongly and `‖P_L‖ ≤ 1`, `Φ ∈ C_b^5`, `γ_u` a probability measure and `j ≤ 5`, then
`s102_projHeatD γ Φ P_L j u y → D^j(r2HeatFn γ Φ u)(y)` in the norm of `j`-linear forms.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ} {m T : ℝ}

theorem s102_proj_limit (γ : ℝ → Measure (OscPath d m T)) (hγp : ∀ u, IsProbabilityMeasure (γ u))
    (Pj : ℕ → (OscPath d m T →L[ℝ] OscPath d m T))
    (hconv : ∀ w, Tendsto (fun L => Pj L w) atTop (𝓝 w)) {Φ : OscPath d m T → ℝ} (hΦ : MemCb 5 Φ)
    (j : ℕ) (hj : j ≤ 5) (u : ℝ) (y : OscPath d m T) :
    Tendsto (fun L => s102_projHeatD γ Φ (Pj L) j u y) atTop
      (𝓝 (iteratedFDeriv ℝ j (r2HeatFn γ Φ u) y)) := by
  haveI := hγp u
  obtain ⟨C, hC⟩ := s102_bound_of_memCb hΦ hj
  have hcont : Continuous (iteratedFDeriv ℝ j Φ) :=
    hΦ.1.continuous_iteratedFDeriv (m := j) (by exact_mod_cast hj)
  rw [((s102_r2HeatFn_derivs γ u hΦ).2 j hj y).1]
  unfold s102_projHeatD
  refine tendsto_integral_of_dominated_convergence (fun _ => C) ?_ (integrable_const C) ?_ ?_
  · intro L
    exact (hcont.comp (((Pj L).continuous).comp (by fun_prop : Continuous fun z : OscPath d m T => y + z))).aestronglyMeasurable
  · intro L
    exact Filter.Eventually.of_forall fun z => hC _
  · refine Filter.Eventually.of_forall fun z => ?_
    exact (hcont.tendsto (y + z)).comp (hconv (y + z))

end HRS.MS.R2Interp

end
