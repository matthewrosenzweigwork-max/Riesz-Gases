import HRS.MS.S11Q3A5

/-!
# S11.3 / S11.4 (worker S11Q3), A6: a parametric integral that is `C¹` on `[0,∞)`, and the domination for the normalizer

* `s11q3_param_C1`: `I(t) = ∫ F(t,z) dz` is differentiable on `(0,∞)` with derivative `∫ ∂_tF`, `I` and `I'` are continuous on `[0,∞)`
  (uniform integrable majorant for `t ≥ 0`).
* `s11q3_F0`, `s11q3_E`, `s11q3_W`, `s11q3_W'`: the integrand `W_t(X) = e^{-βN F0(X) + β ∑ Γ_t(X_a)} ∏ ρ_t(X_a)` of the normalizer
  (the constant `½∬ g dμ dμ` cancels against the normalizer) and its time derivative.
* `s11q3_W_bound`: `|W_t|, |∂_tW_t| ≤ N ∏_a h(X_a)` for `t ≥ 0`, with `h` integrable.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S11Q3

open HRS HRS.Whole HRS.MS.MovForce HRS.MS.S113BD

theorem s11q3_param_C1 {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} {F F' : ℝ → Z → ℝ} {bound : Z → ℝ}
    (hb : Integrable bound μ) (hFm : ∀ t, 0 ≤ t → AEStronglyMeasurable (F t) μ)
    (hF'm : ∀ t, 0 ≤ t → AEStronglyMeasurable (F' t) μ) (hFb : ∀ t, 0 ≤ t → ∀ z, ‖F t z‖ ≤ bound z)
    (hF'b : ∀ t, 0 ≤ t → ∀ z, ‖F' t z‖ ≤ bound z)
    (hder : ∀ t, 0 < t → ∀ z, HasDerivAt (fun τ => F τ z) (F' t z) t)
    (hcF : ∀ z, ContinuousOn (fun τ => F τ z) (Ici 0)) (hcF' : ∀ z, ContinuousOn (fun τ => F' τ z) (Ici 0)) :
    (∀ t, 0 < t → HasDerivAt (fun τ => ∫ z, F τ z ∂μ) (∫ z, F' t z ∂μ) t) ∧
      ContinuousOn (fun τ => ∫ z, F τ z ∂μ) (Ici 0) ∧ ContinuousOn (fun τ => ∫ z, F' τ z ∂μ) (Ici 0) := by
  refine ⟨fun t ht => ?_, fun t0 ht0 => ?_, fun t0 ht0 => ?_⟩
  · have hs : Ioi (0 : ℝ) ∈ 𝓝 t := Ioi_mem_nhds ht
    have hFi : Integrable (F t) μ := hb.mono' (hFm t ht.le) (Filter.Eventually.of_forall (hFb t ht.le))
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Ioi 0) (bound := bound) hs
      (by filter_upwards [hs] with τ hτ; exact hFm τ (le_of_lt hτ)) hFi (hF'm t ht.le)
      (Filter.Eventually.of_forall fun z τ hτ => hF'b τ (le_of_lt hτ) z) hb
      (Filter.Eventually.of_forall fun z τ hτ => hder τ hτ z)).2
  · refine continuousWithinAt_of_dominated (bound := bound) ?_ ?_ hb (Filter.Eventually.of_forall fun z => hcF z t0 ht0)
    · exact eventually_nhdsWithin_of_forall fun t ht => hFm t ht
    · exact eventually_nhdsWithin_of_forall fun t ht => Filter.Eventually.of_forall (hFb t ht)
  · refine continuousWithinAt_of_dominated (bound := bound) ?_ ?_ hb (Filter.Eventually.of_forall fun z => hcF' z t0 ht0)
    · exact eventually_nhdsWithin_of_forall fun t ht => hF'm t ht
    · exact eventually_nhdsWithin_of_forall fun t ht => Filter.Eventually.of_forall (hF'b t ht)

end HRS.MS.S11Q3

end
