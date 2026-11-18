import HRS.MS.R2InterpAux66

/-!
# S10.2 (worker S102), part 67 (packet M1): the density of the time marginals against the invariant law

If `P = P'.withDensity (φ ∘ X₀)` where under `P'` both `X₀` and `X_t` have the law `Q` (invariance), then the law of `X_t` under `P` is
`(Q.withDensity φ) κ` for the transition kernel `κ = condDistrib X_t X₀ P'`, which preserves `Q`; hence it has an `L^p(Q)` density bounded by `‖φ‖_{L^p(Q)}`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]

theorem s102_transfer_density (P P' : Measure Ω) [IsProbabilityMeasure P'] (X0 Xt : Ω → E)
    (hX0 : Measurable X0) (hXt : Measurable Xt) (Q : Measure E) [IsProbabilityMeasure Q] (φ : E → ℝ≥0∞)
    (hφ : Measurable φ) (hP : P = P'.withDensity (fun ω => φ (X0 ω))) (h0 : P'.map X0 = Q) (ht : P'.map Xt = Q)
    :
    ∃ κ : Kernel E E, IsMarkovKernel κ ∧ Q.bind κ = Q ∧ P.map Xt = (Q.withDensity φ).bind κ := by
  set κ : Kernel E E := condDistrib Xt X0 P' with hκ
  haveI : IsMarkovKernel κ := inferInstance
  have hinv : Q.bind κ = Q := by
    have := condDistrib_comp_map (μ := P') hX0.aemeasurable hXt.aemeasurable
    rw [h0, ht] at this
    exact this
  have hcp : Q ⊗ₘ κ = P'.map (fun ω => (X0 ω, Xt ω)) := by
    have := compProd_map_condDistrib (μ := P') hX0.aemeasurable hXt.aemeasurable
    rwa [h0] at this
  have hlaw : P.map Xt = (Q.withDensity φ).bind κ := by
    ext C hC
    rw [Measure.map_apply hXt hC, Measure.bind_apply hC κ.aemeasurable,
      lintegral_withDensity_eq_lintegral_mul _ hφ (κ.measurable_coe hC)]
    have h1 : P (Xt ⁻¹' C) = ∫⁻ ω, φ (X0 ω) * (C.indicator 1 (Xt ω)) ∂P' := by
      rw [hP, withDensity_apply _ (hXt hC), ← lintegral_indicator (hXt hC)]
      refine lintegral_congr fun ω => ?_
      by_cases h : Xt ω ∈ C <;> simp [h, Set.indicator]
    rw [h1]
    have h2 : ∫⁻ ω, φ (X0 ω) * (C.indicator 1 (Xt ω)) ∂P' =
        ∫⁻ z, φ z.1 * C.indicator 1 z.2 ∂(P'.map (fun ω => (X0 ω, Xt ω))) := by
      exact (lintegral_map (f := fun z : E × E => φ z.1 * C.indicator 1 z.2)
        ((hφ.comp measurable_fst).mul ((measurable_one.indicator hC).comp measurable_snd))
        (hX0.prodMk hXt)).symm
    rw [h2, ← hcp, Measure.lintegral_compProd (f := fun z : E × E => φ z.1 * C.indicator 1 z.2)
      ((hφ.comp measurable_fst).mul ((measurable_one.indicator hC).comp measurable_snd))]
    refine lintegral_congr fun x => ?_
    simp only [Pi.mul_apply]
    rw [lintegral_const_mul _ (measurable_one.indicator hC), lintegral_indicator_one hC]
  exact ⟨κ, inferInstance, hinv, hlaw⟩

end HRS.MS.R2Interp

end
