import HRS.MS.FinNoiseAux6
import HRS.MS.SuppU9

/-!
# S8.6 `finite_noise`, packet P2 (S86): the deterministic reference covariance density

`s86_reference_density`: for a jointly Borel, bounded feature family `Γ` and a probability measure `μ`
there is `Cdet : ℝ → 𝒦 →L 𝒦 →L ℝ` with `Cdet r = featureForm m H β⁻¹ (Γ · r) μ` for all `r`, satisfying
`IsDetCovDensity H Cdet` (measurable entries, positive trace class, integrable trace) and the trace bound
`2 β⁻¹ d B²`.  Statement adopted from the Pro packet S8.6.05, checked: true.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.FinNoise

open HRS HRS.Whole HRS.MS.U9

theorem s86_reference_density (d : ℕ) (m H β B : ℝ) (hβ : 0 < β)
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (Γ : Fin d → ℝ → Euc d → KSpace d m H)
    (hΓ : ∀ i, Measurable (fun p : ℝ × Euc d => Γ i p.1 p.2))
    (hΓbound : ∀ (i : Fin d) (r : ℝ) (x : Euc d), ‖Γ i r x‖ ≤ B) :
    ∃ Cdet : ℝ → KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ,
      IsDetCovDensity H Cdet ∧
      (∀ (r : ℝ) (u v : KSpace d m H),
        Cdet r u v = featureForm m H β⁻¹ (fun i => Γ i r) μ u v) ∧
      ∀ r : ℝ, traceNormForm (Cdet r) ≤ 2 * β⁻¹ * (d : ℝ) * B ^ 2 := by
  have hq : 0 ≤ β⁻¹ := (inv_pos.2 hβ).le
  have hΓr : ∀ r : ℝ, ∀ i, Measurable (Γ i r) := fun r i =>
    (hΓ i).comp (measurable_const.prodMk measurable_id)
  have hex : ∀ r : ℝ, ∃ Bf : KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ,
      (∀ u v, Bf u v = u9_form β⁻¹ (fun i => Γ i r) μ u v) ∧ IsTraceClassCov Bf ∧
      traceNormForm Bf ≤ 2 * d * B ^ 2 * β⁻¹ * (μ Set.univ).toReal :=
    fun r => u9_exists_form hq (hΓr r) (fun i x => hΓbound i r x)
  choose Cdet hform htc htr using hex
  refine ⟨Cdet, ⟨?_, fun σ _ => htc σ, ?_⟩, hform, fun r => ?_⟩
  · intro x y
    have hf : (fun σ => Cdet σ x y) = fun σ => 2 * β⁻¹ * ∑ a : Fin d,
        ∫ x', inner ℝ (Γ a σ x') x * inner ℝ (Γ a σ x') y ∂μ := by
      funext σ; rw [hform]; rfl
    rw [hf]
    refine measurable_const.mul (Finset.measurable_sum _ fun a _ => ?_)
    have hm : Measurable (Function.uncurry fun (σ : ℝ) (x' : Euc d) =>
        inner ℝ (Γ a σ x') x * inner ℝ (Γ a σ x') y) :=
      ((u9_meas_inner (hΓ a) x).mul (u9_meas_inner (hΓ a) y))
    exact (hm.stronglyMeasurable.integral_prod_right (ν := μ)).measurable
  · have hmeas : Measurable fun σ => traceNormForm (Cdet σ) :=
      measurable_traceNormForm Cdet (fun x y => by
        have hf : (fun σ => Cdet σ x y) = fun σ => 2 * β⁻¹ * ∑ a : Fin d,
            ∫ x', inner ℝ (Γ a σ x') x * inner ℝ (Γ a σ x') y ∂μ := by
          funext σ; rw [hform]; rfl
        rw [hf]
        refine measurable_const.mul (Finset.measurable_sum _ fun a _ => ?_)
        have hm : Measurable (Function.uncurry fun (σ : ℝ) (x' : Euc d) =>
            inner ℝ (Γ a σ x') x * inner ℝ (Γ a σ x') y) :=
          ((u9_meas_inner (hΓ a) x).mul (u9_meas_inner (hΓ a) y))
        exact (hm.stronglyMeasurable.integral_prod_right (ν := μ)).measurable)
    refine Measure.integrableOn_of_bounded (M := 2 * β⁻¹ * (d : ℝ) * B ^ 2) (by simp)
      hmeas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun σ => ?_
    rw [Real.norm_of_nonneg (u9_traceNormForm_nonneg _)]
    have := htr σ
    simp only [measure_univ, ENNReal.toReal_one, mul_one] at this
    refine this.trans (le_of_eq ?_)
    ring
  · have := htr r
    simp only [measure_univ, ENNReal.toReal_one, mul_one] at this
    refine this.trans (le_of_eq ?_)
    ring

end HRS.MS.FinNoise
