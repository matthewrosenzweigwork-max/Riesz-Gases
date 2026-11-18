import HRS.Sections.AdjKGlueAux13

/-!
# ADJK-GLUE, part 14: convergence in law from a characteristic-function comparison
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

universe u

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ}

/-- If `L_n` is close (in characteristic functions) to `A_n + G` with `G ∼ γ` independent, and `A_n ⇒ A'`, then
`L_n ⇒ A' + G'` for `G' ∼ γ` independent of `A'`. -/
theorem adjkg_conv_of_comparison {p : ℕ} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (L A : ∀ n, Ω n → EuclideanSpace ℝ (Fin p)) (hL : ∀ n, AEMeasurable (L n) (P n))
    (γ : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure γ]
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (A' G' : Ω' → EuclideanSpace ℝ (Fin p)) (hA' : AEMeasurable A' P') (hG' : AEMeasurable G' P')
    (hind : IndepFun A' G' P') (hlawG : P'.map G' = γ)
    (hAconv : TendstoInDistribution A atTop A' P P')
    (hcmp : ∀ t, Tendsto (fun n => ‖charFun ((P n).map (L n)) t -
      charFun ((P n).map (A n)) t * charFun γ t‖) atTop (𝓝 0)) :
    TendstoInDistribution L atTop (fun ω => A' ω + G' ω) P P' := by
  refine TendstoInDistribution.of_tendsto_charFun hL (hA'.add hG') fun t => ?_
  have e : charFun (P'.map (fun ω => A' ω + G' ω)) t =
      charFun (P'.map A') t * charFun γ t := by
    rw [hind.charFun_map_fun_add_eq_mul hA' hG', Pi.mul_apply, hlawG]
  rw [e]
  have h1 := hAconv.tendsto_charFun t
  have h2 : Tendsto (fun n => charFun ((P n).map (A n)) t * charFun γ t) atTop
      (𝓝 (charFun (P'.map A') t * charFun γ t)) := h1.mul_const _
  have h3 : Tendsto (fun n => charFun ((P n).map (L n)) t -
      charFun ((P n).map (A n)) t * charFun γ t) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 (hcmp t)
  have := h3.add h2
  rw [zero_add] at this
  refine this.congr fun n => ?_
  ring

theorem adjkg_linCoord_measurable {N : ℕ} (μ : Measure (Torus d)) {f : Torus d → ℝ} (hf : Measurable f) :
    Measurable (fun X : Config d N => linCoord μ f X) := by
  unfold linCoord
  refine measurable_const.mul ((measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)).sub
    measurable_const)
  exact hf.comp (measurable_pi_apply i)

end HRS.AdjK
