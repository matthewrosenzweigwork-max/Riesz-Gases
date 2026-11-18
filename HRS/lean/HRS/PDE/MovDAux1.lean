import HRS.PDE.MovSpec2b

/-!
# MOVD Aux1: narrow convergence of the conditioned marginals (`movT_cond_narrow`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

theorem movd_cond_narrow {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [TopologicalSpace α]
    [BorelSpace α]
    (P : Measure Ω) [IsProbabilityMeasure P] {Z : Ω → α} (hZ : Measurable Z) {A : ℕ → Set Ω}
    (hA : ∀ k, MeasurableSet (A k)) (hP : Tendsto (fun k => P (A k)) atTop (𝓝 1))
    {φ : α → ℝ} (hφ : Continuous φ) (hb : ∃ C, ∀ x, |φ x| ≤ C) :
    Tendsto (fun k => ∫ x, φ x ∂((movT_cond P (A k)).map Z)) atTop (𝓝 (∫ x, φ x ∂(P.map Z))) := by
  obtain ⟨C, hC⟩ := hb
  have hφm : Measurable φ := hφ.measurable
  have hφZ : Measurable (fun ω => φ (Z ω)) := hφm.comp hZ
  have hint : Integrable (fun ω => φ (Z ω)) P :=
    Integrable.of_bound hφZ.aestronglyMeasurable C (Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using hC (Z ω))
  have ha : Tendsto (fun k => (P (A k)).toReal) atTop (𝓝 1) := by
    have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hP
    rw [ENNReal.toReal_one] at this
    exact this
  have hJ : Tendsto (fun k => ∫ ω in A k, φ (Z ω) ∂P) atTop (𝓝 (∫ ω, φ (Z ω) ∂P)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbound : ∀ k, ‖(∫ ω in A k, φ (Z ω) ∂P) - ∫ ω, φ (Z ω) ∂P‖ ≤ C * (1 - (P (A k)).toReal) := by
      intro k
      have h1 := integral_add_compl (hA k) hint
      have h2 : (∫ ω in A k, φ (Z ω) ∂P) - ∫ ω, φ (Z ω) ∂P = -∫ ω in (A k)ᶜ, φ (Z ω) ∂P := by
        rw [← h1]; ring
      rw [h2, norm_neg]
      have h3 := norm_setIntegral_le_of_norm_le_const (μ := P) (s := (A k)ᶜ) (f := fun ω => φ (Z ω))
        (C := C) (measure_lt_top _ _) (fun x _ => by simpa [Real.norm_eq_abs] using hC (Z x))
      refine h3.trans (le_of_eq ?_)
      rw [measureReal_def, prob_compl_eq_one_sub (hA k), ENNReal.toReal_sub_of_le prob_le_one
        ENNReal.one_ne_top]
      simp
    have hlim : Tendsto (fun k => C * (1 - (P (A k)).toReal)) atTop (𝓝 0) := by
      have := ((tendsto_const_nhds (x := (1:ℝ))).sub ha).const_mul C
      simpa using this
    exact squeeze_zero (fun k => norm_nonneg _) hbound hlim
  have hform : ∀ k, ∫ x, φ x ∂((movT_cond P (A k)).map Z) =
      ((P (A k)).toReal)⁻¹ * ∫ ω in A k, φ (Z ω) ∂P := by
    intro k
    rw [integral_map hZ.aemeasurable hφm.aestronglyMeasurable]
    unfold movT_cond
    rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  have hfin : ∫ x, φ x ∂(P.map Z) = ∫ ω, φ (Z ω) ∂P :=
    integral_map hZ.aemeasurable hφm.aestronglyMeasurable
  rw [hfin]
  simp_rw [hform]
  have := (ha.inv₀ one_ne_zero).mul hJ
  simpa using this

end HRS

end
