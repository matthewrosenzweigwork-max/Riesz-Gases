import HRS.PDE.MovDAux4

/-!
# MOVD Aux5: abstract limit `k → ∞` of the source term under conditioning (`movT_source_limit_cond`)

Abstract lemmas: (i) convergence of `∫ S d(P(·|A_k)∘Z⁻¹)` for a fixed integrable `S`; (ii) a jointly measurable
modification of a process with a.s. continuous paths.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

theorem movd_cond_tendsto_integral {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) [IsProbabilityMeasure P] {Z : Ω → α} (hZ : Measurable Z) {A : ℕ → Set Ω}
    (hA : ∀ k, MeasurableSet (A k)) (hP : Tendsto (fun k => P (A k)) atTop (𝓝 1))
    {S : α → ℝ} (hS : Integrable S (P.map Z)) :
    Tendsto (fun k => ∫ x, S x ∂((movT_cond P (A k)).map Z)) atTop (𝓝 (∫ x, S x ∂(P.map Z))) := by
  have hint : Integrable (fun ω => S (Z ω)) P :=
    (integrable_map_measure hS.aestronglyMeasurable hZ.aemeasurable).1 hS
  have ha : Tendsto (fun k => (P (A k)).toReal) atTop (𝓝 1) := by
    have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hP
    rw [ENNReal.toReal_one] at this
    exact this
  have hcompl : Tendsto (fun k => P (A k)ᶜ) atTop (𝓝 0) := by
    have h1 : ∀ k, P (A k)ᶜ = 1 - P (A k) := fun k => prob_compl_eq_one_sub (hA k)
    simp_rw [h1]
    have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞))) hP (Or.inl ENNReal.one_ne_top)
    simpa using this
  have hset : Tendsto (fun k => ∫⁻ ω in (A k)ᶜ, ‖S (Z ω)‖ₑ ∂P) atTop (𝓝 0) :=
    tendsto_setLIntegral_zero (f := fun ω => ‖S (Z ω)‖ₑ) hint.2.ne hcompl
  have hset' : Tendsto (fun k => (∫⁻ ω in (A k)ᶜ, ‖S (Z ω)‖ₑ ∂P).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hset
    rw [ENNReal.toReal_zero] at this
    exact this
  have hJ : Tendsto (fun k => ∫ ω in A k, S (Z ω) ∂P) atTop (𝓝 (∫ ω, S (Z ω) ∂P)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hset'
    have h1 := integral_add_compl (hA k) hint
    have h2 : (∫ ω in A k, S (Z ω) ∂P) - ∫ ω, S (Z ω) ∂P = -∫ ω in (A k)ᶜ, S (Z ω) ∂P := by
      rw [← h1]; ring
    rw [h2, norm_neg]
    have h3 := enorm_integral_le_lintegral_enorm (μ := P.restrict (A k)ᶜ) (fun ω => S (Z ω))
    have hne : ∫⁻ ω in (A k)ᶜ, ‖S (Z ω)‖ₑ ∂P ≠ ⊤ :=
      ne_top_of_le_ne_top hint.2.ne (setLIntegral_le_lintegral _ _)
    rw [← ofReal_norm] at h3
    exact (ENNReal.ofReal_le_iff_le_toReal hne).1 h3
  have hform : ∀ k, ∫ x, S x ∂((movT_cond P (A k)).map Z) =
      ((P (A k)).toReal)⁻¹ * ∫ ω in A k, S (Z ω) ∂P := by
    intro k
    rw [integral_map hZ.aemeasurable (hS.aestronglyMeasurable.mono_ac
      ((movd_cond_ac P (A k)).map hZ))]
    unfold movT_cond
    rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  have hfin : ∫ x, S x ∂(P.map Z) = ∫ ω, S (Z ω) ∂P :=
    integral_map hZ.aemeasurable hS.aestronglyMeasurable
  rw [hfin]
  simp_rw [hform]
  have := (ha.inv₀ one_ne_zero).mul hJ
  simpa using this

/-- A jointly measurable modification of a process with a.s. continuous paths. -/
theorem movd_path_modification {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    [TopologicalSpace β] [TopologicalSpace.PseudoMetrizableSpace β] [BorelSpace β] [Inhabited β]
    (P : Measure Ω) (X : ℝ≥0 → Ω → β) (hX : ∀ t, Measurable (X t))
    (hc : ∀ᵐ ω ∂P, Continuous fun t => X t ω) :
    ∃ Xt : ℝ → Ω → β, (∀ r : ℝ, Xt r =ᵐ[P] X r.toNNReal) ∧ Measurable (Function.uncurry Xt) := by
  obtain ⟨N₀, hN₀sub, hN₀m, hN₀0⟩ : ∃ N : Set Ω, {ω | ¬ Continuous fun t => X t ω} ⊆ N ∧
      MeasurableSet N ∧ P N = 0 :=
    ⟨toMeasurable P {ω | ¬ Continuous fun t => X t ω}, subset_toMeasurable _ _,
      measurableSet_toMeasurable _ _, by rw [measure_toMeasurable]; exact ae_iff.1 hc⟩
  classical
  refine ⟨fun r ω => if ω ∈ N₀ then default else X r.toNNReal ω, fun r => ?_, ?_⟩
  · have : ∀ᵐ ω ∂P, ω ∉ N₀ := by
      rw [ae_iff]; simpa using hN₀0
    filter_upwards [this] with ω hω
    simp [hω]
  · refine measurable_uncurry_of_continuous_of_measurable (fun ω => ?_) (fun r => ?_)
    · by_cases hω : ω ∈ N₀
      · simp only [hω, if_true]; exact continuous_const
      · simp only [hω, if_false]
        have : Continuous fun t => X t ω := by
          by_contra hcon
          exact hω (hN₀sub hcon)
        exact this.comp continuous_real_toNNReal
    · exact Measurable.ite hN₀m measurable_const (hX _)

end HRS

end
