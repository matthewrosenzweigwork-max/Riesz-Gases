import HRS.Whole.MovtrAux9

/-!
# MOVTR auxiliary 10: translation covariance of the modulated energy and Gibbs law
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

lemma movtr_convMeasure_translate (g : Euc d → ℝ) (μ : Measure (Euc d)) (a x : Euc d) :
    convMeasure g (μ.map (fun y => y + a)) (x + a) = convMeasure g μ x := by
  unfold convMeasure
  have := integral_map_equiv (μ := μ) (MeasurableEquiv.addRight a) (fun y => g (x + a - y))
  simp only [MeasurableEquiv.coe_addRight] at this
  rw [this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [add_sub_add_right_eq_sub]

lemma movtr_energyPairing_translate (g : Euc d → ℝ) (μ : Measure (Euc d)) (a : Euc d) :
    energyPairing g (μ.map (fun y => y + a)) (μ.map (fun y => y + a)) = energyPairing g μ μ := by
  unfold energyPairing
  have e : ∀ f : Euc d → ℝ, ∫ y, f y ∂(μ.map (fun y => y + a)) = ∫ y, f (y + a) ∂μ := by
    intro f
    have := integral_map_equiv (μ := μ) (MeasurableEquiv.addRight a) f
    simpa only [MeasurableEquiv.coe_addRight] using this
  have inner : ∀ x : Euc d, ∫ y, g (x - y) ∂(μ.map (fun y => y + a)) = ∫ y, g (x - (y + a)) ∂μ := by
    intro x
    exact e (fun y => g (x - y))
  simp_rw [inner]
  rw [e (fun x => ∫ y, g (x - (y + a)) ∂μ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [add_sub_add_right_eq_sub]

lemma movtr_modulatedEnergy_translate (g : Euc d → ℝ) {N : ℕ} (μ : Measure (Euc d)) (a : Euc d)
    (X : EucConfig d N) :
    modulatedEnergy g (fun i => X i + a) (μ.map (fun y => y + a)) = modulatedEnergy g X μ := by
  unfold modulatedEnergy
  simp only [add_sub_add_right_eq_sub, movtr_convMeasure_translate, movtr_energyPairing_translate]


/-- The joint translation of configurations as a measurable equivalence. -/
def movtr_cfgEquiv (d N : ℕ) (a : Euc d) : EucConfig d N ≃ᵐ EucConfig d N :=
  MeasurableEquiv.piCongrRight (fun _ : Fin N => MeasurableEquiv.addRight a)

lemma movtr_cfgEquiv_apply (N : ℕ) (a : Euc d) (X : EucConfig d N) :
    movtr_cfgEquiv d N a X = fun i => X i + a := rfl

lemma movtr_pi_map (N : ℕ) (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (a : Euc d) :
    (Measure.pi fun _ : Fin N => μ).map (movtr_cfgEquiv d N a) =
      Measure.pi fun _ : Fin N => μ.map (fun y => y + a) := by
  have : IsProbabilityMeasure (μ.map (fun y => y + a)) := inferInstance
  have h := Measure.pi_map_pi (μ := fun _ : Fin N => μ) (f := fun _ y => y + a)
    (fun _ => (measurable_add_const a).aemeasurable)
  exact h

lemma movtr_map_withDensity {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (e : α ≃ᵐ β)
    (ν : Measure α) [SFinite ν] (g : β → ℝ≥0∞) :
    (ν.withDensity (g ∘ e)).map e = (ν.map e).withDensity g := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply' _ (e ⁻¹' s), withDensity_apply' _ s,
    Measure.restrict_map e.measurable hs, lintegral_map_equiv]
  rfl

lemma movtr_gibbsNormalizer_translate (g : Euc d → ℝ) (N : ℕ) (β : ℝ) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] (a : Euc d) :
    gibbsNormalizer g N β (μ.map (fun y => y + a)) = gibbsNormalizer g N β μ := by
  unfold gibbsNormalizer
  rw [← movtr_pi_map N μ a]
  rw [integral_map_equiv (movtr_cfgEquiv d N a)
    (fun X : EucConfig d N => Real.exp (-β * N * modulatedEnergy g X (μ.map (fun y => y + a))))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  simp only [movtr_cfgEquiv_apply]
  rw [movtr_modulatedEnergy_translate]

lemma movtr_modulatedGibbs_translate (g : Euc d → ℝ) (N : ℕ) (β : ℝ) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] (a : Euc d) :
    modulatedGibbs g N β (μ.map (fun y => y + a)) =
      (modulatedGibbs g N β μ).map (fun X i => X i + a) := by
  unfold modulatedGibbs
  rw [movtr_gibbsNormalizer_translate]
  have hmap : (fun X i => X i + a) = ⇑(movtr_cfgEquiv d N a) := rfl
  rw [hmap, Measure.map_smul, ← movtr_pi_map N μ a]
  congr 1
  have hf : (fun X : EucConfig d N =>
      ENNReal.ofReal (Real.exp (-β * N * modulatedEnergy g X μ))) =
      (fun X : EucConfig d N =>
        ENNReal.ofReal (Real.exp (-β * N * modulatedEnergy g X (μ.map (fun y => y + a))))) ∘
          (movtr_cfgEquiv d N a) := by
    funext X
    simp only [Function.comp, movtr_cfgEquiv_apply, movtr_modulatedEnergy_translate]
  rw [hf, movtr_map_withDensity]
  exact (movtr_cfgEquiv d N a).measurable.aemeasurable

end HRS.Whole
