import HRS.Uniform.Q54cAux46

/-!
# Q54c, part 47: product-space independence and the moments of the coupled noises on `Ω' × Ω`
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q54c

open HRS

theorem indep_prod_aux {Ω' Ω : Type*} {mΩ' : MeasurableSpace Ω'} {mΩ : MeasurableSpace Ω}
    (P' : Measure Ω') (PΩ : Measure Ω) [IsProbabilityMeasure P'] [IsProbabilityMeasure PΩ]
    {E H : Type*} [MeasurableSpace E] [MeasurableSpace H] (η₀ : Ω → E) (hη₀ : Measurable η₀)
    (G : ℝ → Ω' → H) (hG : ∀ τ, Measurable (G τ)) (S : Set ℝ) :
    Indep (MeasurableSpace.comap (fun p : Ω' × Ω => η₀ p.2) inferInstance)
      (⨆ τ ∈ S, MeasurableSpace.comap (fun p : Ω' × Ω => G τ p.1) inferInstance) (P'.prod PΩ) := by
  have hbase : Indep (MeasurableSpace.comap (fun p : Ω' × Ω => p.2) inferInstance)
      (MeasurableSpace.comap (fun p : Ω' × Ω => p.1) inferInstance) (P'.prod PΩ) := by
    have := indepFun_prod (μ := P') (ν := PΩ) (X := fun ω : Ω' => ω) (Y := fun ω : Ω => ω)
      measurable_id measurable_id
    exact ((IndepFun_iff_Indep _ _ _).1 this).symm
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hbase ?_) ?_
  · have : (fun p : Ω' × Ω => η₀ p.2) = η₀ ∘ (fun p : Ω' × Ω => p.2) := rfl
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hη₀.comap_le
  · refine iSup₂_le fun τ _ => ?_
    have : (fun p : Ω' × Ω => G τ p.1) = G τ ∘ (fun p : Ω' × Ω => p.1) := rfl
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (hG τ).comap_le

theorem lintegral_prod_fst {Ω' Ω : Type*} {mΩ' : MeasurableSpace Ω'} {mΩ : MeasurableSpace Ω}
    (P' : Measure Ω') (PΩ : Measure Ω) [IsProbabilityMeasure P'] [IsProbabilityMeasure PΩ]
    {f : Ω' → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f p.1 ∂(P'.prod PΩ) = ∫⁻ ω, f ω ∂P' :=
  (measurePreserving_fst (μ := P') (ν := PΩ)).lintegral_comp hf

theorem lintegral_prod_snd {Ω' Ω : Type*} {mΩ' : MeasurableSpace Ω'} {mΩ : MeasurableSpace Ω}
    (P' : Measure Ω') (PΩ : Measure Ω) [IsProbabilityMeasure P'] [IsProbabilityMeasure PΩ]
    {f : Ω → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f p.2 ∂(P'.prod PΩ) = ∫⁻ ω, f ω ∂PΩ :=
  (measurePreserving_snd (μ := P') (ν := PΩ)).lintegral_comp hf

theorem map_prod_snd {Ω' Ω : Type*} {mΩ' : MeasurableSpace Ω'} {mΩ : MeasurableSpace Ω}
    (P' : Measure Ω') (PΩ : Measure Ω) [IsProbabilityMeasure P'] [IsProbabilityMeasure PΩ]
    {E : Type*} [MeasurableSpace E] (η₀ : Ω → E) (hη₀ : Measurable η₀) :
    (P'.prod PΩ).map (fun p : Ω' × Ω => η₀ p.2) = PΩ.map η₀ := by
  have : (fun p : Ω' × Ω => η₀ p.2) = η₀ ∘ (fun p : Ω' × Ω => p.2) := rfl
  rw [this, ← Measure.map_map hη₀ measurable_snd, Measure.map_snd_prod]
  simp

end HRS.Uniform.Q54c
