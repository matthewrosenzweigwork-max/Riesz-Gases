import HRS.MC.CepH5Q2

/-!
# Packet CEPH5FISH, part 3: measurability of `r ↦ fisherInfo D N (selectedLaw Q X r)` for `V ∈ C¹`

`h5_fisher_measurable_ck` is `CepH5.h5_fisher_measurable` with the additional hypothesis `Torus.IsCk 1 D.V`
(without regularity of `D.V` the test integrand `F_ζ` is not continuous, nor even measurable).
-/

noncomputable section

namespace HRS.MC.CepH5Pf

open HRS MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {N : ℕ}

lemma q3_cont_integral {Q : Measure Ω} [IsProbabilityMeasure Q] {X : ℝ≥0 → Ω → Config 1 N}
    (hmeas : ∀ t, Measurable (X t))
    (hcont : ∀ᵐ ω ∂Q, ∀ i, Continuous fun t => X t ω i) {F : Config 1 N → ℝ} (hF : Continuous F) :
    Continuous fun r : ℝ => ∫ x, F x ∂(selectedLaw Q X r) := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖F x‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_univ (X := Config 1 N)).exists_bound_of_continuousOn hF.continuousOn
    exact ⟨C, fun x => hC x (Set.mem_univ x)⟩
  have h1 : ∀ r : ℝ, ∫ x, F x ∂(selectedLaw Q X r) = ∫ ω, F (X (Real.toNNReal r) ω) ∂Q := by
    intro r
    simp only [selectedLaw, law]
    exact integral_map (hmeas _).aemeasurable hF.aestronglyMeasurable
  simp_rw [h1]
  refine continuous_of_dominated (bound := fun _ => C) (fun r => ?_) (fun r => ?_) ?_ ?_
  · exact (hF.measurable.comp (hmeas _)).aestronglyMeasurable
  · exact Eventually.of_forall fun ω => hC _
  · exact integrable_const C
  · filter_upwards [hcont] with ω hω
    refine hF.comp ?_
    exact continuous_pi fun i => (hω i).comp continuous_real_toNNReal

theorem h5_fisher_measurable_ck [NeZero N] {Q : Measure Ω} [IsProbabilityMeasure Q] (D : DynData 1)
    (hV : Torus.IsCk 1 D.V)
    {X : ℝ≥0 → Ω → Config 1 N} (hmeas : ∀ t, Measurable (X t))
    (hcont : ∀ᵐ ω ∂Q, ∀ i, Continuous fun t => X t ω i) :
    Measurable fun r : ℝ => fisherInfo D N (selectedLaw Q X r) := by
  apply LowerSemicontinuous.measurable
  unfold fisherInfo
  refine lowerSemicontinuous_biSup fun ζ hζ => ?_
  have hc := q3_cont_integral hmeas hcont (q2_F_cont D hV hζ)
  exact (ENNReal.continuous_ofReal.comp hc).lowerSemicontinuous

end HRS.MC.CepH5Pf
