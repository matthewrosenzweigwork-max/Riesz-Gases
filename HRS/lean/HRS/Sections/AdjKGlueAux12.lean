import HRS.Sections.AdjKGlueAux11
import HRS.Main.GFB4Aux15

/-!
# ADJK-GLUE, part 12: the product extension `P ⊗ γ` of a particle system

For a particle system on `(Ω, P)` and a probability measure `γ` on `E`, the system composed with `Prod.fst` on
`(Ω × E, P ⊗ γ)` is again a particle system, and a filtered strong solution for the enlarged filtration
`(ℱ_t ⊗ ℬ(E)) ⊔ nullSets`.  Used to realise a Gaussian vector independent of the initial configuration on the sample space.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

universe u v

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ}

theorem adjkg_prod_preimage {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
    (P : Measure Ω) [SFinite P] (γ : Measure E) [IsProbabilityMeasure γ] (B : Set Ω) :
    (P.prod γ) (Prod.fst ⁻¹' B) = P B := by
  rw [show (Prod.fst ⁻¹' B : Set (Ω × E)) = B ×ˢ Set.univ from Set.prod_univ.symm, Measure.prod_prod,
    measure_univ, mul_one]

theorem adjkg_enlarge_particle {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {E : Type v} [MeasurableSpace E] (γ : Measure E) [IsProbabilityMeasure γ] {N : ℕ} {D : DynData d}
    {T : ℝ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : IsParticleSystem P D T X₀ W X) :
    IsParticleSystem (P.prod γ) D T (fun ω => X₀ ω.1) (fun t ω => W t ω.1) (fun t ω => X t ω.1) := by
  have hπ : MeasurePreserving (Prod.fst : Ω × E → Ω) (P.prod γ) P := measurePreserving_fst
  refine ⟨⟨fun i j => ?_, ?_⟩, ?_, GF.isStrongSolution_comp hπ hX.sol⟩
  · obtain ⟨hB, -⟩ := hX.brownian
    have h := hB i j
    refine ⟨⟨fun I => (h.hasLaw I).comp hπ.hasLaw⟩, ?_⟩
    exact hπ.quasiMeasurePreserving.ae h.cont
  · obtain ⟨-, hI⟩ := hX.brownian
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hI ⊢
    intro S sets hsets
    have e1 : (⋂ i ∈ S, (fun ω : Ω × E => (fun t : ℝ≥0 => W t ω.1 i.1 i.2)) ⁻¹' sets i) =
        Prod.fst ⁻¹' (⋂ i ∈ S, (fun ω : Ω => (fun t : ℝ≥0 => W t ω i.1 i.2)) ⁻¹' sets i) := by
      ext ω; simp
    rw [e1, adjkg_prod_preimage]
    rw [hI S hsets]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact (adjkg_prod_preimage P γ _).symm
  · rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro s t hs ht
    have h := hX.indep
    rw [indepFun_iff_measure_inter_preimage_eq_mul] at h
    have e1 : ((fun ω : Ω × E => X₀ ω.1) ⁻¹' s ∩ (fun ω : Ω × E => (fun t : ℝ≥0 => W t ω.1)) ⁻¹' t) =
        Prod.fst ⁻¹' (X₀ ⁻¹' s ∩ (fun ω : Ω => (fun t : ℝ≥0 => W t ω)) ⁻¹' t) := by
      ext ω; simp
    rw [e1, adjkg_prod_preimage, h s t hs ht]
    exact congrArg₂ (· * ·) (adjkg_prod_preimage P γ _).symm (adjkg_prod_preimage P γ _).symm

theorem adjkg_enlarge_filtered {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {E : Type v} [mE : MeasurableSpace E] (γ : Measure E)
    [IsProbabilityMeasure γ] {N : ℕ} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsFilteredSolution P ℱ W' W X) :
    ∃ (ℱ' : Filtration ℝ (inferInstance : MeasurableSpace (Ω × E)))
      (W'' : ℝ≥0 → Ω × E → (Fin N × Fin d) → ℝ),
      IsFilteredSolution (P.prod γ) ℱ' W'' (fun t ω => W t ω.1) (fun t ω => X t ω.1) := by
  have hπ : MeasurePreserving (Prod.fst : Ω × E → Ω) (P.prod γ) P := measurePreserving_fst
  have hπ' : ∀ t : ℝ, Measurable[GF.gfb4_initFil (P.prod γ) ℱ t, ℱ t] (Prod.fst : Ω × E → Ω) :=
    fun t => Measurable.of_comap_le
      (le_sup_left.trans' (le_sup_left (a := MeasurableSpace.comap Prod.fst (ℱ t))))
  have hΔm : ∀ s t : ℝ≥0, Measurable (fun ω => W' t ω - W' s ω) := fun s t =>
    ((hF.brownian.adapted t).mono (ℱ.le _) le_rfl).sub ((hF.brownian.adapted s).mono (ℱ.le _) le_rfl)
  have hκ : (Kernel.const Unit γ).comap (fun _ : Ω => ())
      (@measurable_const Unit Ω _ mΩ ()) = Kernel.const Ω γ := by
    ext ω : 1
    simp [Kernel.comap_apply]
  refine ⟨GF.gfb4_initFil (P.prod γ) ℱ, fun t ω' k => W' t ω'.1 k, ?_⟩
  have hbr : IsBrownianFiltration (P.prod γ) (GF.gfb4_initFil (P.prod γ) ℱ)
      (fun t ω' k => W' t ω'.1 k) :=
    { complete := fun t A hA hA0 =>
        (le_sup_right : HRS.nullSets (P.prod γ) ≤ _) _ (MeasurableSpace.measurableSet_generateFrom ⟨hA, hA0⟩)
      adapted := fun t => (hF.brownian.adapted t).comp (hπ' t)
      zero := fun ω => hF.brownian.zero _
      cont := fun ω => hF.brownian.cont _
      indep_incr := fun s t hst => by
        have h1 := GF.gfb4_indep_core P ℱ (s := (s : ℝ)) s.2 (ξ := fun _ : Ω => ())
          (@measurable_const Unit Ω _ (ℱ 0) ()) (Kernel.const Unit γ)
          (fun ω => W' t ω - W' s ω) (hΔm s t) (hF.brownian.indep_incr s t hst)
        rw [hκ, Measure.compProd_const] at h1
        exact GF.gfb4_indep_null (P.prod γ) h1
      gaussian_incr := fun s t hst => by
        have h := hF.brownian.gaussian_incr s t hst
        refine ⟨((hΔm s t).comp measurable_fst).aemeasurable, ?_⟩
        rw [show (fun ω' : Ω × E => W' t ω'.1 - W' s ω'.1) =
          (fun ω => W' t ω - W' s ω) ∘ Prod.fst from rfl, ← Measure.map_map (hΔm s t) measurable_fst,
          hπ.map_eq]
        exact h.map_eq }
  refine ⟨hbr, ?_, ?_, ?_⟩
  · filter_upwards [hπ.quasiMeasurePreserving.ae hF.coords] with w hw t i j
    exact hw t i j
  · intro t
    exact (hF.adapted t).comp (hπ' t)
  · intro i
    have h := hF.progressive i
    exact h.comp (measurable_fst.prodMk ((hπ' i).comp measurable_snd))

end HRS.AdjK
