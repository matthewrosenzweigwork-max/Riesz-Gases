import HRS.MC.CepH2Core3
import HRS.MC.CepH2Sde6

/-!
# CEPH2, A: the entropy dissipation inequality for strong solutions with Lipschitz gradient
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N] {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem h2_weakFP_max {θ : ℝ} {U : Ch N → ℝ} {ν : ℝ → Measure (Ch N)} (h : H2WeakFP θ U ν) :
    H2WeakFP θ U (fun t => ν (max t 0)) := by
  intro g hg t ht
  have := h g hg t ht
  simp only [max_eq_left ht, max_self]
  rw [this]
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  simp only [max_eq_left hs.1]

theorem cepH2_lipschitz_case' [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) (hUper : ∀ z, U (z + cep_diag N) = U z)
    (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ U z)
    {K : ℝ≥0} (hK : LipschitzWith K (gradient U))
    {θ : ℝ} (hθ : 0 < θ) {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) {Z : ℝ → Ω → Ch N}
    (hZ : cep_IsChamberSolution P ℱ W' π (Real.sqrt (2 * θ)) (fun z => -(gradient U z)) z₀ Z)
    (hfin : cep_cylEntropy θ U (P.map fun ω => cep_reduce (z₀ ω)) < ⊤) :
    ∃ D : ℝ → ℝ≥0∞, (∀ T : ℝ, AEMeasurable D (volume.restrict (Icc (0 : ℝ) T))) ∧
      (∀ r : ℝ, 0 ≤ r → cep_cylFisher θ U (P.map fun ω => cep_reduce (Z r ω)) ≤ D r) ∧
      ∀ t : ℝ, 0 ≤ t →
        cep_cylEntropy θ U (P.map fun ω => cep_reduce (Z t ω))
          + ((ENNReal.ofReal θ * ∫⁻ r in Icc (0 : ℝ) t, D r : ℝ≥0∞) : EReal)
          ≤ cep_cylEntropy θ U (P.map fun ω => cep_reduce (z₀ ω)) := by
  have hz0m : Measurable z₀ := hz₀.mono (ℱ.le 0) le_rfl
  have hZm : ∀ t : ℝ, 0 ≤ t → Measurable (Z t) := fun t ht => (hZ.2.1 t ht).mono (ℱ.le t) le_rfl
  have hZmax : ∀ t : ℝ, Measurable (Z (max t 0)) := fun t => hZm _ (le_max_right _ _)
  set μ' : ℝ → Measure (Ch N) := fun t => P.map fun ω => cep_reduce (Z (max t 0) ω) with hμ'
  haveI hprob : ∀ t, IsProbabilityMeasure (μ' t) := fun t =>
    (Measure.isProbabilityMeasure_map_iff (h2_measurable_reduce.comp (hZmax t)).aemeasurable).2 inferInstance
  have hμeq : ∀ t : ℝ, 0 ≤ t → μ' t = P.map fun ω => cep_reduce (Z t ω) := fun t ht => by
    simp only [hμ', max_eq_left ht]
  -- initial law
  have hZ0 : ∀ᵐ ω ∂P, Z 0 ω = z₀ ω := by
    filter_upwards [hZ.2.2] with ω h
    have := h 0 le_rfl
    have hn : cep_noise π W' 0 ω = 0 := by
      ext k
      simp [cep_noise, hW'.zero]
    rw [this, hn]
    simp
  have hμ0 : μ' 0 = P.map fun ω => cep_reduce (z₀ ω) := by
    rw [hμeq 0 le_rfl]
    refine Measure.map_congr ?_
    filter_upwards [hZ0] with ω h
    rw [h]
  haveI hprob0 : IsProbabilityMeasure (P.map fun ω => cep_reduce (z₀ ω)) :=
    (Measure.isProbabilityMeasure_map_iff (h2_measurable_reduce.comp hz0m).aemeasurable).2 inferInstance
  obtain ⟨hcell0, hm0'⟩ := cepH2_moment_init_proof hU hconf hθ hfin
  have hmeasf : Measurable fun z : Ch N => ENNReal.ofReal (‖h2_perp z‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (h2_continuous_perp.norm.pow 2).measurable
  have hm0 : ∫⁻ ω, ENNReal.ofReal (‖h2_perp (z₀ ω)‖ ^ 2) ∂P < ⊤ := by
    have hred0 : Measurable fun ω => cep_reduce (z₀ ω) := h2_measurable_reduce.comp hz0m
    rw [lintegral_map hmeasf hred0] at hm0'
    simpa only [Function.comp, h2_perp_reduce] using hm0'
  have hcell : ∀ t, 0 ≤ t → μ' t (cep_cell N)ᶜ = 0 := fun t ht => by
    have hredt : Measurable fun ω => cep_reduce (Z (max t 0) ω) := h2_measurable_reduce.comp (hZmax t)
    rw [hμ', Measure.map_apply hredt h2_cell_measurable.compl]
    have : (fun ω => cep_reduce (Z (max t 0) ω)) ⁻¹' (cep_cell N)ᶜ = ∅ := by
      ext ω
      simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
      exact h2_reduce_mem_cell _
    rw [this, measure_empty]
  have hfp : H2WeakFP θ U μ' :=
    h2_weakFP_max (cepH2_weakFP_of_sde_proof hW' hπ hU hUper hK hθ hz₀ hZ)
  have hfin' : cep_cylEntropy θ U (μ' 0) < ⊤ := by rw [hμ0]; exact hfin
  have core : ∀ T : ℝ, 0 ≤ T →
      AEMeasurable (h2_Dlim θ U μ') (volume.restrict (Icc (0 : ℝ) T)) ∧
      (∀ r ∈ Icc (0 : ℝ) T, cep_cylFisher θ U (μ' r) ≤ h2_Dlim θ U μ' r) ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        cep_cylEntropy θ U (μ' t) + ((ENNReal.ofReal θ * ∫⁻ r in Icc (0 : ℝ) t, h2_Dlim θ U μ' r : ℝ≥0∞) : EReal)
          ≤ cep_cylEntropy θ U (μ' 0) := by
    intro T hT
    obtain ⟨M, hMtop, hM⟩ := cepH2_moment_flow_proof hW' hπ hU hUper hK hθ hz₀ hZ hm0 T
    refine cepH2_core' hU hUper hconf hK hθ hcell hT ⟨M, hMtop, fun t ht => ?_⟩ ?_ hfp hfin'
    · have hredt : Measurable fun ω => cep_reduce (Z t ω) := h2_measurable_reduce.comp (hZm t ht.1)
      rw [hμeq t ht.1, lintegral_map hmeasf hredt]
      simpa only [Function.comp, h2_perp_reduce] using hM t ht
    · intro g hg hper hb
      have := cepH2_narrow_of_paths (P := P) (ℱ := ℱ) (fun t ht => hZ.2.1 t ht) hZ.1 T hg hper hb
      exact this.congr fun t ht => by rw [hμeq t ht.1]
  refine ⟨h2_Dlim θ U μ', fun T => ?_, fun r hr => ?_, fun t ht => ?_⟩
  · exact ((core (max T 0) (le_max_right _ _)).1).mono_set (Icc_subset_Icc le_rfl (le_max_left _ _))
  · have := (core r hr).2.1 r ⟨hr, le_rfl⟩
    rwa [hμeq r hr] at this
  · have := (core t ht).2.2 t ⟨ht, le_rfl⟩
    rwa [hμeq t ht, hμ0] at this

end HRS.MC.CepH2
