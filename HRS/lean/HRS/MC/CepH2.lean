import HRS.MC.CepH2Mov3
import HRS.MC.CepH2Loc2

/-!
# Packet CEPH2: entropy dissipation for the regularised chamber flow (`cep_H2_cylinder_entropy`)

`HRS.MC.CepH2.cep_H2_cylinder_entropy_proof` has the statement of `HRS.MC.Cepa.cep_H2_cylinder_entropy`.
Route: freeze the potential outside the tube `‖P⊥ z‖ < n` (`cepH2_freeze`), solve the SDE for the frozen
(Lipschitz-gradient) potentials (CepE3), prove the dissipation inequality for them (`cepH2_lipschitz_case'`),
identify the limit pathwise (`cepH2_loc_tendsto`) and pass to the limit by lower semicontinuity
(`cepH2_freeze_limit`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem h2_law_prob [NeZero N] [IsProbabilityMeasure P] {Y : Ω → Ch N} (hY : Measurable Y) :
    IsProbabilityMeasure (P.map fun ω => cep_reduce (Y ω)) :=
  (Measure.isProbabilityMeasure_map_iff (h2_measurable_reduce.comp hY).aemeasurable).2 inferInstance

theorem h2_law_cell [NeZero N] {Y : Ω → Ch N} (hY : Measurable Y) :
    (P.map fun ω => cep_reduce (Y ω)) (cep_cell N)ᶜ = 0 := by
  rw [Measure.map_apply (f := fun ω => cep_reduce (Y ω)) (h2_measurable_reduce.comp hY) h2_cell_measurable.compl]
  have : (fun ω => cep_reduce (Y ω)) ⁻¹' (cep_cell N)ᶜ = ∅ := by
    ext ω
    simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
    exact h2_reduce_mem_cell _
  rw [this, measure_empty]

theorem h2_Z0_ae [NeZero N] [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} {σ' : ℝ} {B : Ch N → Ch N} {z₀ : Ω → Ch N} {Z : ℝ → Ω → Ch N}
    (hZ : cep_IsChamberSolution P ℱ W' π σ' B z₀ Z) : ∀ᵐ ω ∂P, Z 0 ω = z₀ ω := by
  filter_upwards [hZ.2.2] with ω h
  have := h 0 le_rfl
  have hn : cep_noise π W' 0 ω = 0 := by
    ext k
    simp [cep_noise, hW'.zero]
  rw [this, hn]
  simp

theorem cep_H2_cylinder_entropy_proof [IsProbabilityMeasure P] [NeZero N] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {U : Ch N → ℝ} (hU : ContDiff ℝ 2 U) (hUper : ∀ z, U (z + cep_diag N) = U z)
    (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ U z)
    {invβ : ℝ} (hβ : 0 < invβ) {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀)
    {Z : ℝ → Ω → Ch N}
    (hZ : cep_IsChamberSolution P ℱ W' π (Real.sqrt (2 * invβ)) (fun z => -(gradient U z)) z₀ Z)
    (hfin : cep_cylEntropy invβ U (P.map fun ω => cep_reduce (z₀ ω)) < ⊤) :
    ∀ t : ℝ, 0 ≤ t →
      cep_cylEntropy invβ U (P.map fun ω => cep_reduce (Z t ω))
        + ((ENNReal.ofReal invβ * ∫⁻ r in Set.Icc (0 : ℝ) t,
            cep_cylFisher invβ U (P.map fun ω => cep_reduce (Z r ω)) : ℝ≥0∞) : EReal)
        ≤ cep_cylEntropy invβ U (P.map fun ω => cep_reduce (z₀ ω)) := by
  obtain ⟨Un, K, hUnd, hUnper, hLip, ⟨c, C, hc, hlow⟩, hUnU, hUnle⟩ := cepH2_freeze hU hUper hconf
  have hex : ∀ n, ∃ Zn : ℝ → Ω → Ch N, cep_IsChamberSolution P ℱ W' π (Real.sqrt (2 * invβ))
      (fun z => -(gradient (Un n) z)) z₀ Zn := fun n =>
    HRS.MC.CepE3.cep_E3_regularised_sde_proof hW' hπ (B := fun z => -(gradient (Un n) z)) (L := K n)
      ((hLip n).neg) (Real.sqrt (2 * invβ)) hz₀
  choose Zn hZn using hex
  have hz0m : Measurable z₀ := hz₀.mono (ℱ.le 0) le_rfl
  have hZm : ∀ t : ℝ, 0 ≤ t → Measurable (Z t) := fun t ht => (hZ.2.1 t ht).mono (ℱ.le t) le_rfl
  have hZnm : ∀ n, ∀ t : ℝ, 0 ≤ t → Measurable (Zn n t) := fun n t ht => ((hZn n).2.1 t ht).mono (ℱ.le t) le_rfl
  haveI hν0 : IsProbabilityMeasure (P.map fun ω => cep_reduce (z₀ ω)) := h2_law_prob hz0m
  have hlaw0 : P.map (fun ω => cep_reduce (Z 0 ω)) = P.map fun ω => cep_reduce (z₀ ω) := by
    refine Measure.map_congr ?_
    filter_upwards [h2_Z0_ae hW' hZ] with ω h
    rw [h]
  have hlawn0 : ∀ n, P.map (fun ω => cep_reduce (Zn n 0 ω)) = P.map fun ω => cep_reduce (z₀ ω) := fun n => by
    refine Measure.map_congr ?_
    filter_upwards [h2_Z0_ae hW' (hZn n)] with ω h
    rw [h]
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ → Measure (Ch N), ∀ t, μ t = P.map fun ω => cep_reduce (Z (max t 0) ω) :=
    ⟨_, fun t => rfl⟩
  obtain ⟨μn, hμn⟩ : ∃ μn : ℕ → ℝ → Measure (Ch N),
      ∀ n t, μn n t = P.map fun ω => cep_reduce (Zn n (max t 0) ω) := ⟨_, fun n t => rfl⟩
  haveI hμp : ∀ t, IsProbabilityMeasure (μ t) := fun t => by
    rw [hμ t]; exact h2_law_prob (hZm _ (le_max_right _ _))
  haveI hμnp : ∀ n t, IsProbabilityMeasure (μn n t) := fun n t => by
    rw [hμn n t]; exact h2_law_prob (hZnm n _ (le_max_right _ _))
  have hμt : ∀ t : ℝ, 0 ≤ t → μ t = P.map fun ω => cep_reduce (Z t ω) := fun t ht => by
    rw [hμ t, max_eq_left ht]
  have hμnt : ∀ n, ∀ t : ℝ, 0 ≤ t → μn n t = P.map fun ω => cep_reduce (Zn n t ω) := fun n t ht => by
    rw [hμn n t, max_eq_left ht]
  have hμ0 : μ 0 = P.map fun ω => cep_reduce (z₀ ω) := by rw [hμt 0 le_rfl, hlaw0]
  have hμn0 : ∀ n, μn n 0 = P.map fun ω => cep_reduce (z₀ ω) := fun n => by rw [hμnt n 0 le_rfl, hlawn0 n]
  have hcellμ : ∀ t, 0 ≤ t → μ t (cep_cell N)ᶜ = 0 := fun t ht => by
    rw [hμt t ht]; exact h2_law_cell (hZm t ht)
  have hfin' : cep_cylEntropy invβ U (μ 0) < ⊤ := by rw [hμ0]; exact hfin
  have htv : ∀ t, 0 ≤ t → ∀ ψ : Ch N → ℝ, Continuous ψ → (∀ z, ψ (z + cep_diag N) = ψ z) →
      (∃ C, ∀ z, |ψ z| ≤ C) → Tendsto (fun n => ∫ z, ψ z ∂(μn n t)) atTop (𝓝 (∫ z, ψ z ∂(μ t))) := by
    intro t ht ψ hψ _ hb
    have := cepH2_loc_tendsto (P := P) (ℱ := ℱ) (W' := W') (π := π) hU hLip hUnU hZ hZn ht hψ.measurable hb
    have e : ∀ Y : Ω → Ch N, Measurable Y → ∫ z, ψ z ∂(P.map fun ω => cep_reduce (Y ω)) =
        ∫ ω, ψ (cep_reduce (Y ω)) ∂P := fun Y hY =>
      integral_map (h2_measurable_reduce.comp hY).aemeasurable hψ.aestronglyMeasurable
    simp_rw [hμnt _ t ht, hμt t ht]
    simp_rw [e _ (hZnm _ t ht), e _ (hZm t ht)]
    exact this
  have hdiss : ∀ n, ∃ D : ℝ → ℝ≥0∞, (∀ T : ℝ, AEMeasurable D (volume.restrict (Icc (0 : ℝ) T))) ∧
      (∀ r : ℝ, 0 ≤ r → cep_cylFisher invβ (Un n) (μn n r) ≤ D r) ∧
      ∀ t : ℝ, 0 ≤ t → cep_cylEntropy invβ (Un n) (μn n t)
          + ((ENNReal.ofReal invβ * ∫⁻ r in Icc (0 : ℝ) t, D r : ℝ≥0∞) : EReal)
          ≤ cep_cylEntropy invβ (Un n) (μn n 0) := by
    intro n
    have hfinn : cep_cylEntropy invβ (Un n) (P.map fun ω => cep_reduce (z₀ ω)) < ⊤ :=
      lt_of_le_of_lt (h2_entropy_mono (hU.of_le (by norm_num)) hconf hβ (hUnd n).continuous (hUnle n) ⟨c, C, hc, hlow n⟩ hfin) hfin
    obtain ⟨D, hDm, hDF, hDE⟩ := cepH2_lipschitz_case' hW' hπ ((hUnd n).of_le (by norm_num)) (hUnper n) ⟨c, C, hc, hlow n⟩ (hLip n)
      hβ hz₀ (hZn n) hfinn
    refine ⟨D, hDm, fun r hr => ?_, fun t ht => ?_⟩
    · rw [hμnt n r hr]; exact hDF r hr
    · rw [hμnt n t ht, hμn0 n]; exact hDE t ht
  have key := cepH2_freeze_limit hU hUper hconf hc (fun n => (hUnd n).continuous) hlow hUnle hUnU hβ
    (μ := μ) (μn := μn) hcellμ (fun n => (hμn0 n).trans hμ0.symm) hfin' htv hdiss
  intro t ht
  have := key t ht
  rw [hμt t ht, hμ0] at this
  have e : ∫⁻ r in Icc (0 : ℝ) t, cep_cylFisher invβ U (μ r) =
      ∫⁻ r in Icc (0 : ℝ) t, cep_cylFisher invβ U (P.map fun ω => cep_reduce (Z r ω)) :=
    setLIntegral_congr_fun measurableSet_Icc fun r hr => by rw [hμt r hr.1]
  rw [e] at this
  exact this

end HRS.MC.CepH2
