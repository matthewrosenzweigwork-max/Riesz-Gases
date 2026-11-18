import HRS.MC.CepH2Ent3

/-!
# CEPH2, the density of a measure with finite entropy, and the entropy as a free energy
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

section
variable {U : Ch N → ℝ} {θ : ℝ}

theorem h2_cylEntropy_density (hU : Continuous U)
    (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ U z) (hθ : 0 < θ)
    {ρ : Ch N → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫⁻ x in cep_cell N, ENNReal.ofReal (ρ x) = 1)
    (hΦ : Integrable (fun x => ρ x * Real.log (ρ x) + ρ x * U x / θ) (volume.restrict (cep_cell N))) :
    cep_cylEntropy θ U (h2_dMeas ρ) = (((∫ x in cep_cell N, (ρ x * Real.log (ρ x) + ρ x * U x / θ)) : ℝ) : EReal) := by
  obtain ⟨hne, hval⟩ := h2_klDiv_density hU hconf hθ hρ hρ0 hρ1 hΦ
  unfold cep_cylEntropy relEntropy
  rw [← EReal.coe_ennreal_toReal hne, hval, ← EReal.coe_sub]
  congr 1
  ring

/-- A probability measure with finite relative entropy has a density with the stated integrability. -/
theorem h2_density_of_finite (hU : Continuous U)
    (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ U z) (hθ : 0 < θ)
    {μ : Measure (Ch N)} [IsProbabilityMeasure μ] (h : klDiv μ (cep_cylRef θ U) ≠ ⊤) :
    ∃ ρ : Ch N → ℝ, Measurable ρ ∧ (∀ x, 0 ≤ ρ x) ∧ μ = h2_dMeas ρ ∧
      ∫⁻ x in cep_cell N, ENNReal.ofReal (ρ x) = 1 ∧
      Integrable (fun x => ρ x * Real.log (ρ x) + ρ x * U x / θ) (volume.restrict (cep_cell N)) := by
  haveI := h2_cylRef_prob hU hconf hθ
  set ν0 : Measure (Ch N) := (volume : Measure (Ch N)).restrict (cep_cell N) with hν0
  have hac : μ ≪ cep_cylRef θ U := by
    by_contra hna; exact h (klDiv_of_not_ac hna)
  have hint : Integrable (llr μ (cep_cylRef θ U)) μ := by
    by_contra hni; exact h (klDiv_of_not_integrable hni)
  have hrefac : cep_cylRef θ U ≪ ν0 := by
    rw [h2_cylRef_eq hU θ]; exact withDensity_absolutelyContinuous _ _
  have hac2 : μ ≪ ν0 := hac.trans hrefac
  set ρ : Ch N → ℝ := fun x => (μ.rnDeriv ν0 x).toReal with hρdef
  have hρ : Measurable ρ := (Measure.measurable_rnDeriv μ ν0).ennreal_toReal
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => ENNReal.toReal_nonneg
  have hμeq : μ = h2_dMeas ρ := by
    unfold h2_dMeas
    have h1 : μ = ν0.withDensity (μ.rnDeriv ν0) := (Measure.withDensity_rnDeriv_eq μ ν0 hac2).symm
    conv_lhs => rw [h1]
    refine withDensity_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top μ ν0] with x hx
    simp only [hρdef]
    rw [ENNReal.ofReal_toReal hx.ne]
  have hρ1 : ∫⁻ x in cep_cell N, ENNReal.ofReal (ρ x) = 1 := by
    have h1 : (h2_dMeas ρ) univ = ∫⁻ x in cep_cell N, ENNReal.ofReal (ρ x) := by
      unfold h2_dMeas
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← h1, ← hμeq, measure_univ]
  refine ⟨ρ, hρ, hρ0, hμeq, hρ1, ?_⟩
  -- integrability of the free energy density
  have hρi := h2_integrable_of_lintegral hρ hρ0 hρ1
  have hllr := h2_llr_density hU hconf hθ hρ hρ0
  rw [hμeq] at hint
  set Lz : ℝ := Real.log (cep_cylPartition θ U).toReal with hLz
  have hℓ : Integrable (fun x => Real.log (ρ x) + Lz + U x / θ) (h2_dMeas ρ) :=
    hint.congr (by filter_upwards [hllr] with x hx using hx)
  have hfm : Measurable fun x => ENNReal.ofReal (ρ x) := ENNReal.measurable_ofReal.comp hρ
  have hflt : ∀ᵐ x ∂ν0, ENNReal.ofReal (ρ x) < ⊤ := Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hℓ' := hℓ
  unfold h2_dMeas at hℓ'
  rw [integrable_withDensity_iff_integrable_smul' hfm hflt] at hℓ'
  have hsm : ∀ x, (ENNReal.ofReal (ρ x)).toReal • (Real.log (ρ x) + Lz + U x / θ) =
      (ρ x * Real.log (ρ x) + ρ x * U x / θ) + Lz * ρ x := fun x => by
    rw [ENNReal.toReal_ofReal (hρ0 x), smul_eq_mul]; ring
  have : Integrable (fun x => ((ρ x * Real.log (ρ x) + ρ x * U x / θ) + Lz * ρ x) - Lz * ρ x) ν0 := by
    refine Integrable.sub (hℓ'.congr (ae_of_all _ hsm)) (hρi.const_mul Lz)
  refine this.congr (ae_of_all _ fun x => ?_)
  simp only; ring

end

end HRS.MC.CepH2
