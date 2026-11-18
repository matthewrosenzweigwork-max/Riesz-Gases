import HRS.MC.CepH2Comp3

/-!
# CEPH2, identification of the cylinder entropy of a measure with density on the cell
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

/-- The single-time `H2Set` (constant family on `[0,0]`). -/
theorem h2_set_const {θ v : ℝ} {U : Ch N → ℝ} {K : ℝ≥0} (hθ : 0 < θ) (hv : 0 < v) (hU : ContDiff ℝ 1 U)
    (hUper : ∀ z, U (z + cep_diag N) = U z) (hK : LipschitzWith K (gradient U)) (μ : Measure (Ch N))
    [IsProbabilityMeasure μ] (hcell : μ (cep_cell N)ᶜ = 0) (hmom : Integrable (fun y => ‖h2_perp y‖ ^ 2) μ) :
    H2Set θ v U K (fun _ => μ) 0 (∫ y, ‖h2_perp y‖ ^ 2 ∂μ) where
  hθ := hθ
  hv := hv
  hU := hU
  hUper := hUper
  hK := hK
  hT := le_rfl
  hprob := fun _ => inferInstance
  hcell := fun _ => hcell
  hmom := fun _ => hmom
  hM := fun _ => le_rfl
  hnar := fun g _ _ _ => continuous_const
  hfp := fun g _ t ht => by
    have : t = 0 := le_antisymm ht.2 ht.1
    subst this
    simp

theorem h2_integrable_Phi_single {θ v : ℝ} {U : Ch N → ℝ} {K : ℝ≥0} (hθ : 0 < θ) (hv : 0 < v)
    (hU : ContDiff ℝ 1 U) (hUper : ∀ z, U (z + cep_diag N) = U z) (hK : LipschitzWith K (gradient U))
    (μ : Measure (Ch N)) [IsProbabilityMeasure μ] (hcell : μ (cep_cell N)ᶜ = 0)
    (hmom : Integrable (fun y => ‖h2_perp y‖ ^ 2) μ) :
    Integrable (fun x => h2_mu v μ x * Real.log (h2_mu v μ x) + h2_mu v μ x * U x / θ)
      (volume.restrict (cep_cell N)) :=
  (h2_set_const hθ hv hU hUper hK μ hcell hmom).integrable_Phi 0

section
variable {U : Ch N → ℝ} {θ : ℝ}

theorem h2_cylWeight_pos (θ : ℝ) (U : Ch N → ℝ) (x : Ch N) : 0 < cep_cylWeight θ U x :=
  ENNReal.ofReal_pos.2 (Real.exp_pos _)

theorem h2_cylWeight_ne_top (θ : ℝ) (U : Ch N → ℝ) (x : Ch N) : cep_cylWeight θ U x ≠ ⊤ :=
  ENNReal.ofReal_ne_top

theorem h2_cylRef_eq (hU : Continuous U) (θ : ℝ) :
    cep_cylRef θ U = ((volume : Measure (Ch N)).restrict (cep_cell N)).withDensity
      (fun x => (cep_cylPartition θ U)⁻¹ * cep_cylWeight θ U x) := by
  unfold cep_cylRef
  have := withDensity_smul (μ := (volume : Measure (Ch N)).restrict (cep_cell N))
    (cep_cylPartition θ U)⁻¹ (h2_cylWeight_measurable hU θ)
  rw [← this]
  rfl

/-- The density of `ρ dx|_cell` with respect to the Gibbs reference. -/
theorem h2_density_eq_ref (hU : Continuous U)
    (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ U z) (hθ : 0 < θ)
    {ρ : Ch N → ℝ} (hρ : Measurable ρ) :
    ((volume : Measure (Ch N)).restrict (cep_cell N)).withDensity (fun x => ENNReal.ofReal (ρ x)) =
      (cep_cylRef θ U).withDensity
        (fun x => ENNReal.ofReal (ρ x) * (cep_cylPartition θ U * (cep_cylWeight θ U x)⁻¹)) := by
  have hZ0 := (h2_partition_pos hU θ).ne'
  have hZt := (h2_partition_lt_top hconf hθ).ne
  have hwm := h2_cylWeight_measurable hU θ
  have hfm : Measurable fun x => ENNReal.ofReal (ρ x) := ENNReal.measurable_ofReal.comp hρ
  have key : ((volume : Measure (Ch N)).restrict (cep_cell N)).withDensity
      (fun x => ((cep_cylPartition θ U)⁻¹ * cep_cylWeight θ U x) *
        (ENNReal.ofReal (ρ x) * (cep_cylPartition θ U * (cep_cylWeight θ U x)⁻¹))) =
      (((volume : Measure (Ch N)).restrict (cep_cell N)).withDensity
        (fun x => (cep_cylPartition θ U)⁻¹ * cep_cylWeight θ U x)).withDensity
        (fun x => ENNReal.ofReal (ρ x) * (cep_cylPartition θ U * (cep_cylWeight θ U x)⁻¹)) :=
    withDensity_mul _ (measurable_const.mul hwm) (hfm.mul (measurable_const.mul hwm.inv))
  rw [h2_cylRef_eq hU θ, ← key]
  congr 1
  funext x
  have h1 := h2_cylWeight_pos θ U x
  have h2 := h2_cylWeight_ne_top θ U x
  calc ENNReal.ofReal (ρ x) = ENNReal.ofReal (ρ x) * (((cep_cylPartition θ U)⁻¹ * cep_cylPartition θ U) *
        (cep_cylWeight θ U x * (cep_cylWeight θ U x)⁻¹)) := by
        rw [ENNReal.inv_mul_cancel hZ0 hZt, ENNReal.mul_inv_cancel h1.ne' h2]; simp
    _ = _ := by ring

theorem h2_density_ac (hU : Continuous U)
    (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ U z) (hθ : 0 < θ)
    {ρ : Ch N → ℝ} (hρ : Measurable ρ) :
    ((volume : Measure (Ch N)).restrict (cep_cell N)).withDensity (fun x => ENNReal.ofReal (ρ x)) ≪
      cep_cylRef θ U := by
  rw [h2_density_eq_ref hU hconf hθ hρ]
  exact withDensity_absolutelyContinuous _ _

end

end HRS.MC.CepH2
