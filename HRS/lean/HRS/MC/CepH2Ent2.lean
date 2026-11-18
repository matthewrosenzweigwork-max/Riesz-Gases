import HRS.MC.CepH2Ent1

/-!
# CEPH2, entropy identification for measures with density on the cell
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

/-- The measure `ρ dx` restricted to the cell. -/
def h2_dMeas (ρ : Ch N → ℝ) : Measure (Ch N) :=
  ((volume : Measure (Ch N)).restrict (cep_cell N)).withDensity (fun x => ENNReal.ofReal (ρ x))

theorem h2_molMeas_eq (v : ℝ) (μ : Measure (Ch N)) : h2_molMeas v μ = h2_dMeas (h2_mu v μ) := rfl

section
variable {U : Ch N → ℝ} {θ : ℝ}

theorem h2_dMeas_prob {ρ : Ch N → ℝ} (h : ∫⁻ x in cep_cell N, ENNReal.ofReal (ρ x) = 1) :
    IsProbabilityMeasure (h2_dMeas ρ) := by
  refine ⟨?_⟩
  unfold h2_dMeas
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact h

theorem h2_dMeas_compl (ρ : Ch N → ℝ) : h2_dMeas ρ (cep_cell N)ᶜ = 0 := by
  unfold h2_dMeas
  rw [withDensity_apply _ h2_cell_measurable.compl, Measure.restrict_restrict h2_cell_measurable.compl,
    compl_inter_self]
  simp

theorem h2_llr_density (hU : Continuous U)
    (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ U z) (hθ : 0 < θ)
    {ρ : Ch N → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) :
    ∀ᵐ x ∂(h2_dMeas ρ), llr (h2_dMeas ρ) (cep_cylRef θ U) x =
      Real.log (ρ x) + Real.log (cep_cylPartition θ U).toReal + U x / θ := by
  have hZ0 := (h2_partition_pos hU θ).ne'
  have hZt := (h2_partition_lt_top hconf hθ).ne
  have hac : h2_dMeas ρ ≪ cep_cylRef θ U := h2_density_ac hU hconf hθ hρ
  haveI : IsProbabilityMeasure (cep_cylRef θ U) := h2_cylRef_prob hU hconf hθ
  have hrn0 := Measure.rnDeriv_withDensity (cep_cylRef θ U)
    (f := fun x => ENNReal.ofReal (ρ x) * (cep_cylPartition θ U * (cep_cylWeight θ U x)⁻¹))
    ((ENNReal.measurable_ofReal.comp hρ).mul (measurable_const.mul (h2_cylWeight_measurable hU θ).inv))
  rw [← h2_density_eq_ref hU hconf hθ hρ] at hrn0
  have hrn : (h2_dMeas ρ).rnDeriv (cep_cylRef θ U) =ᵐ[cep_cylRef θ U]
      (fun x => ENNReal.ofReal (ρ x) * (cep_cylPartition θ U * (cep_cylWeight θ U x)⁻¹)) := hrn0
  have hrn' := hac.ae_le hrn
  have hpos : ∀ᵐ x ∂(h2_dMeas ρ), 0 < ρ x := by
    unfold h2_dMeas
    rw [ae_withDensity_iff (f := fun x => ENNReal.ofReal (ρ x)) (ENNReal.measurable_ofReal.comp hρ)]
    refine Eventually.of_forall fun x hx => ?_
    rcases (hρ0 x).lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [← h]; simp) hx
  filter_upwards [hrn', hpos] with x hx hpx
  unfold llr
  rw [hx]
  have hw : cep_cylWeight θ U x = ENNReal.ofReal (Real.exp (-(U x) / θ)) := rfl
  have e1 : (ENNReal.ofReal (ρ x) * ((cep_cylPartition θ U) * (cep_cylWeight θ U x)⁻¹)).toReal =
      ρ x * ((cep_cylPartition θ U).toReal * (Real.exp (-(U x) / θ))⁻¹) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, hw, ENNReal.toReal_ofReal (hρ0 x),
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rw [e1]
  have hZr : 0 < (cep_cylPartition θ U).toReal := ENNReal.toReal_pos hZ0 hZt
  rw [Real.log_mul hpx.ne' (mul_pos hZr (inv_pos.2 (Real.exp_pos _))).ne', Real.log_mul hZr.ne'
    (inv_pos.2 (Real.exp_pos _)).ne', Real.log_inv, Real.log_exp]
  ring


theorem h2_integrable_of_lintegral {ρ : Ch N → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (h : ∫⁻ x in cep_cell N, ENNReal.ofReal (ρ x) = 1) : Integrable ρ (volume.restrict (cep_cell N)) := by
  refine ⟨hρ.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hρ0), h]
  exact ENNReal.one_lt_top

theorem h2_integral_of_lintegral {ρ : Ch N → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (h : ∫⁻ x in cep_cell N, ENNReal.ofReal (ρ x) = 1) : ∫ x in cep_cell N, ρ x = 1 := by
  have := ofReal_integral_eq_lintegral_ofReal (h2_integrable_of_lintegral hρ hρ0 h) (ae_of_all _ hρ0)
  rw [h] at this
  have h0 : 0 ≤ ∫ x in cep_cell N, ρ x := integral_nonneg hρ0
  rwa [← ENNReal.ofReal_one, ENNReal.ofReal_eq_ofReal_iff h0 zero_le_one] at this

theorem h2_klDiv_density (hU : Continuous U)
    (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ U z) (hθ : 0 < θ)
    {ρ : Ch N → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫⁻ x in cep_cell N, ENNReal.ofReal (ρ x) = 1)
    (hΦ : Integrable (fun x => ρ x * Real.log (ρ x) + ρ x * U x / θ) (volume.restrict (cep_cell N))) :
    klDiv (h2_dMeas ρ) (cep_cylRef θ U) ≠ ⊤ ∧
      (klDiv (h2_dMeas ρ) (cep_cylRef θ U)).toReal =
        (∫ x in cep_cell N, (ρ x * Real.log (ρ x) + ρ x * U x / θ)) +
          Real.log (cep_cylPartition θ U).toReal := by
  haveI := h2_dMeas_prob hρ1
  haveI := h2_cylRef_prob hU hconf hθ
  have hac : h2_dMeas ρ ≪ cep_cylRef θ U := h2_density_ac hU hconf hθ hρ
  have hρi := h2_integrable_of_lintegral hρ hρ0 hρ1
  set Lz : ℝ := Real.log (cep_cylPartition θ U).toReal with hLz
  have hfm : Measurable fun x => ENNReal.ofReal (ρ x) := ENNReal.measurable_ofReal.comp hρ
  have hflt : ∀ᵐ x ∂((volume : Measure (Ch N)).restrict (cep_cell N)), ENNReal.ofReal (ρ x) < ⊤ :=
    Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hsm : ∀ x, (ENNReal.ofReal (ρ x)).toReal • (Real.log (ρ x) + Lz + U x / θ) =
      (ρ x * Real.log (ρ x) + ρ x * U x / θ) + Lz * ρ x := fun x => by
    rw [ENNReal.toReal_ofReal (hρ0 x), smul_eq_mul]; ring
  have hℓ : Integrable (fun x => Real.log (ρ x) + Lz + U x / θ) (h2_dMeas ρ) := by
    unfold h2_dMeas
    rw [integrable_withDensity_iff_integrable_smul' hfm hflt]
    simp_rw [hsm]
    exact hΦ.add (hρi.const_mul Lz)
  have hllr := h2_llr_density hU hconf hθ hρ hρ0
  have hint : Integrable (llr (h2_dMeas ρ) (cep_cylRef θ U)) (h2_dMeas ρ) := hℓ.congr (by
    filter_upwards [hllr] with x hx using hx.symm)
  have h1 := toReal_klDiv hac hint
  refine ⟨?_, ?_⟩
  · rw [klDiv_of_ac_of_integrable hac hint]; exact ENNReal.ofReal_ne_top
  · rw [h1]
    simp only [probReal_univ, add_sub_cancel_right]
    rw [integral_congr_ae hllr]
    have e : ∫ x, (Real.log (ρ x) + Lz + U x / θ) ∂(h2_dMeas ρ) =
        ∫ x in cep_cell N, ((ρ x * Real.log (ρ x) + ρ x * U x / θ) + Lz * ρ x) := by
      unfold h2_dMeas
      rw [integral_withDensity_eq_integral_toReal_smul hfm hflt]
      exact integral_congr_ae (ae_of_all _ hsm)
    rw [e, integral_add hΦ (hρi.const_mul Lz), integral_const_mul, h2_integral_of_lintegral hρ hρ0 hρ1]
    ring

end

end HRS.MC.CepH2
