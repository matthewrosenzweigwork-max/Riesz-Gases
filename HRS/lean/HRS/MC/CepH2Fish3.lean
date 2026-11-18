import HRS.MC.CepH2Fish2

/-!
# CEPH2, C5 (b): lower semicontinuity of the cylinder Fisher information under mollification
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

theorem cepH2_fisher_lsc {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) (hUper : ∀ z, U (z + cep_diag N) = U z)
    {θ : ℝ} (hθ : 0 < θ) {μ : Measure (Ch N)} [IsProbabilityMeasure μ] {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    cep_cylFisher θ U μ ≤ liminf (fun n => ∫⁻ x in cep_cell N, ENNReal.ofReal (h2_dens θ (2 * θ * ε n) U μ x)) atTop := by
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by norm_num)
  set v : ℕ → ℝ := fun n => 2 * θ * ε n with hv
  have hvpos : ∀ n, 0 < v n := fun n => by have := hε n; simp only [hv]; positivity
  have hv0 : Tendsto v atTop (𝓝 0) := by
    have := hε0.const_mul (2 * θ)
    simpa [hv, mul_assoc] using this
  unfold cep_cylFisher
  refine iSup_le fun ζ => iSup_le fun hζ' => ?_
  obtain ⟨hζ, hper, hR⟩ := hζ'
  obtain ⟨R', hfar⟩ := h2_zeta_far hR
  obtain ⟨C, hC⟩ := h2_fint_bdd hU1 hUper θ hζ hper hfar
  have hψ := h2_fint_continuous hU1 θ hζ
  have hψper := fun z => h2_fint_periodic hUper θ hper z
  haveI : ∀ n, IsProbabilityMeasure (h2_molMeas (v n) μ) := fun n => h2_molMeas_prob (hvpos n) μ
  have hlim := h2_molMeas_tendsto μ hvpos hv0 hψ hψper hC
  have hlim' : Tendsto (fun n => ENNReal.ofReal (∫ z, h2_fint θ U ζ z ∂(h2_molMeas (v n) μ))) atTop
      (𝓝 (ENNReal.ofReal (∫ z, h2_fint θ U ζ z ∂μ))) := ENNReal.tendsto_ofReal hlim
  have hgoal : ENNReal.ofReal (∫ z, h2_fint θ U ζ z ∂μ) ≤
      liminf (fun n => ∫⁻ x in cep_cell N, ENNReal.ofReal (h2_dens θ (v n) U μ x)) atTop := by
    rw [← hlim'.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall fun n =>
      h2_fint_le_D1 hθ (hvpos n) hU1 hUper hζ hper hfar μ)
  exact hgoal

end HRS.MC.CepH2
