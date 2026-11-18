import HRS.MC.CepH2Init3

/-!
# CEPH2, C4: the initial-data bound `F(Ĝ_ε * μ) ≤ 𝓗_U(μ) + e(ε)`, `e(ε) → 0`
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

theorem h2_integrable_moment_of_lintegral {μ : Measure (Ch N)} [IsFiniteMeasure μ]
    (h : ∫⁻ z, ENNReal.ofReal (‖h2_perp z‖ ^ 2) ∂μ < ⊤) : Integrable (fun y => ‖h2_perp y‖ ^ 2) μ :=
  ⟨(h2_continuous_perp.norm.pow 2).aestronglyMeasurable, by
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => by positivity)]; exact h⟩

theorem cepH2_initial_bound {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) (hUper : ∀ z, U (z + cep_diag N) = U z)
    {K : ℝ≥0} (hK : LipschitzWith K (gradient U))
    (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ U z)
    {θ : ℝ} (hθ : 0 < θ) {μ : Measure (Ch N)} [IsProbabilityMeasure μ]
    (hfin : cep_cylEntropy θ U μ < ⊤) :
    ∃ e : ℝ → ℝ, Tendsto e (𝓝[>] 0) (𝓝 0) ∧ ∀ ε : ℝ, 0 < ε →
      ((h2_free θ U (h2_mol θ ε μ) : ℝ) : EReal) ≤ cep_cylEntropy θ U μ + ((e ε : ℝ) : EReal) := by
  have hrel := h2_relEntropy_ne_top hfin
  unfold relEntropy at hrel
  obtain ⟨hcell, hm0⟩ := cepH2_moment_init_proof hU hconf hθ hfin
  have hmom := h2_integrable_moment_of_lintegral hm0
  obtain ⟨ρ, hρ, hρ0, hμeq, hρ1, hΦ⟩ := h2_density_of_finite hU.continuous hconf hθ hrel
  have hH := h2_cylEntropy_density hU.continuous hconf hθ hρ hρ0 hρ1 hΦ
  rw [hμeq] at hmom hfin
  rw [hμeq]
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by norm_num)
  haveI := h2_dMeas_prob hρ1
  set G : ℝ := ∫ y, ‖gradient U y‖ ^ 2 ∂(h2_dMeas ρ) with hG
  have hG0 : 0 ≤ G := integral_nonneg fun y => by positivity
  set H0 : ℝ := ∫ x in cep_cell N, (ρ x * Real.log (ρ x) + ρ x * U x / θ) with hH0
  set f : ℝ → ℝ := fun ε => (Real.sqrt ε / 2 * G + K * N * θ * ε + N * θ * Real.sqrt ε) / θ with hf
  refine ⟨f, ?_, fun ε hε => ?_⟩
  · have hc : Continuous f := by
      simp only [hf]
      have := Real.continuous_sqrt
      fun_prop
    have h0 : f 0 = 0 := by simp [hf]
    have := hc.tendsto 0
    rw [h0] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  · have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
    have hv : 0 < 2 * θ * ε := by positivity
    have h := h2_free_le hU hUper hK hconf hθ hρ hρ0 hρ1 hΦ hmom hv hs
    rw [← hG] at h
    rw [h2_mol_eq]
    rw [hH]
    set s : ℝ := Real.sqrt ε with hs'
    have hε' : ε = s * s := (Real.mul_self_sqrt hε.le).symm
    have h1 : 1 / (2 * s) * ((N : ℝ) * (2 * θ * ε)) = N * θ * s := by
      rw [hε']; field_simp
    have e : (s / 2 * G + ((K : ℝ) / 2 + 1 / (2 * s)) * (N * (2 * θ * ε))) / θ = f ε := by
      simp only [hf]
      have k2 : ((K : ℝ) / 2 + 1 / (2 * s)) * (N * (2 * θ * ε)) = K * N * θ * ε + 1 / (2 * s) * (N * (2 * θ * ε)) := by
        ring
      rw [k2, h1, ← hs']
      ring
    rw [e] at h
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    exact h

end HRS.MC.CepH2
