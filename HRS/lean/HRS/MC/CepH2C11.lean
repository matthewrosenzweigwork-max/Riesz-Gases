import HRS.MC.CepH2Lip1

/-!
# Packet CEPH2C11: `cep_H2_c11_cylinder_entropy` (H2 for a `C^{1,1}` potential)

Direct consequence of `HRS.MC.CepH2.cepH2_lipschitz_case'`, which needs only `U ∈ C¹` with Lipschitz gradient.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2C11

open HRS HRS.MC.Cepa

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem cep_H2_c11_cylinder_entropy_proof [IsProbabilityMeasure P] [NeZero N] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) {K : ℝ≥0} (hK : LipschitzWith K (gradient U))
    (hUper : ∀ z, U (z + cep_diag N) = U z)
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
  obtain ⟨D, -, hDF, hDE⟩ := HRS.MC.CepH2.cepH2_lipschitz_case' hW' hπ hU hUper hconf hK hβ hz₀ hZ hfin
  intro t ht
  refine le_trans (add_le_add le_rfl ?_) (hDE t ht)
  refine EReal.coe_ennreal_le_coe_ennreal_iff.2 (mul_le_mul_right ?_ _)
  exact setLIntegral_mono' measurableSet_Icc fun r hr => hDF r hr.1

end HRS.MC.CepH2C11
