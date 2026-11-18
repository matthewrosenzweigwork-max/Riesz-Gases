import HRS.MC.Q714GTCoreThm

/-!
# Packet GT (row 7.14): `gaussian_taylor_proof`

The statement of `HRS.MC.Q714.gaussian_taylor` (copied verbatim), proved by passing to the laws of `G₁, G₂`
and applying `gt_core`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open HRS

noncomputable section

namespace HRS.MC.Q714.GT

theorem gaussian_taylor_proof {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    {Ω₁ : Type} [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁] (G₁ : Ω₁ → B)
    {Ω₂ : Type} [MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂] (G₂ : Ω₂ → B)
    (hG₁m : AEMeasurable G₁ P₁) (hG₂m : AEMeasurable G₂ P₂)
    (hG₁ : IsCenteredGaussian (law P₁ G₁)) (hG₂ : IsCenteredGaussian (law P₂ G₂))
    (Δ : (B [×2]→L[ℝ] ℝ) → ℝ)
    (hΔ : ∀ M : B [×2]→L[ℝ] ℝ,
      Δ M = ∫ ω, M ![G₂ ω, G₂ ω] ∂P₂ - ∫ ω, M ![G₁ ω, G₁ ω] ∂P₁)
    (δ : ℝ) (hδ : ∀ M : B [×2]→L[ℝ] ℝ, ‖M‖ ≤ 1 → |Δ M| ≤ δ)
    (Φ : B → ℝ) (hΦ : MemCb 4 Φ) (C₂ C₄ : ℝ)
    (hC₂ : ∀ y, ‖iteratedFDeriv ℝ 2 Φ y‖ ≤ C₂) (hC₄ : ∀ y, ‖iteratedFDeriv ℝ 4 Φ y‖ ≤ C₄) :
    |∫ ω, Φ (G₂ ω) ∂P₂ - ∫ ω, Φ (G₁ ω) ∂P₁| ≤ C₂ * δ / 2 ∧
    |∫ ω, Φ (G₂ ω) ∂P₂ - ∫ ω, Φ (G₁ ω) ∂P₁ -
        (1 / 2) * ∫ ω, Δ (iteratedFDeriv ℝ 2 Φ (G₁ ω)) ∂P₁| ≤ C₄ * δ ^ 2 / 8 := by
  have hmeasM : ∀ M : B [×2]→L[ℝ] ℝ, Continuous fun z : B => M ![z, z] := fun M =>
    M.cont.comp (continuous_pi fun i => by fin_cases i <;> exact continuous_id)
  have hΔ' : ∀ M : B [×2]→L[ℝ] ℝ,
      Δ M = ∫ z, M ![z, z] ∂(P₂.map G₂) - ∫ z, M ![z, z] ∂(P₁.map G₁) := by
    intro M
    rw [hΔ, integral_map hG₂m (hmeasM M).aestronglyMeasurable,
      integral_map hG₁m (hmeasM M).aestronglyMeasurable]
  have hΦc : Continuous Φ := hΦ.1.continuous
  have hcore := gt_core hG₁ hG₂ Δ hΔ' δ hδ Φ hΦ C₂ C₄ hC₂ hC₄
  have e1 : ∫ ω, Φ (G₁ ω) ∂P₁ = ∫ z, Φ z ∂(P₁.map G₁) :=
    (integral_map hG₁m hΦc.aestronglyMeasurable).symm
  have e2 : ∫ ω, Φ (G₂ ω) ∂P₂ = ∫ z, Φ z ∂(P₂.map G₂) :=
    (integral_map hG₂m hΦc.aestronglyMeasurable).symm
  have hs₁ := gaussian_sqnorm_integrable hG₁
  have hs₂ := gaussian_sqnorm_integrable hG₂
  obtain ⟨L, hLΔ, -, -⟩ := gt_delta_clm hs₁ hs₂ Δ hΔ' δ hδ
  have hcont : Continuous fun z : B => Δ (iteratedFDeriv ℝ 2 Φ z) := by
    have : (fun z : B => Δ (iteratedFDeriv ℝ 2 Φ z)) = fun z => L (iteratedFDeriv ℝ 2 Φ z) := by
      funext z; rw [hLΔ]
    rw [this]
    exact L.continuous.comp (hΦ.1.continuous_iteratedFDeriv (m := 2) (by norm_num))
  have e3 : ∫ ω, Δ (iteratedFDeriv ℝ 2 Φ (G₁ ω)) ∂P₁ =
      ∫ z, Δ (iteratedFDeriv ℝ 2 Φ z) ∂(P₁.map G₁) :=
    (integral_map hG₁m hcont.aestronglyMeasurable).symm
  rw [e1, e2, e3]
  exact hcore

end HRS.MC.Q714.GT

end
