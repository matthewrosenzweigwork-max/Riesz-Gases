import HRS.MC.Q714GTCoreThm

/-!
# E214P1 (L1): first-order Gaussian comparison for `C²` test functions

`gaussian_taylor_proof` demands `MemCb 4`; the function `f = 𝒦 ∘ D³Φ` of the hybrid correction is only `C²`.  The first
conjunct of `gt_core` uses only the interpolation `gt_interp` for `Φ` itself, so it holds for `C²` functions with bounded
`Φ, DΦ, D²Φ`: for two centred Gaussian laws whose second-moment forms differ by at most `δ` on the unit ball,
`|E Θ(G₂) - E Θ(G₁)| ≤ K δ / 2` where `K` bounds `‖D²Θ‖`.
-/

open MeasureTheory ProbabilityTheory
open HRS

noncomputable section

namespace HRS.MC.E214P

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]

/-- Law-level first-order comparison for a `C²` function with bounded value, gradient and Hessian. -/
theorem p1_first_core {γ₁ γ₂ : Measure B} [IsProbabilityMeasure γ₁] [IsProbabilityMeasure γ₂]
    (h₁ : IsCenteredGaussian γ₁) (h₂ : IsCenteredGaussian γ₂)
    (Δ : (B [×2]→L[ℝ] ℝ) → ℝ)
    (hΔ : ∀ M : B [×2]→L[ℝ] ℝ, Δ M = ∫ z, M ![z, z] ∂γ₂ - ∫ z, M ![z, z] ∂γ₁)
    (δ : ℝ) (hδ : ∀ M : B [×2]→L[ℝ] ℝ, ‖M‖ ≤ 1 → |Δ M| ≤ δ)
    {Θ : B → ℝ} (hΘ : ContDiff ℝ 2 Θ) {M0 M1 K : ℝ}
    (hM0 : ∀ w, |Θ w| ≤ M0) (hM1 : ∀ w, ‖iteratedFDeriv ℝ 1 Θ w‖ ≤ M1)
    (hK : ∀ w, ‖iteratedFDeriv ℝ 2 Θ w‖ ≤ K) :
    |∫ z, Θ z ∂γ₂ - ∫ z, Θ z ∂γ₁| ≤ K * δ / 2 := by
  have hs₁ := gaussian_sqnorm_integrable h₁
  have hs₂ := gaussian_sqnorm_integrable h₂
  obtain ⟨L, hLΔ, hδ0, hLn⟩ := HRS.MC.Q714.GT.gt_delta_clm hs₁ hs₂ Δ hΔ δ hδ
  have hL : ∀ M : B [×2]→L[ℝ] ℝ, L M = ∫ z, M ![z, z] ∂γ₂ - ∫ z, M ![z, z] ∂γ₁ :=
    fun M => by rw [hLΔ, hΔ]
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  set μ := γ₁.prod γ₂ with hμ
  set f : ℝ → ℝ := fun θ => ∫ q, Θ (HRS.MC.Q714.GT.gtPt θ q) ∂μ with hf
  have hI := fun θ => HRS.MC.Q714.GT.gt_interp h₁ h₂ L hL hLn hΘ hM0 hM1 hK θ
  obtain ⟨e1, e2⟩ := HRS.MC.Q714.GT.gt_endpoints (γ₁ := γ₁) (γ₂ := γ₂) hΘ.continuous hM0
  have hπ : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have key := HRS.MC.Q714.GT.gt_cmp_abs (f := f)
    (f' := fun θ => Real.sin θ * Real.cos θ * ∫ q, L (iteratedFDeriv ℝ 2 Θ (HRS.MC.Q714.GT.gtPt θ q)) ∂μ)
    (g := fun θ => (δ * K / 2) * Real.sin θ ^ 2)
    (g' := fun θ => 2 * (δ * K / 2) * Real.sin θ * Real.cos θ) (fun θ => (hI θ).1)
    (fun θ => HRS.MC.Q714.GT.gt_hasDerivAt_sin_sq _ θ) hπ (fun θ hθ => by
      have hsc := HRS.MC.Q714.GT.gt_sin_cos_nonneg hθ.1 hθ.2
      rw [abs_mul, abs_of_nonneg hsc]
      calc Real.sin θ * Real.cos θ * |∫ q, L (iteratedFDeriv ℝ 2 Θ (HRS.MC.Q714.GT.gtPt θ q)) ∂μ|
          ≤ Real.sin θ * Real.cos θ * (δ * K) := mul_le_mul_of_nonneg_left (hI θ).2 hsc
        _ = _ := by ring)
  simp only [Real.sin_pi_div_two, Real.sin_zero] at key
  have hf0 : f 0 = ∫ z, Θ z ∂γ₁ := e1
  have hfπ : f (Real.pi / 2) = ∫ z, Θ z ∂γ₂ := e2
  rw [← hfπ, ← hf0]
  refine key.trans (le_of_eq ?_)
  ring

/-- Random-variable form: `G₁, G₂` a.e. measurable with centred Gaussian laws. -/
theorem p1_first_rv {Ω₁ : Type} [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (G₁ : Ω₁ → B) {Ω₂ : Type} [MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (G₂ : Ω₂ → B) (hG₁m : AEMeasurable G₁ P₁) (hG₂m : AEMeasurable G₂ P₂)
    (hG₁ : IsCenteredGaussian (law P₁ G₁)) (hG₂ : IsCenteredGaussian (law P₂ G₂))
    (Δ : (B [×2]→L[ℝ] ℝ) → ℝ)
    (hΔ : ∀ M : B [×2]→L[ℝ] ℝ,
      Δ M = ∫ ω, M ![G₂ ω, G₂ ω] ∂P₂ - ∫ ω, M ![G₁ ω, G₁ ω] ∂P₁)
    (δ : ℝ) (hδ : ∀ M : B [×2]→L[ℝ] ℝ, ‖M‖ ≤ 1 → |Δ M| ≤ δ)
    {Θ : B → ℝ} (hΘ : ContDiff ℝ 2 Θ) {M0 M1 K : ℝ}
    (hM0 : ∀ w, |Θ w| ≤ M0) (hM1 : ∀ w, ‖iteratedFDeriv ℝ 1 Θ w‖ ≤ M1)
    (hK : ∀ w, ‖iteratedFDeriv ℝ 2 Θ w‖ ≤ K) :
    |∫ ω, Θ (G₂ ω) ∂P₂ - ∫ ω, Θ (G₁ ω) ∂P₁| ≤ K * δ / 2 := by
  have hmeasM : ∀ M : B [×2]→L[ℝ] ℝ, Continuous fun z : B => M ![z, z] := fun M =>
    M.cont.comp (continuous_pi fun i => by fin_cases i <;> exact continuous_id)
  haveI : IsProbabilityMeasure (law P₁ G₁) := (Measure.isProbabilityMeasure_map_iff hG₁m).2 inferInstance
  haveI : IsProbabilityMeasure (law P₂ G₂) := (Measure.isProbabilityMeasure_map_iff hG₂m).2 inferInstance
  have hΔ' : ∀ M : B [×2]→L[ℝ] ℝ,
      Δ M = ∫ z, M ![z, z] ∂(P₂.map G₂) - ∫ z, M ![z, z] ∂(P₁.map G₁) := by
    intro M
    rw [hΔ, integral_map hG₂m (hmeasM M).aestronglyMeasurable,
      integral_map hG₁m (hmeasM M).aestronglyMeasurable]
  have hcore := p1_first_core hG₁ hG₂ Δ hΔ' δ hδ hΘ hM0 hM1 hK
  rw [integral_map hG₂m hΘ.continuous.aestronglyMeasurable,
    integral_map hG₁m hΘ.continuous.aestronglyMeasurable] at *
  exact hcore

end HRS.MC.E214P

end
