import HRS.MC.Q714GTMain

/-!
# Packet GT (row 7.14), the law-level theorem `gt_core`

Two-sided Gaussian Taylor bounds for laws `γ₁, γ₂` of centred Gaussians, from the interpolation
`θ ↦ ∫ Φ(cos θ x + sin θ y) d(γ₁ ⊗ γ₂)` (`gt_hasDerivAt`), applied to `Φ` and to `Ψ = Δ ∘ D²Φ`.
-/

open MeasureTheory ProbabilityTheory
open HRS

noncomputable section

namespace HRS.MC.Q714.GT

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]

lemma gt_L_D2 {γ₁ γ₂ : Measure B} (L : (B [×2]→L[ℝ] ℝ) →L[ℝ] ℝ)
    (hL : ∀ M : B [×2]→L[ℝ] ℝ, L M = ∫ z, M ![z, z] ∂γ₂ - ∫ z, M ![z, z] ∂γ₁)
    (Θ : B → ℝ) (u : B) :
    L (iteratedFDeriv ℝ 2 Θ u) = gtQ γ₂ Θ u - gtQ γ₁ Θ u := by
  rw [hL]
  simp [iteratedFDeriv_two_apply, gtQ]

/-- First-order interpolation derivative with `Δ` in place of the explicit second moments. -/
lemma gt_interp {γ₁ γ₂ : Measure B} [IsProbabilityMeasure γ₁] [IsProbabilityMeasure γ₂]
    (h₁ : IsCenteredGaussian γ₁) (h₂ : IsCenteredGaussian γ₂)
    (L : (B [×2]→L[ℝ] ℝ) →L[ℝ] ℝ)
    (hL : ∀ M : B [×2]→L[ℝ] ℝ, L M = ∫ z, M ![z, z] ∂γ₂ - ∫ z, M ![z, z] ∂γ₁)
    {δ : ℝ} (hLn : ‖L‖ ≤ δ) {Θ : B → ℝ} (hΘ : ContDiff ℝ 2 Θ) {M0 M1 K : ℝ}
    (hM0 : ∀ w, |Θ w| ≤ M0) (hM1 : ∀ w, ‖iteratedFDeriv ℝ 1 Θ w‖ ≤ M1)
    (hK : ∀ w, ‖iteratedFDeriv ℝ 2 Θ w‖ ≤ K) (θ : ℝ) :
    HasDerivAt (fun θ => ∫ q, Θ (gtPt θ q) ∂(γ₁.prod γ₂))
      (Real.sin θ * Real.cos θ * ∫ q, L (iteratedFDeriv ℝ 2 Θ (gtPt θ q)) ∂(γ₁.prod γ₂)) θ ∧
    |∫ q, L (iteratedFDeriv ℝ 2 Θ (gtPt θ q)) ∂(γ₁.prod γ₂)| ≤ δ * K := by
  have hd := gt_hasDerivAt h₁ h₂ hΘ hM0 (M1 := M1) (M2 := K)
    (fun w => by rw [← norm_iteratedFDeriv_one]; exact hM1 w)
    (fun w => by rw [gt_norm_D2]; exact hK w) θ
  have heq : ∀ q : B × B, L (iteratedFDeriv ℝ 2 Θ (gtPt θ q)) =
      gtQ γ₂ Θ (gtPt θ q) - gtQ γ₁ Θ (gtPt θ q) := fun q => gt_L_D2 L hL Θ _
  simp_rw [heq]
  refine ⟨hd, ?_⟩
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hδ0 : 0 ≤ δ := (norm_nonneg L).trans hLn
  have := norm_integral_le_of_norm_le_const (μ := γ₁.prod γ₂)
    (f := fun q : B × B => gtQ γ₂ Θ (gtPt θ q) - gtQ γ₁ Θ (gtPt θ q)) (C := δ * K)
    (Filter.Eventually.of_forall fun q => by
      rw [← heq q, Real.norm_eq_abs]
      calc |L (iteratedFDeriv ℝ 2 Θ (gtPt θ q))|
          ≤ ‖L‖ * ‖iteratedFDeriv ℝ 2 Θ (gtPt θ q)‖ := L.le_opNorm _
        _ ≤ δ * K := mul_le_mul hLn (hK _) (norm_nonneg _) hδ0)
  simpa using this

/-- Values of the interpolation at the endpoints. -/
lemma gt_endpoints {γ₁ γ₂ : Measure B} [IsProbabilityMeasure γ₁] [IsProbabilityMeasure γ₂]
    {Θ : B → ℝ} (hΘ : Continuous Θ) {M : ℝ} (hM : ∀ w, |Θ w| ≤ M) :
    ∫ q, Θ (gtPt 0 q) ∂(γ₁.prod γ₂) = ∫ z, Θ z ∂γ₁ ∧
    ∫ q, Θ (gtPt (Real.pi / 2) q) ∂(γ₁.prod γ₂) = ∫ z, Θ z ∂γ₂ := by
  have hb : ∀ q : B × B, ‖Θ q.1‖ ≤ M := fun q => by rw [Real.norm_eq_abs]; exact hM _
  have hb' : ∀ q : B × B, ‖Θ q.2‖ ≤ M := fun q => by rw [Real.norm_eq_abs]; exact hM _
  have i1 : Integrable (fun q : B × B => Θ q.1) (γ₁.prod γ₂) :=
    Integrable.of_bound (C := M) (hΘ.comp continuous_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall hb)
  have i2 : Integrable (fun q : B × B => Θ q.2) (γ₁.prod γ₂) :=
    Integrable.of_bound (C := M) (hΘ.comp continuous_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall hb')
  constructor
  · simp only [gtPt_zero]
    rw [integral_prod _ i1]
    simp
  · simp only [gtPt_pi_div_two]
    rw [integral_prod _ i2]
    simp

end HRS.MC.Q714.GT

end
