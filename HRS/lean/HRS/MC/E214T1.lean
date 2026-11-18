import HRS.MC.E214P5
import HRS.MC.E214P3
import HRS.MC.Q714GTFinal
import HRS.MC.Q714AsmBase

/-!
# E214T1: the Hessian step of the two-parameter expansion

For two a.e. measurable centred Gaussian random elements `G₂ = Z^{a+·}` (on `P₂`) and `G₁ = Z_{β,T}` (on `P₁`) of a
separable Banach space, and `Φ` in the `C_b^5` unit ball,
`|E Φ(G₂) - E Φ(G₁) - ½ E_{ω₁} Δ(D²Φ(G₁ ω₁))| ≤ covDist² / 8`,
where `Δ M = E M(G₂,G₂) - E M(G₁,G₁)` is the nested integral occurring in `two_parameter_expansion`.
This instantiates `gaussian_taylor_proof` with `C₂ = C₄ = 1` and `δ = covDist` (`p3_abs_le_covDist`).
-/

open MeasureTheory ProbabilityTheory
open HRS

noncomputable section

namespace HRS.MC.E214T

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]

theorem t1_hessian {Ω₁ : Type} [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (G₁ : Ω₁ → B) {Ω₂ : Type} [MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (G₂ : Ω₂ → B) (hG₁m : AEMeasurable G₁ P₁) (hG₂m : AEMeasurable G₂ P₂)
    (hG₁ : IsCenteredGaussian (law P₁ G₁)) (hG₂ : IsCenteredGaussian (law P₂ G₂))
    {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B 5) :
    |∫ ω, Φ (G₂ ω) ∂P₂ - ∫ ω, Φ (G₁ ω) ∂P₁ -
        (1 / 2) * ∫ ω₁, (∫ ω, (iteratedFDeriv ℝ 2 Φ (G₁ ω₁)) ![G₂ ω, G₂ ω] ∂P₂ -
          ∫ ω₂, (iteratedFDeriv ℝ 2 Φ (G₁ ω₁)) ![G₁ ω₂, G₁ ω₂] ∂P₁) ∂P₁| ≤
      HRS.Main.covDist P₂ P₁ G₂ G₁ ^ 2 / 8 := by
  have i₁ := HRS.MC.E214P.p3_sqnorm_integrable hG₁m hG₁
  have i₂ := HRS.MC.E214P.p3_sqnorm_integrable hG₂m hG₂
  have hgt := HRS.MC.Q714.GT.gaussian_taylor_proof P₁ G₁ P₂ G₂ hG₁m hG₂m hG₁ hG₂
    (fun M => ∫ ω, M ![G₂ ω, G₂ ω] ∂P₂ - ∫ ω, M ![G₁ ω, G₁ ω] ∂P₁) (fun M => rfl)
    (HRS.Main.covDist P₂ P₁ G₂ G₁)
    (fun M hM => HRS.MC.E214P.p3_abs_le_covDist P₂ P₁ G₂ G₁ i₂ i₁ M hM)
    Φ (HRS.MC.Q714.Asm.asm_memCb4 hΦ) 1 1 (HRS.MC.Q714.Asm.asm_norm2 hΦ)
    (HRS.MC.Q714.Asm.asm_norm4 hΦ)
  simpa using hgt.2

end HRS.MC.E214T

end
