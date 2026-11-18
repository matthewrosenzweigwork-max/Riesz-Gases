import HRS.MC.E214P1
import HRS.Main.HeadlineEdgeworth

/-!
# E214P3 (L3): `|E M(Z₁,Z₁) - E M(Z₂,Z₂)| ≤ covDist` and the Gaussian comparison in terms of `covDist`

`covDist` is a real `iSup`: for a family that is not bounded above it is the junk value `0`.  Here the family is bounded
by `E‖Z₁‖² + E‖Z₂‖²` as soon as both squared norms are integrable (`p3_bddAbove`), so `le_ciSup` is legitimate.
-/

open MeasureTheory ProbabilityTheory
open HRS

noncomputable section

namespace HRS.MC.E214P

section CovDist

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] {Ω₁ Ω₂ : Type*}
  [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

theorem p3_quad_le (M : B [×2]→L[ℝ] ℝ) (hM : ‖M‖ ≤ 1) (z : B) : ‖M ![z, z]‖ ≤ ‖z‖ ^ 2 := by
  have := M.le_opNorm ![z, z]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
  calc ‖M ![z, z]‖ ≤ ‖M‖ * (‖z‖ * ‖z‖) := this
    _ ≤ 1 * (‖z‖ * ‖z‖) := mul_le_mul_of_nonneg_right hM (mul_self_nonneg _)
    _ = ‖z‖ ^ 2 := by ring

theorem p3_abs_integral_le (P : Measure Ω₁) (Z : Ω₁ → B) (hZ : Integrable (fun ω => ‖Z ω‖ ^ 2) P)
    (M : B [×2]→L[ℝ] ℝ) (hM : ‖M‖ ≤ 1) :
    |∫ ω, M ![Z ω, Z ω] ∂P| ≤ ∫ ω, ‖Z ω‖ ^ 2 ∂P := by
  have := norm_integral_le_of_norm_le (μ := P) (f := fun ω => M ![Z ω, Z ω]) hZ
    (Filter.Eventually.of_forall fun ω => p3_quad_le M hM (Z ω))
  simpa [Real.norm_eq_abs] using this

theorem p3_bddAbove (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) (Z₁ : Ω₁ → B) (Z₂ : Ω₂ → B)
    (h₁ : Integrable (fun ω => ‖Z₁ ω‖ ^ 2) P₁) (h₂ : Integrable (fun ω => ‖Z₂ ω‖ ^ 2) P₂) :
    BddAbove (Set.range fun M : {M : B [×2]→L[ℝ] ℝ // ‖M‖ ≤ 1} =>
      |∫ ω, M.1 ![Z₁ ω, Z₁ ω] ∂P₁ - ∫ ω, M.1 ![Z₂ ω, Z₂ ω] ∂P₂|) := by
  refine ⟨∫ ω, ‖Z₁ ω‖ ^ 2 ∂P₁ + ∫ ω, ‖Z₂ ω‖ ^ 2 ∂P₂, ?_⟩
  rintro _ ⟨M, rfl⟩
  have e1 := p3_abs_integral_le P₁ Z₁ h₁ M.1 M.2
  have e2 := p3_abs_integral_le P₂ Z₂ h₂ M.1 M.2
  exact (abs_sub _ _).trans (add_le_add e1 e2)

/-- **L3.**  Every unit bilinear form is dominated by `covDist` (needs the two second moments finite). -/
theorem p3_abs_le_covDist (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) (Z₁ : Ω₁ → B) (Z₂ : Ω₂ → B)
    (h₁ : Integrable (fun ω => ‖Z₁ ω‖ ^ 2) P₁) (h₂ : Integrable (fun ω => ‖Z₂ ω‖ ^ 2) P₂)
    (M : B [×2]→L[ℝ] ℝ) (hM : ‖M‖ ≤ 1) :
    |∫ ω, M ![Z₁ ω, Z₁ ω] ∂P₁ - ∫ ω, M ![Z₂ ω, Z₂ ω] ∂P₂| ≤
      HRS.Main.covDist P₁ P₂ Z₁ Z₂ :=
  le_ciSup (f := fun M : {M : B [×2]→L[ℝ] ℝ // ‖M‖ ≤ 1} =>
      |∫ ω, M.1 ![Z₁ ω, Z₁ ω] ∂P₁ - ∫ ω, M.1 ![Z₂ ω, Z₂ ω] ∂P₂|)
    (p3_bddAbove P₁ P₂ Z₁ Z₂ h₁ h₂) ⟨M, hM⟩

theorem p3_covDist_nonneg (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) (Z₁ : Ω₁ → B) (Z₂ : Ω₂ → B) :
    0 ≤ HRS.Main.covDist P₁ P₂ Z₁ Z₂ :=
  Real.iSup_nonneg fun _ => abs_nonneg _

end CovDist

section Compare

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]

/-- A random element with centred Gaussian law has an integrable squared norm. -/
theorem p3_sqnorm_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → B} (hGm : AEMeasurable G P) (hG : IsCenteredGaussian (law P G)) :
    Integrable (fun ω => ‖G ω‖ ^ 2) P := by
  have h := gaussian_sqnorm_integrable hG
  haveI : IsProbabilityMeasure (law P G) := (Measure.isProbabilityMeasure_map_iff hGm).2 inferInstance
  exact (integrable_map_measure (by fun_prop : AEStronglyMeasurable (fun y : B => ‖y‖ ^ 2) (P.map G)) hGm).1 h

/-- **L1 + L3.**  First-order Gaussian comparison of two centred Gaussian random elements, with the error
measured by `covDist` (which is the genuine supremum here, not the junk value). -/
theorem p3_compare {Ω₁ : Type} [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (G₁ : Ω₁ → B) {Ω₂ : Type} [MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (G₂ : Ω₂ → B) (hG₁m : AEMeasurable G₁ P₁) (hG₂m : AEMeasurable G₂ P₂)
    (hG₁ : IsCenteredGaussian (law P₁ G₁)) (hG₂ : IsCenteredGaussian (law P₂ G₂))
    {Θ : B → ℝ} (hΘ : ContDiff ℝ 2 Θ) {M0 M1 K : ℝ}
    (hM0 : ∀ w, |Θ w| ≤ M0) (hM1 : ∀ w, ‖iteratedFDeriv ℝ 1 Θ w‖ ≤ M1)
    (hK : ∀ w, ‖iteratedFDeriv ℝ 2 Θ w‖ ≤ K) :
    |∫ ω, Θ (G₂ ω) ∂P₂ - ∫ ω, Θ (G₁ ω) ∂P₁| ≤ K * HRS.Main.covDist P₂ P₁ G₂ G₁ / 2 := by
  have i₁ := p3_sqnorm_integrable hG₁m hG₁
  have i₂ := p3_sqnorm_integrable hG₂m hG₂
  exact p1_first_rv P₁ G₁ P₂ G₂ hG₁m hG₂m hG₁ hG₂
    (fun M => ∫ ω, M ![G₂ ω, G₂ ω] ∂P₂ - ∫ ω, M ![G₁ ω, G₁ ω] ∂P₁) (fun M => rfl)
    (HRS.Main.covDist P₂ P₁ G₂ G₁) (fun M hM => p3_abs_le_covDist P₂ P₁ G₂ G₁ i₂ i₁ M hM)
    hΘ hM0 hM1 hK

end Compare

end HRS.MC.E214P

end
