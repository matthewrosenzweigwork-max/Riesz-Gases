import HRS.MC.E214P4

/-!
# E214P5 (L5): integrability and comparison bookkeeping for `∫ L(D³Φ(G))`

For an a.e. measurable `G` the integrand `ω ↦ L (D³Φ (G ω))` is bounded by `‖L‖` and a.e. strongly measurable, hence
integrable (the Bochner integral is genuine, not the junk value `0`); the difference of two such integrals with
tensors `L, L'` is bounded by `‖L - L'‖`.
-/

open MeasureTheory ProbabilityTheory
open HRS

noncomputable section

namespace HRS.MC.E214P

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]

theorem p5_pointwise {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B 5) (L : (B [×3]→L[ℝ] ℝ) →L[ℝ] ℝ) (z : B) :
    |L (iteratedFDeriv ℝ 3 Φ z)| ≤ ‖L‖ := (p4_bound hΦ L).1 z

theorem p5_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {G : Ω → B} (hG : AEMeasurable G P) {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B 5)
    (L : (B [×3]→L[ℝ] ℝ) →L[ℝ] ℝ) :
    Integrable (fun ω => L (iteratedFDeriv ℝ 3 Φ (G ω))) P :=
  Integrable.of_bound (((L.continuous.comp (p4_cont hΦ)).comp_aestronglyMeasurable hG.aestronglyMeasurable))
    ‖L‖ (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact p5_pointwise hΦ L _)

theorem p5_abs_integral_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → B} {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B 5) (L : (B [×3]→L[ℝ] ℝ) →L[ℝ] ℝ) :
    |∫ ω, L (iteratedFDeriv ℝ 3 Φ (G ω)) ∂P| ≤ ‖L‖ := by
  have := norm_integral_le_of_norm_le_const (μ := P)
    (f := fun ω => L (iteratedFDeriv ℝ 3 Φ (G ω))) (C := ‖L‖)
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact p5_pointwise hΦ L _)
  simpa [Real.norm_eq_abs] using this

/-- Replacing the tensor `L` by `L'` changes the cubic term by at most `‖L - L'‖`. -/
theorem p5_cubic_diff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → B} (hG : AEMeasurable G P) {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B 5)
    (L L' : (B [×3]→L[ℝ] ℝ) →L[ℝ] ℝ) :
    |∫ ω, L (iteratedFDeriv ℝ 3 Φ (G ω)) ∂P - ∫ ω, L' (iteratedFDeriv ℝ 3 Φ (G ω)) ∂P| ≤ ‖L - L'‖ := by
  rw [← integral_sub (p5_integrable hG hΦ L) (p5_integrable hG hΦ L')]
  have := p5_abs_integral_le (P := P) (G := G) hΦ (L - L')
  simpa using this

/-- `∫ Φ d(law G) = ∫ Φ(G)`. -/
theorem p5_law_integral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {G : Ω → B}
    (hG : AEMeasurable G P) {Φ : B → ℝ} (hΦ : Continuous Φ) :
    ∫ z, Φ z ∂(law P G) = ∫ ω, Φ (G ω) ∂P :=
  integral_map hG hΦ.aestronglyMeasurable

end HRS.MC.E214P

end
