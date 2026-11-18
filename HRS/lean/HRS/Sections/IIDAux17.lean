import HRS.Sections.IIDAux16

/-!
# IID helper chain, part 17: the two-component mixture (second part of Proposition 5.9).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.IID

section Mixture

open HRS.InitialDataAux

variable {d : ℕ}

lemma isProb_map' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → β} (hf : Measurable f) : IsProbabilityMeasure (μ.map f) :=
  ⟨by rw [Measure.map_apply hf MeasurableSet.univ]; simp⟩

/-- Per-sign facts: smooth distance and coupling data for the density `(1 + s b')ρ`. -/
theorem sign_facts {m : ℝ} (hm : (d : ℝ) < 2 * m) {Cs Cw Cz M c : ℝ}
    (hgen : ∀ q ρ : Torus d → ℝ, IsProbDensity q → (∀ x, c / 2 ≤ q x) → IsProbDensity ρ →
      ∀ κ : ℝ, 0 ≤ κ → (∀ x, |q x - ρ x| ≤ κ * ρ x) →
      ∀ γ : Measure (NegSobolev d m), IsCenteredGaussianWithCov m γ (iidCov (withDensityReal ρ)) →
      ∀ N : ℕ, 1 ≤ N →
        smoothDist 2 ((Measure.pi fun _ : Fin N => withDensityReal q).map
            (fld m N (withDensityReal q))) γ ≤
          Cs * (N : ℝ) ^ (-((m - (d : ℝ) / 2) / (2 * m))) + Cz * κ ∧
        CB ((Measure.pi fun _ : Fin N => withDensityReal q).map (fld m N (withDensityReal q))) γ
          (Cw * (Real.log (Real.exp 1 * N) / Real.sqrt N) ^
            ((m - (d : ℝ) / 2) / (m + (d : ℝ) / 2)) + Cz * κ) M)
    {ρ b' : Torus d → ℝ} (hρ : IsProbDensity ρ) (hρc : ∀ x, c ≤ ρ x) (hb'm : Measurable b') {B : ℝ}
    (hB : ∀ x, |b' x| ≤ B) (h0 : ∫ x, ρ x * b' x = 0) {s : ℝ} (hs : |s| * B ≤ 1 / 2)
    {γ : Measure (NegSobolev d m)} (hγ : IsCenteredGaussianWithCov m γ (iidCov (withDensityReal ρ)))
    {N : ℕ} (hN : 1 ≤ N) :
    smoothDist 2 ((Measure.pi fun _ : Fin N => withDensityReal fun x => (1 + s * b' x) * ρ x).map
        (fld m N (withDensityReal fun x => (1 + s * b' x) * ρ x))) γ ≤
      Cs * (N : ℝ) ^ (-((m - (d : ℝ) / 2) / (2 * m))) + Cz * (|s| * B) ∧
    CB ((Measure.pi fun _ : Fin N => withDensityReal fun x => (1 + s * b' x) * ρ x).map
        (fld m N (withDensityReal fun x => (1 + s * b' x) * ρ x))) γ
      (Cw * (Real.log (Real.exp 1 * N) / Real.sqrt N) ^
        ((m - (d : ℝ) / 2) / (m + (d : ℝ) / 2)) + Cz * (|s| * B)) M := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  exact hgen _ ρ (qd_prob hρ hb'm hB hs h0) (qd_ge hρ hρc hB hs) hρ (|s| * B) (by positivity)
    (qd_close hρ hB) γ hγ N hN


/-- Law of the mixture field, decomposed as a mixture of translates. -/
lemma law_mix {m : ℝ} (hm : (d : ℝ) < 2 * m) {N : ℕ} (hN : 1 ≤ N) {ρ q₁ q₂ : Torus d → ℝ}
    (hρ : IsProbDensity ρ) (hq₁ : IsProbDensity q₁) (hq₂ : IsProbDensity q₂) (s : NegSobolev d m)
    (h₁ : ∀ X, fld m N (withDensityReal ρ) X = fld m N (withDensityReal q₁) X + s)
    (h₂ : ∀ X, fld m N (withDensityReal ρ) X = fld m N (withDensityReal q₂) X + -s) :
    ((2 : ℝ≥0∞)⁻¹ • Measure.pi (fun _ : Fin N => withDensityReal q₁) +
        (2 : ℝ≥0∞)⁻¹ • Measure.pi (fun _ : Fin N => withDensityReal q₂)).map
      (fld m N (withDensityReal ρ)) =
    (2 : ℝ≥0∞)⁻¹ • (((Measure.pi fun _ : Fin N => withDensityReal q₁).map
        (fld m N (withDensityReal q₁))).map fun x => x + s) +
    (2 : ℝ≥0∞)⁻¹ • (((Measure.pi fun _ : Fin N => withDensityReal q₂).map
        (fld m N (withDensityReal q₂))).map fun x => x + -s) := by
  haveI := isProb_withDensityReal hq₁
  haveI := isProb_withDensityReal hq₂
  have hF : ∀ μ : Measure (Torus d), IsProbabilityMeasure μ → Measurable (fld m N μ) :=
    fun μ _ => (continuous_fld hm hN μ).measurable
  haveI := isProb_withDensityReal hρ
  have hFρ := hF (withDensityReal ρ) inferInstance
  rw [Measure.map_add _ _ hFρ, Measure.map_smul, Measure.map_smul,
    Measure.map_map (measurable_add_const s) (hF (withDensityReal q₁) inferInstance),
    Measure.map_map (measurable_add_const (-s)) (hF (withDensityReal q₂) inferInstance)]
  · have e1 : ((fun x => x + s) ∘ fld m N (withDensityReal q₁)) = fld m N (withDensityReal ρ) :=
      funext fun X => (h₁ X).symm
    have e2 : ((fun x => x + -s) ∘ fld m N (withDensityReal q₂)) = fld m N (withDensityReal ρ) :=
      funext fun X => (h₂ X).symm
    rw [e1, e2]
  · exact hFρ.aemeasurable
  · exact hFρ.aemeasurable

end Mixture

end HRS.IID
