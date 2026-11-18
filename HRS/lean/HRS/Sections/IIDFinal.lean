import HRS.Sections.Sec5
import HRS.Sections.IIDAux18

/-!
# Relocated proofs of Proposition 5.9 (`iid_field_comparison`, `iid_field_mixture`)

Statements are copied verbatim from `HRS/Sections/Sec5.lean`; `Sec5.lean` is not edited.  Each
`_proof` is tied to its statement by an `example` (`type_of%`).  Helpers: `HRS/Sections/IIDAux1..`
(namespace `HRS.IID`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {d : ℕ}

theorem iid_field_comparison_proof (hd : 2 ≤ d) (m : ℝ) (hm : (d : ℝ) / 2 < m) (c Cbar : ℝ)
    (hc : 0 < c) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, c ≤ ρ x) →
      (∀ x, ρ x ≤ Cbar) → ∀ γ : Measure (NegSobolev d m),
      IsCenteredGaussianWithCov m γ (iidCov (withDensityReal ρ)) →
      ∀ N : ℕ, 1 ≤ N →
        smoothDist 2 (law (Measure.pi fun _ : Fin N => withDensityReal ρ)
            (fun X : Config d N => etaE m X (withDensityReal ρ))) γ ≤ Cm * iidRateSmooth d m N ∧
        wassersteinE 1 (law (Measure.pi fun _ : Fin N => withDensityReal ρ)
            (fun X : Config d N => etaE m X (withDensityReal ρ))) γ ≤
          ENNReal.ofReal (Cm * iidRateW d m N) ∧
        wassersteinE 2 (law (Measure.pi fun _ : Fin N => withDensityReal ρ)
            (fun X : Config d N => etaE m X (withDensityReal ρ))) γ ≤
          ENNReal.ofReal (Cm * iidRateW d m N ^ ((1 : ℝ) / 3)) := by
  obtain ⟨Cm, hCm, h⟩ := HRS.IID.iid_comparison_aux hd m hm c hc
  exact ⟨Cm, hCm, fun ρ hρ hρc _ γ hγ N hN => h ρ hρ hρc γ hγ N hN⟩

example := (@iid_field_comparison_proof : type_of% @HRS.iid_field_comparison)

theorem iid_field_mixture_proof (hd : 2 ≤ d) (m : ℝ) (hm : (d : ℝ) / 2 < m) (c Cbar : ℝ) (hc : 0 < c)
    (a : ℝ) (b : Torus d → ℝ) (hbm : Measurable b) (hbL : MemLp b ⊤ volume) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, c ≤ ρ x) →
      (∀ x, ρ x ≤ Cbar) → pair (withDensityReal ρ) b = 0 →
      ∀ γ : Measure (NegSobolev d m),
      IsCenteredGaussianWithCov m γ (iidCov (withDensityReal ρ)) →
      ∀ N : ℕ, 2 ≤ N → 4 * a ^ 2 * (eLpNorm b ⊤ volume).toReal ^ 2 ≤ N →
        smoothDist 2
            (law ((2 : ℝ≥0∞)⁻¹ • Measure.pi (fun _ : Fin N =>
                  withDensityReal fun x => (1 + a * b x / Real.sqrt N) * ρ x) +
                (2 : ℝ≥0∞)⁻¹ • Measure.pi (fun _ : Fin N =>
                  withDensityReal fun x => (1 - a * b x / Real.sqrt N) * ρ x))
              (fun X : Config d N => etaE m X (withDensityReal ρ)))
            ((2 : ℝ≥0∞)⁻¹ • γ.map (fun F => F + NegSobolev.ofFun m (fun x => a * b x * ρ x)) +
              (2 : ℝ≥0∞)⁻¹ • γ.map (fun F => F - NegSobolev.ofFun m (fun x => a * b x * ρ x))) ≤
          Cm * iidRateSmooth d m N ∧
        wassersteinE 1
            (law ((2 : ℝ≥0∞)⁻¹ • Measure.pi (fun _ : Fin N =>
                  withDensityReal fun x => (1 + a * b x / Real.sqrt N) * ρ x) +
                (2 : ℝ≥0∞)⁻¹ • Measure.pi (fun _ : Fin N =>
                  withDensityReal fun x => (1 - a * b x / Real.sqrt N) * ρ x))
              (fun X : Config d N => etaE m X (withDensityReal ρ)))
            ((2 : ℝ≥0∞)⁻¹ • γ.map (fun F => F + NegSobolev.ofFun m (fun x => a * b x * ρ x)) +
              (2 : ℝ≥0∞)⁻¹ • γ.map (fun F => F - NegSobolev.ofFun m (fun x => a * b x * ρ x))) ≤
          ENNReal.ofReal (Cm * iidRateW d m N) ∧
        wassersteinE 2
            (law ((2 : ℝ≥0∞)⁻¹ • Measure.pi (fun _ : Fin N =>
                  withDensityReal fun x => (1 + a * b x / Real.sqrt N) * ρ x) +
                (2 : ℝ≥0∞)⁻¹ • Measure.pi (fun _ : Fin N =>
                  withDensityReal fun x => (1 - a * b x / Real.sqrt N) * ρ x))
              (fun X : Config d N => etaE m X (withDensityReal ρ)))
            ((2 : ℝ≥0∞)⁻¹ • γ.map (fun F => F + NegSobolev.ofFun m (fun x => a * b x * ρ x)) +
              (2 : ℝ≥0∞)⁻¹ • γ.map (fun F => F - NegSobolev.ofFun m (fun x => a * b x * ρ x))) ≤
          ENNReal.ofReal (Cm * iidRateW d m N ^ ((1 : ℝ) / 3)) := by
  obtain ⟨Cm, hCm, h⟩ := HRS.IID.mixture_aux hd m hm c hc a b hbm hbL
  exact ⟨Cm, hCm, fun ρ hρ hρc _ hpair γ hγ N hN hN4 => h ρ hρ hρc hpair γ hγ N hN hN4⟩

example := (@iid_field_mixture_proof : type_of% @HRS.iid_field_mixture)

end HRS
