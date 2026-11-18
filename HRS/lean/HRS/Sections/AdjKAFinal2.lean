import HRS.Sections.AdjKAAux16

/-!
# ADJKA: relocated proof of the `AdjKSpec` packet BCONV (`adjk_conv_kolmogorov`)

It lives apart from `AdjKAFinal.lean` because the helper chain of BCONV imports the proofs of A2 and B1 from there.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjk_conv_kolmogorov_proof (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    (j : ℕ) (hj : (d : ℝ) + 2 ≤ j) (m : ℝ) (hjm : (j : ℝ) + 2 ≤ m) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ mΩ) (μ : ℝ → Ω → Measure (Torus d)) (_ : ∀ r ω, IsProbabilityMeasure (μ r ω))
      (M : ℝ → Ω → NegSobolev d m),
      IsHilbertMartingaleWithCovariation P ℱ T M (fun r ω => covForm m β⁻¹ (μ r ω)) →
      ∀ Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m,
        IsDualEvolution htr.dyn ρ m Vev → (∀ T' : ℝ, 0 ≤ T' → IsPlainEvolution Vev T') →
        ∀ Z : ℝ → Ω → NegSobolev d m,
          (∀ t ∈ Set.Icc (0 : ℝ) T,
            IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) M 0 t (Z t)) →
          (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T)) → (∀ t, Measurable (Z t)) →
          ∫⁻ ω, ⨆ t ∈ ratIcc 0 T, adjkEnergy (j : ℝ) m (Z t ω) ∂P ≤ ENNReal.ofReal C ∧
          ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
            ∫⁻ ω, ‖Z t ω - Z s ω‖ₑ ^ (4 : ℝ) ∂P ≤ ENNReal.ofReal (C * |t - s| ^ 2) :=
  adjka_bconv hd htr j hj m hjm T hT

example := (@adjk_conv_kolmogorov_proof : type_of% @HRS.AdjK.adjk_conv_kolmogorov)

end HRS.AdjK
