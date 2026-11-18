import HRS.Uniform.Q54Aux23

/-!
# Q54, part 24: Lemma 3.27 `evolution_estimates` (relocated proof)

`HRS.Uniform.evolution_estimates` (in `HRS/Uniform/Evolution.lean`) cannot import this development (`Q54Aux1` imports `Evolution`), so
the proof is stated here as `evolution_estimates_proof` with the verbatim statement, and tied to the frozen statement by `example`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q54

open HRS HRS.Uniform

variable {d : ℕ}

theorem evolution_estimates_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (r : ℝ) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ (β : ℝ) (hβ : 0 < β) (V ρ₀ : Torus d → ℝ),
      PDE.FiniteRegHyp d s β β K V ρ₀ → ∀ ρc : ℝ → PDE.Coeff d,
      PDE.IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc →
      ∃ Cr cr : ℝ, 0 < Cr ∧ 0 < cr ∧
        ∃ Vev : ℝ → ℝ → NegSobolev d r →L[ℝ] NegSobolev d r,
          IsDualEvolution (PDE.mfData d s hs0 hsd V β hβ) (PDE.mfPath ρc) r Vev ∧
          (∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T) ∧
          (∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Cr * Real.exp (-cr * (t - u))) ∧
          ∀ T : ℝ, 0 < T → ∃ CrT : ℝ, 0 ≤ CrT ∧
            ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
              (ℱ : Filtration ℝ mΩ) (a : ℝ), 0 ≤ a →
              ∀ (M : ℝ → Ω → NegSobolev d r) (Sg : ℝ → Ω → (NegSobolev d r →L[ℝ] NegSobolev d r →L[ℝ] ℝ)),
                IsHilbertMartingaleWithCovariation P ℱ (a + T) M Sg →
                ∃ Z : ℝ → Ω → NegSobolev d r,
                  (∀ t ∈ Set.Icc a (a + T),
                    IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d r)) M a t (Z t)) ∧
                  (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc a (a + T))) ∧
                  ∫⁻ ω, (⨆ t ∈ Set.Icc a (a + T), ‖Z t ω‖ₑ) ^ 2 ∂P ≤
                    ENNReal.ofReal CrT *
                      ∫⁻ ω, (∫⁻ u in Set.Icc a (a + T), ENNReal.ofReal (traceNormForm (Sg u ω))) ∂P :=
  evolution_estimates_of_input hd s hs0 hsd r (exists_levelInput hd s hs0 hsd r)

example := (@evolution_estimates_proof : type_of% @HRS.Uniform.evolution_estimates)

end HRS.Uniform.Q54
