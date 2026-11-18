import HRS.Uniform.Q48eAux1
import HRS.Uniform.Evolution

/-!
# Q54, part 1: the maximal-estimate half of Lemma 3.27 from quasi-contractivity (assembly)

`LevelInput` is the analytic content of Lemma 3.27 at a single real level `r` for the solution `ρc` of Proposition 5.1:
a dual evolution `Vev` on `E_r` which is a plain strongly continuous evolution, is quasi-contractive in the `E_r` norm
(`‖Vev t u‖ ≤ e^{c (t-u)}`, `u ≤ t`) and has exponential decay `‖Vev t u‖ ≤ C_r e^{-c_r (t-u)}`.

`evolution_estimates_of_input` is `HRS.Uniform.evolution_estimates` with the single analytic input `LevelInput`
(for all `K ≥ K₀` and all admissible data); all the stochastic analysis (window maximal estimate, existence of a
continuous version of the convolution) is discharged from `winmax_of_quasi` (Q48e, Kotelenez).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q54

open HRS HRS.Uniform

variable {d : ℕ}

/-- The analytic input of Lemma 3.27 at level `r`. -/
def LevelInput (d : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (β : ℝ) (hβ : 0 < β)
    (ρc : ℝ → PDE.Coeff d) (r : ℝ) : Prop :=
  ∃ Vev : ℝ → ℝ → NegSobolev d r →L[ℝ] NegSobolev d r,
    IsDualEvolution (PDE.mfData d s hs0 hsd V β hβ) (PDE.mfPath ρc) r Vev ∧
    (∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T) ∧
    (∃ c : ℝ, ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Real.exp (c * (t - u))) ∧
    ∃ Cr cr : ℝ, 0 < Cr ∧ 0 < cr ∧ ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Cr * Real.exp (-cr * (t - u))

/-- `HRS.Uniform.evolution_estimates` from the analytic input `LevelInput`. -/
theorem evolution_estimates_of_input (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (r : ℝ)
    (hin : ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ (β : ℝ) (hβ : 0 < β) (V ρ₀ : Torus d → ℝ),
      PDE.FiniteRegHyp d s β β K V ρ₀ → ∀ ρc : ℝ → PDE.Coeff d,
      PDE.IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc → LevelInput d s hs0 hsd V β hβ ρc r) :
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
                      ∫⁻ ω, (∫⁻ u in Set.Icc a (a + T), ENNReal.ofReal (traceNormForm (Sg u ω))) ∂P := by
  obtain ⟨K₀, hK₀⟩ := hin
  refine ⟨K₀, fun K hK β hβ V ρ₀ hH ρc hρc => ?_⟩
  obtain ⟨Vev, hdual, hplain, ⟨c, hc⟩, Cr, cr, hCr, hcr, hdec⟩ := hK₀ K hK β hβ V ρ₀ hH ρc hρc
  refine ⟨Cr, cr, hCr, hcr, Vev, hdual, hplain, hdec, fun T hT => ?_⟩
  have hq : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Real.exp ((2 * c) * (t - u) / 2) := by
    intro u t hu hut
    have := hc u t hu hut
    rwa [show (2 * c) * (t - u) / 2 = c * (t - u) by ring]
  have hW := Q48e.winmax_of_quasi.{0} hplain (K := 2 * c) hq hT.le
  refine ⟨Kot.CD 2 (2 * c) T, Kot.CD_nonneg _ _ _, ?_⟩
  intro Ω mΩ P _ ℱ a ha M Sg hM
  obtain ⟨Z, h1, -, h3, h4⟩ := hW Ω P ℱ a ha M Sg hM
  exact ⟨Z, h1, h3, h4⟩

end HRS.Uniform.Q54
