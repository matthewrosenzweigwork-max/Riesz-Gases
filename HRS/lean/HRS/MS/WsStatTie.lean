import HRS.MS.WsStatAux11

/-!
# S21: S2.1 (i) `whole_space_stationary`: the conditional reduction (tie, partial)

The frozen statement `HRS.Whole.whole_space_stationary` (`HRS/Whole/Headline.lean`) is
`exists C0 C, (completion clause) /\ forall rho_beta N, GibbsInvariant -> realizations -> (a.e. measurability, smooth bound, W_1 bound)`.

* `S21Main d s a beta T C0 C` is the second conjunct with the constants `C0`, `C` fixed (the particle/path estimates).
* `whole_space_stationary_of_main`: if for every `d, s, a, beta, T` there is a threshold `C0thr` such that for every
  `C0 >= C0thr` some `C` gives `S21Main d s a beta T C0 C`, then the frozen statement holds.  The completion clause is
  proved here (`s21_clause1_stationary`, packet A: for all `C0 >=` its threshold, `oN` monotone in `C0`), so the single
  open item of S2.1 (i) is `S21Main` (packets F-K of `WsStatAux1.lean`).

Nothing here changes a frozen statement.  The hypothesis of `whole_space_stationary_of_main` is the `S21Main` form (a clean `Prop`),
not `type_of% @whole_space_stationary`, so the reduction is not circular.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole

variable {d : ℕ}

/-- The path estimates of S2.1 (i) for fixed constants `C0`, `C`. -/
def S21Main (d : ℕ) (s a β T C₀ C : ℝ) : Prop :=
  ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ N : ℕ, 2 ≤ N →
    GibbsInvariant d s a β N →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
      IsVectorBrownian P W → IndepFun X₀ (fun ζ t => W t ζ) P →
      law P X₀ = canonicalGibbs (rieszKernel d s) (confinement a) N β →
      IsWholeStrongSolution P (quadraticGradientDyn d s a β) T X₀ W X →
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (Z : ℝ → Ω' → OscDual d (wholeSpaceIndex d)),
      IsLinearGaussianEvolutionW P' ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
        (wholeSpaceIndex d) β⁻¹ T
        (susceptibilityCov (rieszKernel d s) (withDensityReal ρβ) β) Z →
      AEMeasurable (zetaPathW (wholeSpaceIndex d) T 0 P X) P ∧
      AEMeasurable (processWindow (wholeSpaceIndex d) T 0 Z) P' ∧
      smoothDist 2 (law P (zetaPathW (wholeSpaceIndex d) T 0 P X))
          (law P' (processWindow (wholeSpaceIndex d) T 0 Z)) ≤
        C * (Real.sqrt (deltaN d s N) + localizationRate d s C₀ N) ∧
      wassersteinE 1 (law P (zetaPathW (wholeSpaceIndex d) T 0 P X))
          (law P' (processWindow (wholeSpaceIndex d) T 0 Z)) ≤
        ENNReal.ofReal (C * (deltaN d s N ^ ((3 : ℝ) / 20) +
          Real.sqrt (localizationRate d s C₀ N)))

theorem whole_space_stationary_of_main
    (hmain : ∀ (d : ℕ), 2 ≤ d → ∀ (s : ℝ), 0 ≤ s → s < d → ∀ (a β : ℝ), 0 < a → 0 < β → ∀ T : ℝ, 0 < T →
      ∃ C₀thr : ℝ, ∀ C₀ : ℝ, C₀thr ≤ C₀ → ∃ C : ℝ, S21Main d s a β T C₀ C) :
    HRS.Whole.WholeSpaceStationaryStatement := by
  intro d hd s hs0 hsd a β ha hβ T hT
  obtain ⟨thr, h⟩ := hmain d hd s hs0 hsd a β ha hβ T hT
  obtain ⟨C₀min, -, hcl⟩ := HRS.MS.S21.s21_clause1_stationary hd hs0 hsd ha hβ
  obtain ⟨C, hC⟩ := h (max thr C₀min) (le_max_left _ _)
  exact ⟨max thr C₀min, C, hcl (max thr C₀min) (le_max_right _ _), hC⟩

end HRS.Whole
