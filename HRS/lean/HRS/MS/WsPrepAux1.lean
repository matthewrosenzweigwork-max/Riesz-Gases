import HRS.MS.WsStatAux2

/-!
# S21R packet 1: the interface of S2.1 (ii) `whole_space_prepared` (reduction to `S21PrepMain`)

`S21PrepMain d s a β β₀ T c₁ C₁ εstar C₀ C` is the second conjunct of the frozen statement
`HRS.Whole.whole_space_prepared` (the particle/path estimates) for fixed constants.

`whole_space_prepared_of_main`: if for every `d, s, a, β, β₀, T, c₁, C₁` there is an `εstar > 0` and a completion threshold
`C₀thr` such that for every `C₀ ≥ C₀thr` some `C` gives `S21PrepMain`, then the frozen statement holds.  The completion clause
(first conjunct of the frozen statement) is proved here from `s21_clause1_resulting` (no open row), so the only open content of
S2.1 (ii) is `S21PrepMain`.  Nothing here changes a frozen statement; the hypothesis is a clean `Prop`, not the frozen type.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole

variable {d : ℕ}

/-- The particle/path estimates of S2.1 (ii) for fixed constants (second conjunct of `whole_space_prepared`). -/
def S21PrepMain (d : ℕ) (s a β β₀ T c₁ C₁ εstar C₀ C : ℝ) : Prop :=
  ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ ε : ℝ, ∀ ψ : Euc d → ℝ,
    IsAdmissiblePerturbation ρβ εstar ε ψ → ∀ ρ : ℝ → Euc d → ℝ,
    IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ → ∀ N : ℕ, 2 ≤ N →
    GibbsEntropyContraction d s a β N →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
      (X : ℝ≥0 → Ω → EucConfig d N),
      IsVectorBrownian P W → IndepFun X₀ (fun ζ t => W t ζ) P →
      law P X₀ = modulatedGibbs (rieszKernel d s) N β₀ (withDensityReal (ρ 0)) →
      (∀ T' : ℝ, IsWholeStrongSolution P (quadraticGradientDyn d s a β) T' X₀ W X) →
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (Z : ℝ → Ω' → OscDual d (wholeSpaceIndex d)),
      (∀ T' : ℝ, IsLinearGaussianEvolutionW P' ((quadraticGradientDyn d s a β).coeff ρ)
        (wholeSpaceIndex d) β⁻¹ T'
        (susceptibilityCov (rieszKernel d s) (withDensityReal (ρ 0)) β₀) Z) →
    ∀ a₀ : ℝ, 0 ≤ a₀ →
      AEMeasurable (flucPathW (wholeSpaceIndex d) T a₀ (Real.sqrt N) X ρ) P ∧
      AEMeasurable (processWindow (wholeSpaceIndex d) T a₀ Z) P' ∧
      smoothDist 2 (law P (flucPathW (wholeSpaceIndex d) T a₀ (Real.sqrt N) X ρ))
          (law P' (processWindow (wholeSpaceIndex d) T a₀ Z)) ≤
        C * (Real.sqrt N * deltaN d s N + localizationRate d s C₀ N + iN d s β₀ N) ∧
      wassersteinE 1 (law P (flucPathW (wholeSpaceIndex d) T a₀ (Real.sqrt N) X ρ))
          (law P' (processWindow (wholeSpaceIndex d) T a₀ Z)) ≤
        ENNReal.ofReal (C * (Real.sqrt N * deltaN d s N +
          Real.sqrt (localizationRate d s C₀ N) + jN d s β₀ N))

/-- The reduction of the frozen statement S2.1 (ii) to `S21PrepMain`. -/
theorem whole_space_prepared_of_main
    (hmain : ∀ (d : ℕ), 2 ≤ d → ∀ (s : ℝ), 0 ≤ s → s < 2 * (d : ℝ) / 3 → ∀ (a β : ℝ), 0 < a → 0 < β →
      ∀ β₀ : ℝ, 0 ≤ β₀ → ∀ T : ℝ, 0 < T → ∀ c₁ C₁ : ℝ,
      ∃ εstar : ℝ, 0 < εstar ∧ ∃ C₀thr : ℝ, ∀ C₀ : ℝ, C₀thr ≤ C₀ →
        ∃ C : ℝ, S21PrepMain d s a β β₀ T c₁ C₁ εstar C₀ C) :
    HRS.Whole.WholeSpacePreparedStatement := by
  intro d hd s hs0 hs a β ha hβ β₀ hβ₀ T hT c₁ C₁
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨εstar, hε, thr, h⟩ := hmain d hd s hs0 hs a β ha hβ β₀ hβ₀ T hT c₁ C₁
  obtain ⟨C₀min, -, hcl⟩ := HRS.MS.S21.s21_clause1_resulting hd hs0 hsd ha hβ C₁
  obtain ⟨C, hC⟩ := h (max thr C₀min) (le_max_left _ _)
  refine ⟨εstar, hε, max thr C₀min, C, ?_, hC⟩
  intro ρβ hρβ ε ψ _ ρ hρ N hN t ht X hX
  exact hcl (max thr C₀min) (le_max_right _ _) ρβ hρβ εstar ε ψ c₁ ρ hρ N hN t ht X hX

end HRS.Whole
