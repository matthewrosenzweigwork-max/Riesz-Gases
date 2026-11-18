import HRS.MS.WsPrepAux13
import HRS.MS.WsPrepAux6
import HRS.MS.MovEntAux1

/-!
# S21R packet 14: `S21PrepMain` from the two metric bounds (the measurability conjuncts are proved)

`S21PrepMetric d s a β β₀ T c₁ C₁ εstar C₀ C` is `S21PrepMain` without its two measurability conjuncts: the data are the same, the conclusion
is the pair of bounds
`smoothDist 2 (law Ξ_{a₀}) (law Z^{a₀}) ≤ C(√N δ_N + w_N + i_N)` and `W_1(law Ξ_{a₀}, law Z^{a₀}) ≤ C(√N δ_N + √w_N + j_N)`.

`s21PrepMain_of_metric`: the a.e. measurability of the particle window (WsPrepAux13, weak continuity of the resulting solution WsPrepAux12) and of
the window of `Z` (WsPrepAux11) hold in the whole class, so `S21PrepMain` follows from `S21PrepMetric`.
`whole_space_prepared_of_metric`: the reduction of the frozen statement S2.1 (ii) to `S21PrepMetric` at one completion constant.  This is the
precise content of S2.1 (ii) that is still open.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole

variable {d : ℕ}

/-- `S21PrepMain` without the two measurability conjuncts. -/
def S21PrepMetric (d : ℕ) (s a β β₀ T c₁ C₁ εstar C₀ C : ℝ) : Prop :=
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
      smoothDist 2 (law P (flucPathW (wholeSpaceIndex d) T a₀ (Real.sqrt N) X ρ))
          (law P' (processWindow (wholeSpaceIndex d) T a₀ Z)) ≤
        C * (Real.sqrt N * deltaN d s N + localizationRate d s C₀ N + iN d s β₀ N) ∧
      wassersteinE 1 (law P (flucPathW (wholeSpaceIndex d) T a₀ (Real.sqrt N) X ρ))
          (law P' (processWindow (wholeSpaceIndex d) T a₀ Z)) ≤
        ENNReal.ofReal (C * (Real.sqrt N * deltaN d s N +
          Real.sqrt (localizationRate d s C₀ N) + jN d s β₀ N))

theorem s21PrepMain_of_metric {s a β β₀ T c₁ C₁ εstar C₀ C : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (ha : 0 < a) (hβ : 0 < β) (hT : 0 < T)
    (h : S21PrepMetric d s a β β₀ T c₁ C₁ εstar C₀ C) : S21PrepMain d s a β β₀ T c₁ C₁ εstar C₀ C := by
  intro ρβ hρβ ε ψ hadm ρ hres N hN hGEC Ω _ P _ X₀ W X hBr hInd hlaw hstrong Ω' _ P' _ Z hZ a₀ ha₀
  obtain ⟨hp, hpos, -⟩ := HRS.MS.MovEnt.s66_rho0_facts hd hs0 hsd ha hβ hρβ
  have hd1 : 1 ≤ d := by omega
  have hm : (d : ℝ) < ((wholeSpaceIndex d : ℕ) : ℝ) := by
    unfold wholeSpaceIndex
    push_cast
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hweak := fun ψ' hψ' hB' => s21p_rho_weak_cont hp hpos hres ψ' hψ' hB'
  refine ⟨?_, s21p_Z_window_aemeas P' ha₀ hT.le (hZ (a₀ + T)), h ρβ hρβ ε ψ hadm ρ hres N hN hGEC
    P X₀ W X hBr hInd hlaw hstrong P' Z hZ a₀ ha₀⟩
  refine s21p_fluc_window_aemeas hd1 (by omega) hm ha₀ hT.le P X ρ _ (hstrong 0).adapted
    (hstrong (a₀ + T)).cont (fun t ht => (hres.global (a₀ + T)).density t ht) ?_
  intro ψ' hψ' hB'
  exact (hweak ψ' hψ' hB').mono fun t ht => ht.1

/-- The reduction of the frozen statement S2.1 (ii) to the metric bounds `S21PrepMetric` (one completion constant). -/
theorem whole_space_prepared_of_metric
    (hmain : ∀ (d : ℕ), 2 ≤ d → ∀ (s : ℝ), 0 ≤ s → s < 2 * (d : ℝ) / 3 → ∀ (a β : ℝ), 0 < a → 0 < β →
      ∀ β₀ : ℝ, 0 ≤ β₀ → ∀ T : ℝ, 0 < T → ∀ c₁ C₁ : ℝ,
      ∃ εstar : ℝ, 0 < εstar ∧ ∃ C₀ C : ℝ, 0 ≤ C ∧ S21PrepMetric d s a β β₀ T c₁ C₁ εstar C₀ C) :
    HRS.Whole.WholeSpacePreparedStatement := by
  refine whole_space_prepared_of_main' fun d hd s hs0 hs a β ha hβ β₀ hβ₀ T hT c₁ C₁ => ?_
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨εstar, hε, C₀, C, hC0, h⟩ := hmain d hd s hs0 hs a β ha hβ β₀ hβ₀ T hT c₁ C₁
  exact ⟨εstar, hε, C₀, C, hC0, s21PrepMain_of_metric hd hs0 hsd ha hβ hT h⟩

end HRS.Whole
