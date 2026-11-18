import HRS.Main.FullBoundsGibbs
import HRS.Main.Equilibrium29Spec

/-!
# FULLBOUNDS (conditional on the chunk-D lemma `equilibrium_initial_law`)

**DEPENDS ON A `sorry`'d STATEMENT.**  `fb_clause_gibbs_cond` and `fb_prepared_full_bounds_cond` use the frozen
`HRS.Main.equilibrium_initial_law` (`HRS/Main/Equilibrium29Spec.lean:399`, chunk D, still `sorry`) as a black box, so
`#print axioms` shows `sorryAx` until chunk D lands.  Everything else is proved: `fb_clause_gibbs_of`
(`FullBoundsGibbs`), `fb_prepared_full_bounds_beta0` (`FullBoundsBeta0`).  Once `equilibrium_initial_law` is replaced by
its `_proof`, `fb_prepared_full_bounds_cond` becomes the unconditional proof of `prepared_full_bounds`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

/-- The frozen `equilibrium_initial_law` has exactly the type `FbEqInitialLaw d`. -/
theorem fb_eq_initial_law : FbEqInitialLaw d := @equilibrium_initial_law d

/-- **Conditional on the `sorry`'d `equilibrium_initial_law`.**  Clause (ii) of `prepared_full_bounds`
(Gibbs preparation, `β₀ > 0`); see `fb_clause_gibbs_of`. -/
theorem fb_clause_gibbs_cond (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ)
    (hT : 0 < T) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        law P X₀ = modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0 →
      ∀ (ν : Measure (NegSobolev d m)),
        IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0) →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Y₀ Y →
        (0 < β₀ →
          smoothDist 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            C * (Real.sqrt N * deltaN d S.s N) ∧
          wassersteinE 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            ENNReal.ofReal (C * (Real.sqrt N * deltaN d S.s N +
              deltaN d S.s N ^ ((1 : ℝ) / 4)))) :=
  fb_clause_gibbs_of fb_eq_initial_law S m hm T hT β₀ hβ₀

/-- **Conditional on the `sorry`'d `equilibrium_initial_law`.**  `prepared_full_bounds`
(`HRS/Main/Headline.lean:920`) verbatim, proved by cases on `β₀ = 0`. -/
theorem fb_prepared_full_bounds_cond (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ)
    (hT : 0 < T) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        law P X₀ = modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0 →
      ∀ (ν : Measure (NegSobolev d m)),
        IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0) →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Y₀ Y →
        (β₀ = 0 →
          smoothDist 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            C * (Real.sqrt N * deltaN d S.s N + iidRateSmooth d m N) ∧
          wassersteinE 1 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            ENNReal.ofReal (C * (Real.sqrt N * deltaN d S.s N +
              deltaN d S.s N ^ ((1 : ℝ) / 4) + iidRateW d m N))) ∧
        (0 < β₀ →
          smoothDist 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            C * (Real.sqrt N * deltaN d S.s N) ∧
          wassersteinE 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            ENNReal.ofReal (C * (Real.sqrt N * deltaN d S.s N +
              deltaN d S.s N ^ ((1 : ℝ) / 4)))) ∧
        (β₀ = 0 → S.s = 0 →
          wassersteinE 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            ENNReal.ofReal (C * ((N : ℝ) ^ (-(1 : ℝ) / 4) + iidRateW d m N ^ ((1 : ℝ) / 3)))) := by
  by_cases h0 : β₀ = 0
  · obtain ⟨C, hC, h⟩ := fb_prepared_full_bounds_beta0 S m hm T hT β₀ hβ₀
    refine ⟨C, hC, ?_⟩
    intro a ha N hN Ω _ P _ X₀ W X hSel hfilt hinit ν hν Ω' _ P' _ Y₀ Y hY
    obtain ⟨h1, h3⟩ := h a ha N hN P X₀ W X hSel hfilt hinit ν hν P' Y₀ Y hY
    exact ⟨h1, fun hpos => absurd h0 hpos.ne', h3⟩
  · obtain ⟨C, hC, h⟩ := fb_clause_gibbs_cond S m hm T hT β₀ hβ₀
    refine ⟨C, hC, ?_⟩
    intro a ha N hN Ω _ P _ X₀ W X hSel hfilt hinit ν hν Ω' _ P' _ Y₀ Y hY
    exact ⟨fun h' => absurd h' h0, h a ha N hN P X₀ W X hSel hfilt hinit ν hν P' Y₀ Y hY,
      fun h' => absurd h' h0⟩

example := (@fb_prepared_full_bounds_cond : type_of% @HRS.Main.prepared_full_bounds)

end Main

end HRS

end
