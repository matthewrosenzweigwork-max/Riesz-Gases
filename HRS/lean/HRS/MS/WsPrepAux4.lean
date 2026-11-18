import HRS.MS.WsPrepAux3
import HRS.MS.WsPrepAux2
import HRS.MS.MovEntTie
import HRS.Whole.Window

/-!
# S21R packet 4: the S6.6 interface at fixed indices (`MovEntAt`)

`HRS.Whole.mov_entropy` (S6.6) is stated with EXISTENTIAL regularity indices `(j, m)` (S L4553-4554, "AMBIGUITY" in its docstring).
For S2.1 (ii) the class of solutions is `IsResultingSolution` (indices `j + 1 = 100d + 1001` in `C_b`, `m = 102d + 1020` in `Σ^m`), so the
conclusions of S6.6 can be applied to a resulting solution only if they hold AT THESE INDICES (`s21p_resulting_in_class`).  From the bare
existential nothing can be said about the indices: if the witnessed `m` exceeds `102d + 1020`, the resulting solution is not known to
lie in the S6.6 class at all, and the smallness `ε_*` of the frozen statement controls only the lower norms.  (The conditional proof
`mov_entropy_of_diss` uses `j = 1`, `m = d/2 + 8`, which are below the frozen indices; with Σ-norm monotonicity this would suffice, but that is
not visible in the statement of `mov_entropy`.)

`MovEntAt d s j m` is the statement of `mov_entropy` with `(j, m)` fixed (and `1 ≤ j`, `d/2 + j + 6 < m` hypotheses, as the indices of S6.3).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

/-- `mov_entropy` (S6.6) at the fixed indices `(j, m)`. -/
def MovEntAt (d : ℕ) (s : ℝ) (j m : ℕ) : Prop :=
  2 ≤ d → 0 ≤ s → s < d → ∀ (β q : ℝ), 0 < β → 0 < q → ∀ (ρ₀ : Euc d → ℝ),
    IsThermalEquilibrium d s q β ρ₀ → 1 ≤ j → (d : ℝ) / 2 + j + 6 < m →
      ∃ εstar r c₀ c C₁ : ℝ, 0 < εstar ∧ 0 < r ∧ 0 < c₀ ∧ 0 < c ∧ 0 < C₁ ∧
        MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁ ∧
        ∃ C₀ : ℝ,
          (∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
            ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
            ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t → ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
              0 ≤ rieszModulatedEnergy d s X (withDensityReal (ρ t)) + oN d s C₀ N) ∧
          (∃ C : ℝ, ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
            ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
            ∀ N : ℕ, 2 ≤ N → GibbsEntropyContraction d s q β N →
            ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
              (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
              MovParticleSetup P d s q β N X₀ W X →
              ∀ t : ℝ, 0 ≤ t →
                relEntropy (P.map (X t.toNNReal))
                    (modulatedGibbs (rieszKernel d s) N β (withDensityReal (ρ t))) ≤
                  ENNReal.ofReal C *
                    (relEntropy (P.map X₀)
                        (modulatedGibbs (rieszKernel d s) N β (withDensityReal (ρ 0))) +
                      ENNReal.ofReal (N * deltaN d s N))) ∧
          ∀ γ : ℝ, 0 ≤ γ →
            (∃ C : ℝ, ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
              ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
              ∀ N : ℕ, 2 ≤ N → GibbsEntropyContraction d s q β N →
              ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
                [IsProbabilityMeasure P] (X₀ : Ω → EucConfig d N)
                (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
                MovParticleSetup P d s q β N X₀ W X →
                MovPrepared d s N γ (withDensityReal (ρ 0)) (P.map X₀) →
                MovParticleBounds d s q β C₀ C ρ N P X) ∧
            (∀ T : ℝ, 0 < T → ∃ CT : ℝ, ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
              ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
              ∀ N : ℕ, 2 ≤ N → GibbsEntropyContraction d s q β N →
              ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
                [IsProbabilityMeasure P] (X₀ : Ω → EucConfig d N)
                (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
                MovParticleSetup P d s q β N X₀ W X →
                MovPrepared d s N γ (withDensityReal (ρ 0)) (P.map X₀) →
                ∀ b : ℝ, 0 ≤ b →
                  ∫⁻ ζ, ⨆ t ∈ Set.Icc b (b + T),
                      ENNReal.ofReal (movSecondMoment (X t.toNNReal ζ)) ∂P ≤
                    ENNReal.ofReal CT)

/-- `MovEntAt` at admissible indices implies the frozen (existential) `mov_entropy`: the interface below is a strengthening of S6.6, not a
different statement. -/
theorem movEntAt_imp_mov_entropy {d : ℕ} {s : ℝ} {j m : ℕ} (hj : 1 ≤ j) (hm : (d : ℝ) / 2 + j + 6 < m)
    (h : MovEntAt d s j m) : type_of% (@HRS.Whole.mov_entropy d s) := by
  intro hd hs0 hsd β q hβ hq ρ₀ hρ
  exact ⟨j, m, hj, hm, h hd hs0 hsd β q hβ hq ρ₀ hρ hj hm⟩

end HRS.Whole
