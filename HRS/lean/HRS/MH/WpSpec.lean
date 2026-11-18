import HRS.Main.GFFinal4
import HRS.Uniform.Q45Max

/-!
# `general_fluctuation_Wp` (Comparison.lean): statement-only packet specification (Chunk H)

Plan: the Theorem 2.1 chain of `HRS/Main/GFFinal*.lean` redone at order `p ≥ 2`.  Pathwise inputs (remainder bound, couplings) are
independent of `p`; only the maximal inequality and the Minkowski step change.  Every theorem below is `sorry`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.Wp

open HRS HRS.GF HRS.Uniform HRS.Uniform.Kot

variable {d : ℕ}

/-- **P1** (size M, about 130 lines).  `HRS.Uniform.Q45.maximal_estimate_meas` (Q45Max.lean:24) at order `p ≥ 2`: same stochastic
convolution `Z`, same continuity and `AEMeasurable (Z t)` conjuncts, and the sup-bound `E sup‖Z‖^p ≤ C · E (∫ ‖Σ‖₁)^{p/2}`.  Route: copy the
proof of Q45Max.lean:24-end with `HilbertBDG.hilbert_bdg p hp` in place of `hilbert_bdg 2`, constant `c ^ p * Cb` in the two-level branch
and `CD p K T` (MaximalDissipative.lean) in the dissipative branch (see `maximal_estimate_twoLevel` MaximalTwoLevel.lean:583 and
MaximalDissipative.lean:103 for the order-`p` statements, and `sup_Z_bound` KotConv.lean:1080).  The pointwise estimate `sup‖Z‖ ≤ c · sup‖M‖` of the
`p = 2` proof is independent of `p`. -/
theorem maximal_estimate_meas_p (T K p : ℝ) (hT : 0 ≤ T) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ mΩ)
        (H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
        [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
        (S : EvolData H E) (_ : S.MaxHyp T K)
        (M : ℝ → Ω → H) (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ))
        (_ : IsHilbertMartingaleWithCovariation P ℱ T M Sg),
        ∃ Z : ℝ → Ω → E,
          (∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P S.VE S.j M 0 t (Z t)) ∧
          (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T)) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (Z t) P) ∧
          ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Z t ω‖ₑ) ^ p ∂P ≤
            ENNReal.ofReal C *
              ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ω))) ^ (p / 2) ∂P := by
  sorry

/-- **P3a** (size S, about 50 lines).  `gff_initial_term_eq` (GFFinal2.lean:16) for every `p > 0`, with no finiteness hypothesis and the
right side in `ℝ≥0∞`: `‖Ξ⁰ - A η'‖_{L^p(P₁)} = A_N ε_{N,p}` where `ε_{N,p}` is the `lintegral` norm.  Route: steps 1 and 2 of the proof of
`gff_initial_term_eq` verbatim; step 3 (Bochner integral to `lintegral`) is not needed. -/
theorem gff_initial_term_eq_lintegral (S : GeneralSetup d) {N : ℕ} {Ω Ω₁ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₁]
    {P : Measure Ω} {P₁ : Measure Ω₁} {π₁ : Ω₁ → Ω} (hπ₁ : MeasurePreserving π₁ P₁ P)
    (X₀ : Ω → Config d N) (X : ℝ≥0 → Ω → Config d N) (hX0 : ∀ᵐ ω ∂P, X 0 ω = X₀ ω)
    (hX₀m : AEMeasurable X₀ P) (η₀ : Ω → NegSobolev d (S.γ : ℝ)) (η' : Ω₁ → NegSobolev d (S.γ : ℝ))
    (hη₀ : Measurable η₀) (hη' : Measurable η')
    (hlaw : P₁.map (fun ω' => (X₀ (π₁ ω'), η' ω')) = P.map (fun ω => (X₀ ω, η₀ ω)))
    (hγm : (d : ℝ) / 2 < (S.γ : ℝ)) (p : ℝ) (hp : 0 < p) :
    (∫⁻ ω, ‖flucProc (S.γ : ℝ) (sigN S N) (fun t ω => X t (π₁ ω)) (S.ρ N) 0 ω - AN S N • η' ω‖ₑ ^ p ∂P₁) ^
        (1 / p) = ENNReal.ofReal (AN S N) *
          (∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (S.γ : ℝ) (empirical (X₀ ω))
            (withDensityReal (S.ρ N 0)) - η₀ ω‖ₑ ^ p ∂P) ^ (1 / p) := by
  sorry

end HRS.MH.Wp
