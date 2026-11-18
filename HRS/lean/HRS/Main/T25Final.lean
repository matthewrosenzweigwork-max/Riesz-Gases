import HRS.Main.T25Aux5

/-!
# T25-IN: relocated proofs of the frozen statements proved by this packet

RELOCATION PATTERN: the frozen statements of `HRS/Main/Headline.lean` are not edited; each proved one is restated VERBATIM here as
`<name>_proof` and tied by `example := (@<name>_proof : type_of% @HRS.Main.<name>)`.

* `prepared_scales_proof` (Theorem 2.5, last paragraph, TeX M L795-801, proof L6748-6767): PREP-SCALES, from `T25Aux5`
  (`entropy_endpoint`, `log_prep_uniform`, the ratio identity `P:eq:initial-p-ratio`, `pressure_two_sided`).
* `prepared_fluctuations`, `prepared_fluctuations_W2`: NOT proved (see the chain plan in the header of `T25Aux1.lean`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

theorem prepared_scales_proof (S : PreparedData d) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) :
    (∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      relEntropy (modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0) (S.refMeasure N 0) < ⊤ ∧
      S.B N (modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0) ≤ C * ((N : ℝ) * deltaN d S.s N)) ∧
    ((0 < β₀ ∨ S.s = 0) →
      ∃ p₀ : ℝ, 1 < p₀ ∧ ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
        MemLp (fun Y => (((modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0).rnDeriv
            (S.refMeasure N 0)) Y).toReal) (ENNReal.ofReal p₀) (S.refMeasure N 0) ∧
        S.J N (modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0) p₀ ≤ C * ((N : ℝ) * deltaN d S.s N)) :=
  HRS.T25.t25_prepared_scales S β₀ hβ₀

example := (@prepared_scales_proof : type_of% @HRS.Main.prepared_scales)

end Main

end HRS

end
