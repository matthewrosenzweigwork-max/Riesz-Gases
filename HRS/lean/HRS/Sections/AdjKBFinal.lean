import HRS.Sections.AdjKBAux2
import HRS.Sections.AdjKBAux6

/-!
# ADJKB Final: relocated proofs of COMPACT and KOLM (statements verbatim from `AdjKSpec`)
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

/-- **COMPACT** (relocated proof). -/
theorem adjk_compactSet_isCompact_proof (d : ℕ) (m T m₁ R : ℝ) (hm₁ : m₁ < m) (δ : ℕ → ℝ)
    (hδ : ∀ j, 0 < δ j) : IsCompact (adjkCompactSet d m T m₁ R δ) :=
  adjkb_compactSet_isCompact d m T m₁ R hm₁ δ hδ

example := (@adjk_compactSet_isCompact_proof : type_of% @HRS.AdjK.adjk_compactSet_isCompact)

/-- **KOLM** (relocated proof). -/
theorem adjk_kolmogorov_equicont_proof {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (T : ℝ) (hT : 0 < T) (p q : ℝ) (hq : 1 < q) (M : ℝ≥0)
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] (P : ∀ i, Measure (Ω i))
    [∀ i, IsProbabilityMeasure (P i)] (Y : ∀ i, Set.Icc (0 : ℝ) T → Ω i → E)
    (hY : ∀ i, IsKolmogorovProcess (Y i) (P i) p q M)
    (hcont : ∀ i, ∀ᵐ ω ∂P i, Continuous fun t => Y i t ω) :
    ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ i,
      P i {ω | ∃ s t : Set.Icc (0 : ℝ) T, |(s : ℝ) - t| ≤ δ ∧ η < ‖Y i s ω - Y i t ω‖} ≤
        ENNReal.ofReal ε :=
  adjkb_kolmogorov_equicont T hT p q hq M P Y hY hcont

example := (@adjk_kolmogorov_equicont_proof : type_of% @HRS.AdjK.adjk_kolmogorov_equicont)

end HRS.AdjK
