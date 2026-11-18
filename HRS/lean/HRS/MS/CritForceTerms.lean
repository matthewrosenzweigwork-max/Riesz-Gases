import HRS.MS.CritForceGeometric

/-!
# S8.2 (core X, glue): a block supremum dominated by a finite sum of terms

If a block supremum is almost surely at most a finite sum of terms (boundary terms, drift integral,
martingale maximal function, deterministic error) each of which has an AEMeasurable `ℝ≥0∞` version
with a known `L²` bound, then the block has an AEMeasurable almost sure majorant whose `L²` norm is at
most the sum of the bounds.  This is exactly the shape of the majorant hypothesis of
`s82_history_bound_maj` (`S82ScalarBlocksMaj`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S82BD

open HRS HRS.Whole

theorem s82_blocks_of_terms {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {n : ℕ} (S : Ω → ℝ≥0∞) (Ti : Fin n → Ω → ℝ≥0∞) (b : Fin n → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hm : ∀ i, AEMeasurable (Ti i) P)
    (hb : ∀ i, (∫⁻ ζ, (Ti i ζ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (b i))
    (hdom : ∀ᵐ ζ ∂P, S ζ ≤ ∑ i, Ti i ζ) :
    ∃ R : Ω → ℝ≥0∞, AEMeasurable R P ∧ (∀ᵐ ζ ∂P, S ζ ≤ R ζ) ∧
      (∫⁻ ζ, (R ζ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (∑ i, b i) := by
  refine ⟨fun ζ => ∑ i, Ti i ζ, Finset.aemeasurable_fun_sum _ fun i _ => hm i, hdom, ?_⟩
  have key : ∀ s : Finset (Fin n),
      (∫⁻ ζ, (∑ i ∈ s, Ti i ζ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (∑ i ∈ s, b i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      have hsm : AEMeasurable (fun ζ => ∑ i ∈ s, Ti i ζ) P :=
        Finset.aemeasurable_fun_sum _ fun i _ => hm i
      have h1 := s82_minkowski P (Ti a) _ (hm a) hsm
      simp only [Finset.sum_insert ha]
      rw [ENNReal.ofReal_add (hb0 a) (Finset.sum_nonneg fun i _ => hb0 i)]
      exact h1.trans (add_le_add (hb a) ih)
  exact key Finset.univ

end HRS.MS.S82BD
