import Mathlib

/-!
# Packet CEPH0, auxiliary 1: abstract mixture lemmas (suprema, Kullback-Leibler divergence)
-/

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.CepH0

/-- A finite sum of suprema over independent index types is bounded by the supremum of the sums. -/
theorem h0_sum_iSup_le {ι : Type*} [DecidableEq ι] (s : Finset ι) {A : ι → Type*}
    [∀ c, Nonempty (A c)] (f : ∀ c, A c → ℝ≥0∞) :
    ∑ c ∈ s, ⨆ a, f c a ≤ ⨆ a : ∀ c, A c, ∑ c ∈ s, f c (a c) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert c s hc ih =>
    rw [Finset.sum_insert hc]
    calc (⨆ a, f c a) + ∑ c ∈ s, ⨆ a, f c a
        ≤ (⨆ a, f c a) + ⨆ a : ∀ c, A c, ∑ c ∈ s, f c (a c) := add_le_add_right ih _
      _ ≤ _ := by
        refine ENNReal.iSup_add_iSup_le fun a b => ?_
        refine le_iSup_of_le (Function.update b c a) ?_
        rw [Finset.sum_insert hc]
        simp only [Function.update_self]
        have h : ∑ c' ∈ s, f c' (Function.update b c a c') = ∑ c' ∈ s, f c' (b c') := by
          refine Finset.sum_congr rfl fun c' hc' => ?_
          rw [Function.update_of_ne]
          rintro rfl
          exact hc hc'
        rw [h]

end HRS.MC.CepH0
