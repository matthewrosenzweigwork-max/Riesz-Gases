import Mathlib
import HRS.Whole.AppendixALemmas
import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerFinal
import HRS.MH.CoercTestSpecDefs
import HRS.MH.CoercTestW7d

/-!
# CoercTest W7e: `p_assembly`

Statement copied verbatim from `HRS/MH/CoercTestSpec.lean`.
Proof: `completionNonnegRd_exists` (first half) and `test_bound_core` (test clause), joined by
`wholeCoercivityPair_iff`, with the maximum of the two thresholds `C₀'`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace HRS.MH.CoercTest

open HRS.MH.CoercLower

variable {d N : ℕ}

/-- [W7e] Final assembly: the frozen target `HRS.Whole.AppendixALemmas.whole_coercivity_pair`
(`HRS/Whole/AppendixALemmas.lean:92`), copied verbatim.  Route: `completionNonnegRd_exists` (CoercLowerFinal:23) and
W7d; take the maximum of the two `C₀'`; `WholeCoercivityPair` unfolds by `wholeCoercivityPair_iff`
(`CompletionNonnegRd` is upward closed in `C₀'` by the quantifier `∀ C₀ ≥ C₀'`). -/
theorem p_assembly (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀' C₁ : ℝ, 0 ≤ C₀' ∧ ∀ C₀ : ℝ, C₀' ≤ C₀ → HRS.Whole.AppendixALemmas.WholeCoercivityPair d s C₀ C₁ := by
  obtain ⟨C₀a, hC₀a, hcomp⟩ := completionNonnegRd_exists (d := d) hd hs0 hsd
  obtain ⟨C₁, C₀b, hC₁, hC₀b, htest⟩ := test_bound_core (d := d) hd hs0 hsd
  refine ⟨max C₀a C₀b, C₁, hC₀a.trans (le_max_left _ _), fun C₀ hC₀ => ?_⟩
  have h1 : C₀a ≤ C₀ := le_trans (le_max_left _ _) hC₀
  have h2 : C₀b ≤ C₀ := le_trans (le_max_right _ _) hC₀
  exact (HRS.MH.CoercTest.wholeCoercivityPair_iff d s C₀ C₁).2 ⟨hcomp C₀ h1, hC₁, htest C₀ h2⟩

end HRS.MH.CoercTest
