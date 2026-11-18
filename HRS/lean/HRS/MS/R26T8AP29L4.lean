import HRS.MS.R26T8AO00
import HRS.MS.R26T8AD04

/-!
# S8.2 T8A P29 (aSource clause): the `aSource` bound for any constant `C' ≥ C`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_p29_aSource (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ C' : ℝ, C ≤ C' → ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ f : Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → TestBound (testOrder d) A f →
      MemLp (aSource (HRS.Whole.withDensityReal rho) f) 2 (HRS.Whole.withDensityReal rho) ∧
      eLpNorm (aSource (HRS.Whole.withDensityReal rho) f) 2 (HRS.Whole.withDensityReal rho) ≤
        ENNReal.ofReal (C' * A) := by
  obtain ⟨C, hC, h⟩ := r26t8a_aSource_bound d hd a beta ha hbeta
  refine ⟨C, hC, fun C' hCC' rho hrho f A hA hf => ?_⟩
  obtain ⟨hm, hb⟩ := h rho hrho f A hA hf
  exact ⟨hm, hb.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCC' hA))⟩

end HRS.MS.R26T8A

end
