import HRS.MS.SA12C33
import HRS.MS.SA12X3C15K

/-! Box energy: the exact sign of a zero-source nonlocal term. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MH.AdjointRd.Phase2SA12C
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction
variable {d : ℕ}

theorem sa12c_boxJetPair_neg (m : ℕ) (L : ℝ) (F N : Euc d → ℝ) :
    boxJetPair m L F (fun y => -N y + 0) = -boxJetPair m L F N := by
  unfold boxJetPair
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun idx _ => ?_
  rw [← integral_neg]
  congr 1
  funext x
  rw [sa12x3_pd_neg_add_zero]; ring

end HRS.MH.AdjointRd.Phase2SA12C
