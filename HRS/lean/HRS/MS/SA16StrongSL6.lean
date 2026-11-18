import HRS.MS.SA16StrongSL4

/-!
# S.A.16 SL6: `wNormE_eq_lift_norm`

The infimum defining `wNormE` is over a single element (SL4), so it is the norm of that lift.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16
open HRS HRS.Whole HRS.Whole.AppendixA

theorem wNormE_eq_lift_norm (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)]
    (G : WmpSpace d m p) (u : Euc d → ℝ)
    (h : ∀ᵐ x ∂(volume : Measure (Euc d)),
      ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m)=u x) :
    wNormE m p u=ENNReal.ofReal ‖G‖ := by
  unfold wNormE
  refine le_antisymm ?_ ?_
  · exact iInf₂_le_of_le G h le_rfl
  · refine le_iInf₂ fun G' hG' => ?_
    have : G' = G := by
      refine wmp_zero_injective d m p G' G ?_
      filter_upwards [hG', h] with x hx1 hx2
      rw [hx1, hx2]
    rw [this]

end HRS.Whole.AppendixA.Phase2SA16
