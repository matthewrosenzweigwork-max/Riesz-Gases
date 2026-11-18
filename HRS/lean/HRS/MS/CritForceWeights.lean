import HRS.MS.CritForceDefs

/-!
# S8.2.05: summability of the explicit Hermite weights
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S82BD

open HRS HRS.Whole

theorem s82_weight_summable (d : ℕ) (hd : 2 ≤ d) (m : ℝ)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) :
    (∀ α : MultiIndex d, 0 ≤ s82Weight d m α) ∧
      Summable (fun α : MultiIndex d => (s82Weight d m α) ^ 2) := by
  have hpos : ∀ α : MultiIndex d, 0 < oscEigenvalue d α := fun α => by
    unfold oscEigenvalue
    have : (0 : ℝ) ≤ (α.degree : ℝ) := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
    linarith
  refine ⟨fun α => Real.rpow_nonneg (hpos α).le _, ?_⟩
  have hM : (s82FeatureOrder d : ℝ) ≤ 8 * d + 80 + d + 6 := by
    unfold s82FeatureOrder
    have h1 : (d + 1) / 2 ≤ d := by omega
    have h2 : (8 * d + 80 + (d + 1) / 2 + 6 : ℕ) ≤ 8 * d + 80 + d + 6 := by omega
    exact_mod_cast h2
  have hm' : (24 * d + 240 : ℝ) ≤ m := by
    have : (wholeSpaceIndex d : ℝ) = 24 * d + 240 := by
      unfold wholeSpaceIndex; push_cast; ring
    linarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hlt : (d : ℝ) < m - s82FeatureOrder d - 4 := by linarith
  have hsum := (summable_oscEigenvalue_rpow_iff (d := d) (by omega) (m - s82FeatureOrder d - 4)).2 hlt
  refine hsum.congr fun α => ?_
  unfold s82Weight
  rw [← Real.rpow_natCast, ← Real.rpow_mul (hpos α).le]
  congr 1
  push_cast
  ring

end HRS.MS.S82BD
