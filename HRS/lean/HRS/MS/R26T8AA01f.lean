import HRS.MS.R26T8AA01e

/-!
# S8.2 T8A A01 (part f): principal-value truncation of an odd kernel
For `κ` odd, measurable, bounded away from `0`, and `φ` with integrable canonical integrand at `u`:
`∫_{ε < ‖u-z‖, ε < ‖v-z‖} φ(z) κ(u-z) dz → ∫ (if ‖u-z‖ ≤ 1/4 then (φ z - φ u) κ(u-z) else φ z κ(u-z)) dz` as `ε → 0+`
(`v ≠ u` a second point at which `φ κ(u-·)` is locally integrable).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_a01_annulus_zero {κ : Euc d → ℝ} (hκm : Measurable κ) (hodd : ∀ w, κ (-w) = -κ w) (u : Euc d)
    {ε : ℝ} (hε : 0 < ε) (hκb : ∃ B, ∀ w : Euc d, ε ≤ ‖w‖ → |κ w| ≤ B) :
    ∫ z, (if ε < ‖u - z‖ ∧ ‖u - z‖ ≤ 1 / 4 then κ (u - z) else 0) = 0 := by
  set h : Euc d → ℝ := fun w => if ε < ‖w‖ ∧ ‖w‖ ≤ 1 / 4 then κ w else 0 with hh
  have e1 : ∫ z, h (u - z) = ∫ w, h w := integral_sub_left_eq_self h volume u
  have e2 : ∫ w, h (-w) = ∫ w, h w := integral_neg_eq_self h volume
  have hneg : ∀ w, h (-w) = -h w := by
    intro w
    simp only [hh, norm_neg, hodd]
    split_ifs <;> simp
  have e3 : ∫ w, h (-w) = -∫ w, h w := by
    simp only [hneg]; exact integral_neg _
  have : ∫ w, h w = 0 := by linarith
  simpa [hh] using (show ∫ z, h (u - z) = 0 by rw [e1, this])

end HRS.MS.R26T8A
