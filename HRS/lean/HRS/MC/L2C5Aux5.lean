import HRS.MC.L2C5Aux4

/-!
# Packet L2C-5, helper 5: the slice estimate at a fixed time

For continuous vector fields `u, w` and continuous densities `r, r' ≥ 0` with `(√r - √r')² ≤ e`:
`∫⟨u,u⟩ r + ∫⟨w,w⟩ r' - 2∫⟨u,w⟩√(r r') ≤ 2e ∫|u|² + 2∫ r'|u - w|²`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Sec7 HRS.PDE

namespace HRS.MC.L2C5

variable {d : ℕ}

theorem l2c5_slice {u w : Torus d → Euc d} {r r' : Torus d → ℝ} {e : ℝ}
    (hu : Continuous u) (hw : Continuous w) (hr : Continuous r) (hr' : Continuous r')
    (hr0 : ∀ x, 0 ≤ r x) (hr'0 : ∀ x, 0 ≤ r' x)
    (he : ∀ x, (Real.sqrt (r x) - Real.sqrt (r' x)) ^ 2 ≤ e) :
    (∫ x, inner ℝ (u x) (u x) * Real.sqrt (r x * r x)) +
        (∫ x, inner ℝ (w x) (w x) * Real.sqrt (r' x * r' x)) -
        2 * ∫ x, inner ℝ (u x) (w x) * Real.sqrt (r x * r' x) ≤
      2 * e * (∫ x, ‖u x‖ ^ 2) + 2 * ∫ x, r' x * ‖u x - w x‖ ^ 2 := by
  have i1 : Integrable (fun x => inner ℝ (u x) (u x) * Real.sqrt (r x * r x)) :=
    HRS.MC.L2C4.l2c4_integrable_of_cont ((hu.inner hu).mul (hr.mul hr).sqrt)
  have i2 : Integrable (fun x => inner ℝ (w x) (w x) * Real.sqrt (r' x * r' x)) :=
    HRS.MC.L2C4.l2c4_integrable_of_cont ((hw.inner hw).mul (hr'.mul hr').sqrt)
  have i3 : Integrable (fun x => inner ℝ (u x) (w x) * Real.sqrt (r x * r' x)) :=
    HRS.MC.L2C4.l2c4_integrable_of_cont ((hu.inner hw).mul (hr.mul hr').sqrt)
  have i4 : Integrable (fun x => ‖u x‖ ^ 2) :=
    HRS.MC.L2C4.l2c4_integrable_of_cont (hu.norm.pow 2)
  have i5 : Integrable (fun x => r' x * ‖u x - w x‖ ^ 2) :=
    HRS.MC.L2C4.l2c4_integrable_of_cont (hr'.mul ((hu.sub hw).norm.pow 2))
  have i12 : Integrable (fun x => inner ℝ (u x) (u x) * Real.sqrt (r x * r x) +
      inner ℝ (w x) (w x) * Real.sqrt (r' x * r' x)) := i1.add i2
  have i32 : Integrable (fun x => 2 * (inner ℝ (u x) (w x) * Real.sqrt (r x * r' x))) :=
    i3.const_mul 2
  have i45 : Integrable (fun x => 2 * e * ‖u x‖ ^ 2) := i4.const_mul (2 * e)
  have i55 : Integrable (fun x => 2 * (r' x * ‖u x - w x‖ ^ 2)) := i5.const_mul 2
  have lhs : (∫ x, inner ℝ (u x) (u x) * Real.sqrt (r x * r x)) +
        (∫ x, inner ℝ (w x) (w x) * Real.sqrt (r' x * r' x)) -
        2 * ∫ x, inner ℝ (u x) (w x) * Real.sqrt (r x * r' x) =
      ∫ x, (inner ℝ (u x) (u x) * Real.sqrt (r x * r x) +
        inner ℝ (w x) (w x) * Real.sqrt (r' x * r' x) -
        2 * (inner ℝ (u x) (w x) * Real.sqrt (r x * r' x))) := by
    rw [integral_sub i12 i32, integral_add i1 i2, integral_const_mul]
  have rhs : 2 * e * (∫ x, ‖u x‖ ^ 2) + 2 * ∫ x, r' x * ‖u x - w x‖ ^ 2 =
      ∫ x, (2 * e * ‖u x‖ ^ 2 + 2 * (r' x * ‖u x - w x‖ ^ 2)) := by
    rw [integral_add i45 i55, integral_const_mul, integral_const_mul]
  rw [lhs, rhs]
  refine integral_mono (i12.sub i32) (i45.add i55) fun x => ?_
  have h := l2c5_pointwise (u x) (w x) (hr0 x) (hr'0 x)
  have h2 : 2 * (Real.sqrt (r x) - Real.sqrt (r' x)) ^ 2 * ‖u x‖ ^ 2 ≤ 2 * e * ‖u x‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_right (he x) (sq_nonneg ‖u x‖)
    nlinarith
  simp only []
  nlinarith [h, h2]

end HRS.MC.L2C5
