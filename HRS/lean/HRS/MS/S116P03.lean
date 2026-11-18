import HRS.Whole.Hermite

/-!
# S11.6 packet P03 (`R26-T8B.P03`): exact scalar relation between two oscillator test normalizations

Prefix `s116_`, namespace `HRS.MS.S116`.  `oscTestFun m α = λ_α^{(n-m)/2} • oscTestFun n α` (with `λ_α = 2|α| + d + 1 > 0`).
-/

set_option autoImplicit false

noncomputable section

namespace HRS.MS.S116

open HRS HRS.Whole

theorem s116_oscEigenvalue_pos {d : ℕ} (α : MultiIndex d) : 0 < oscEigenvalue d α := by
  unfold oscEigenvalue
  have : (0 : ℝ) ≤ (α.degree : ℝ) := Nat.cast_nonneg _
  have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  linarith

theorem s116_osc_rescale {d : ℕ} (m n : ℝ) (α : MultiIndex d) :
    oscTestFun m α = fun x => oscEigenvalue d α ^ ((n - m) / 2) * oscTestFun n α x := by
  funext x
  unfold oscTestFun
  rw [← mul_assoc, ← Real.rpow_add (s116_oscEigenvalue_pos α)]
  congr 2
  ring

end HRS.MS.S116

end
