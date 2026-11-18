import HRS.MS.FixEqP1Aux1

/-!
Weighted chart norms in this packet are not weighted supremum norms.  For
`f : Euc d → ℝ`, `weightedSobolevE r Pw f` is the square root of the sum,
over all ordered derivatives of order at most `r`, of
`∫⁻ x, ofReal (jbracket x ^ (-2 * Pw) * |∂ f x|^2)`.  In particular, this
is a weighted `L²` Sobolev norm.

For the source/target pair `(r, Pw)` and `(r - 2, Pw + 2)`, the target
weight gains a factor `jbracket x ^ (-4)`.  Outside `jbracket x ≥ ρ`,
`ρ ≥ 1`, this factor is at most `ρ ^ (-4)`, hence its contribution to a
norm (after taking a square root) has order `ρ ^ (-2)`.  The theorem below
records the pointwise comparison underlying that tail estimate.  The local
compactness step is an `L²` Rellich theorem and is not supplied here.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.FixEq

variable {d : ℕ}

/-- On the spatial tail `jbracket x ≥ ρ`, increasing the weight parameter
from `Pw` to `Pw + 2` contributes the exact fourth-power decay factor. -/
theorem fp81s21_weightedRellich_tail_weight
    {Pw ρ : ℝ} {x : Euc d} (hρ : 1 ≤ ρ) (hx : ρ ≤ jbracket x) :
    jbracket x ^ (-2 * (Pw + 2)) ≤
      ρ ^ (-4 : ℝ) * jbracket x ^ (-2 * Pw) := by
  have hρpos : 0 < ρ := lt_of_lt_of_le (by norm_num) hρ
  have hfactor : jbracket x ^ (-4 : ℝ) ≤ ρ ^ (-4 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hρpos hx (by norm_num)
  have hsplit : jbracket x ^ (-2 * (Pw + 2)) =
      jbracket x ^ (-4 : ℝ) * jbracket x ^ (-2 * Pw) := by
    rw [show -2 * (Pw + 2) = (-4 : ℝ) + (-2 * Pw) by ring,
      Real.rpow_add (s57p_jbracket_pos x)]
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hfactor
    (Real.rpow_nonneg (s57p_jbracket_pos x).le _)

#print axioms HRS.Fp81.S21.fp81s21_weightedRellich_tail_weight

end HRS.Fp81.S21
