import HRS.MC.S7PIDTNucg
import HRS.MC.S7PIDTFam
import HRS.MC.S7PIDTSys
import HRS.MC.S7PIDTBound

/-!
# Packet PI-D, sub-packet T (part 13): proof of `s7_PID_nuc_trunc` (D4c)

Statement verbatim from `HRS/MC/S7PIDPlan.lean`.  Route (see the docstring there): for `c < c'`, the coordinate families
`g_i(u) = G(p(u) 1_{u ≤ t_i} V^{t_i,u} e_k)` of `S7PIDTFam` have a Gaussian system `(Y, Y')` (`S7PIDTSys`) with
`nuc_ν^F(M) = E M[polyPath Y, polyPath Y']` (`S7PIDTNucg`); the bounds follow from `S7PIDTBound`
and `s7_PID_poly_proof`.  The coarse tensor `nuc_n` is read off the fine system `ν = n+1` by the reindexing `i ↦ 2 i`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDT

open HRS HRS.Sec7 HRS.MC.Sec7.PID

variable {d : ℕ}

lemma S7PIDT_grid_double (c c' : ℝ) (n i : ℕ) : gridPt c c' n i = gridPt c c' (n + 1) (2 * i) := by
  unfold gridPt
  push_cast
  rw [pow_succ]
  field_simp

lemma S7PIDT_theta4 (n : ℕ) : ((2 : ℝ) ^ (-(n : ℝ) / 4)) ^ 4 = 1 / 2 ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have : -(n : ℝ) / 4 * ((4 : ℕ) : ℝ) = -(n : ℝ) := by push_cast; ring
  rw [this, Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]

end HRS.MC.Sec7.S7PIDT

end
