import HRS.MS.R26T8AF07h
import HRS.MS.R26T8AF06
import HRS.MS.R26T8AF05e

/-!
# S8.2 observed-time layer, packet T8A.F07 (helper 07i): the second generator iterate

For a Schwartz `f`, `u = LIter 1 f = localP f + oneJ f`, and `LIter 2 f = localP u + oneJ u`.
With `p` the Schwartz function `localP f` (F06) and `J = oneJ f`, `localP u = localP p + localP J` (F07f), and the
three pieces are bounded by F06 (`localP` of `localP f`), F07g (`localP J`), and F05 (`oneJ u`), with the Schwartz
norms of `f` at order `r+4` (F06 `f06_sob`).  Output: `sobolevNormE r (LIter 2 f) ≤ ofReal (K · oscNorm (r+4) f)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_f07i_sob_lt_top {m : ℝ} {u : Euc d → ℝ} (h : HRS.PDE.ToolboxRd.MemSobolev m u) :
    sobolevNormE m u < ⊤ := by
  unfold sobolevNormE
  rw [if_pos h]
  exact ENNReal.ofReal_lt_top

theorem r26t8a_f07i_sobSmooth_add {p q : Euc d → ℝ} (hp : r26t8a_SobSmooth p)
    (hq : r26t8a_SobSmooth q) : r26t8a_SobSmooth (fun y => p y + q y) := by
  refine ⟨hp.1.add hq.1, fun m => ?_⟩
  refine r26t8a_f05c_mem_of_lt_top (lt_of_le_of_lt (HRS.MH.AdjointRd.Phase2SA12V3.sa12v3_sobolevNormE_add_le
    (m : ℝ) p q) ?_)
  exact ENNReal.add_lt_top.2 ⟨r26t8a_f07i_sob_lt_top (hp.2 m), r26t8a_f07i_sob_lt_top (hq.2 m)⟩

end HRS.MS.R26T8A

end
