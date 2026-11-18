import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD08
import HRS.PDE.ToolboxRd.Fourier

/-!
# S6.7nl.21D: loss-index arithmetic and Sobolev monotonicity
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

/-- S6.7nl.21D: the loss index movA - 1 lowers the Sobolev index, with the norm monotone. -/
theorem s67bd_local_loss_conversion (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (r : ℝ) (hr : 1 ≤ r) (u : Euc d → ℝ)
    (hu : HRS.PDE.ToolboxRd.MemSobolev (r - 1 + (d : ℝ) - s) u) :
    HRS.PDE.ToolboxRd.MemSobolev (r - (movA d s - 1)) u ∧
    s67bd_Hnorm (r - (movA d s - 1)) u ≤ s67bd_Hnorm (r - 1 + (d : ℝ) - s) u := by
  have hA : s + 2 - (d : ℝ) ≤ movA d s := by
    unfold movA
    exact le_max_right _ _
  have hle : r - (movA d s - 1) ≤ r - 1 + (d : ℝ) - s := by linarith
  have hmem := HRS.PDE.ToolboxRd.FourierAux.memSobolev_mono hle hu
  refine ⟨hmem, ?_⟩
  unfold s67bd_Hnorm
  apply Real.sqrt_le_sqrt
  unfold HRS.PDE.ToolboxRd.sobolevNormSq
  apply integral_mono hmem.2 hu.2
  intro ξ
  have hb : (1 : ℝ) ≤ 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by
    have : 0 ≤ 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by positivity
    linarith
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hb hle) (by positivity)

end HRS.MS.BreakdownS67
