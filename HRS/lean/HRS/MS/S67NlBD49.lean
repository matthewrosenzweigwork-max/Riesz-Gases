import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovThermAux1
import HRS.MS.WsStatAux5

/-!
# S6.7nl.49: fixed stationary one-body drift bounds
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

/-- The fixed one-body drift `-β` times the thermal cancellation force of `ρ₀`. -/
def s67bd_oneBodyB (d : ℕ) (s β : ℝ) (ρ₀ : Euc d → ℝ) (x : Euc d) : Euc d :=
  -β • movForce d s ρ₀ x

/-- S6.7nl.49: the fixed one-body drift has bounded derivatives of every order up to N. -/
theorem s67bd_onebody_drift (H : Mov2dTh d s β q ρ₀) (N : ℕ) :
    ∃ Mb : ℝ, 0 ≤ Mb ∧ HasCbBound N Mb (s67bd_oneBodyB d s β ρ₀) := by
  obtain ⟨B, hB, -, hcb⟩ := HRS.MS.Mov0.mv0_gapref H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  obtain ⟨Mb, hMb⟩ := hcb N
  have hfun : s67bd_oneBodyB d s β ρ₀ = B := by
    rw [hB]
    funext x
    unfold s67bd_oneBodyB movForce
    rw [HRS.MS.S21.s21_gradU_eq H.hd H.hs0 H.hsd H.hq H.hβ H.hρ x]
  refine ⟨max Mb 0, le_max_right _ _, ?_⟩
  rw [hfun]
  unfold HasCbBound at hMb ⊢
  exact ⟨hMb.1, fun j hj x => (hMb.2 j hj x).trans (le_max_left _ _)⟩

end HRS.MS.BreakdownS67
