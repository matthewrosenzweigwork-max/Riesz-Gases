import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.Mov63BAux5

/-!
# S6.7nl.28: unique honest centered L2 representative
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

/-- S6.7nl.28: the centered L2 representative of a function in L2 with zero pairing against sqrt(rho0). -/
theorem s67bd_zero_realization (H : Mov2dTh d s β q ρ₀)
    (h : Euc d → ℝ) (hL : MemLp h 2 volume)
    (hzero : (∫ x, Real.sqrt (ρ₀ x) * h x) = 0) :
    ∃! z : MovL2Zero ρ₀, ∀ᵐ x ∂(volume : Measure (Euc d)), movFun z x = h x := by
  have hin : inner ℝ (movSqrtLp ρ₀) (hL.toLp h) = 0 := by
    rw [HRS.MS.Mov63.mnb_inner_sqrt H hL, hzero]
  have hmem : hL.toLp h ∈ MovL2Zero ρ₀ := mov2d_mem_zero_iff.mpr hin
  refine ⟨⟨hL.toLp h, hmem⟩, ?_, ?_⟩
  · filter_upwards [MemLp.coeFn_toLp hL] with x hx
    exact hx
  · intro z hz
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [hz, MemLp.coeFn_toLp hL] with x hx1 hx2
    exact hx1.trans hx2.symm

end HRS.MS.BreakdownS67
