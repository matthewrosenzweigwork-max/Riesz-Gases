import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.ThCorrSob
import HRS.MS.MovForceAux4
import HRS.MS.S67NlBD08
import HRS.MS.S67NlBD14B

/-!
# S6.7nl.21C: physical compact convolution gain at `r - 1 + d - s`
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

/-- S6.7nl.21C: the physical compact convolution of `D_i h` gains `d - s` derivatives in `H^s`. -/
theorem s67bd_local_convolution_gain (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (r : ℝ) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : Euc d → ℝ, ContDiff ℝ 1 h → Integrable h volume →
      ∀ i : Fin d, HRS.PDE.ToolboxRd.MemSobolev (r - 1) (s67bd_D i h) →
      HRS.PDE.ToolboxRd.MemSobolev (r - 1 + (d : ℝ) - s) (s67bd_local d s h i) ∧
      s67bd_Hnorm (r - 1 + (d : ℝ) - s) (s67bd_local d s h i) ≤
        C * s67bd_Hnorm (r - 1) (s67bd_D i h) := by
  have hθ : ContDiff ℝ ∞ (movb2_theta d) := (movb2_bump d).contDiff
  have hc : HasCompactSupport (movb2_theta d) := (movb2_bump d).hasCompactSupport
  obtain ⟨C, hC, hgain⟩ := HRS.MS.Tc3.tc3_riesz_loc_sobolev_gain hθ hc hs0 hsd
  refine ⟨C, hC.le, fun h _ _ i hD => ?_⟩
  obtain ⟨hmem, hnorm⟩ := hgain (r - 1) (s67bd_D i h) hD
  have hconv : s67bd_local d s h i =
      HRS.Whole.convFun (fun x => movb2_theta d x * rieszKernel d s x) (s67bd_D i h) := by
    funext x
    rfl
  have e : r - 1 + (d : ℝ) - s = (r - 1) + ((d : ℝ) - s) := by ring
  rw [hconv, e]
  refine ⟨hmem, ?_⟩
  unfold s67bd_Hnorm
  refine le_trans (Real.sqrt_le_sqrt hnorm) (le_of_eq ?_)
  rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC.le]

end HRS.MS.BreakdownS67
