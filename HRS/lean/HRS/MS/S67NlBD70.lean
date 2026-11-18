import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie

/-!
# S6.7nl.70: nonlinear witnesses below the analytic radius, with the changed class rate
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

/-- S6.7nl.70: nonlinear witnesses below any prescribed radius, with the positive class rate. -/
theorem s67bd_shrink_nonlinear (H : Mov2dTh d s β q ρ₀)
    (j' m : ℕ) (hj' : 1 ≤ j') (hm : (d : ℝ) / 2 + j' + 6 < m)
    (Rstar : ℝ) (hRstar : 0 < Rstar) :
    ∃ εstar r c' C' : ℝ,
      0 < εstar ∧ 0 < r ∧ 0 < c' ∧ 0 < C' ∧ r ≤ Rstar ∧
      MovNonlinearConclusion d s q β ρ₀ j' m εstar r c' c' C' := by
  obtain ⟨εs, r0, c₀, c, C, hεs, hr0, -, hc, hC, hconc, -⟩ :=
    HRS.MS.Mov63.mov_nonlinear_proof H.hd H.hs0 H.hsd β q H.hβ H.hq j' hj' m hm ρ₀ H.hρ
  have hrnew : 0 < min r0 Rstar := lt_min hr0 hRstar
  obtain ⟨ε', hε', -, hconc'⟩ :=
    HRS.MS.MovAdj.s67_shrink hconc hC hεs hrnew (min_le_left _ _)
  exact ⟨ε', min r0 Rstar, c, C, hε', hrnew, hc, hC, min_le_right _ _, hconc'⟩

end HRS.MS.BreakdownS67
