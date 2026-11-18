import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.Whole.MovingDyn
import HRS.MS.S67NlBD69
import HRS.MS.S67NlBD70

/-!
# S6.7nl.T01: the nonlinear part of the moving global adjoint estimate
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.
Term-mode assembly: the uniform gradient estimate (packet 69) fixes a radius and rate, the nonlinear
shrinking theorem (packet 70) provides the class witnesses below that radius, and the 69 estimate is
specialized to each supplied class member.  The frozen theorem is used for its type only.
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

theorem mov_global_adjoint_nonlinear_proof :
    type_of% @HRS.Whole.mov_global_adjoint_nonlinear :=
  fun {d : ℕ} {s : ℝ} hd hs0 hsd β q hβ hq ρ₀ hρ j M hM j' m hj' hm hmM =>
    let H : Mov2dTh d s β q ρ₀ := ⟨hd, hs0, hsd, hβ, hq, hρ⟩
    match s67bd_uniform_gradient H j M hM j' m hj' hm hmM with
    | ⟨Rstar, C, c, hRstar, hC, hc, hbound⟩ =>
      match s67bd_shrink_nonlinear H j' m hj' hm Rstar hRstar with
      | ⟨εstar, r, c', C', hε, hr, hc', hC', hrR, hnonlinear⟩ =>
        ⟨εstar, r, c', c', C', hε, hr, hc', hc', hC', hnonlinear,
          C, c, hc, fun f0 _hf0 ρ hρsmall T φ f hT hf hφ hφosc =>
            hbound r c' (le_of_lt hr) hrR (le_of_lt hc') f0 ρ hρsmall T φ f hT hf hφ hφosc⟩

example := (@mov_global_adjoint_nonlinear_proof : type_of% @HRS.Whole.mov_global_adjoint_nonlinear)

end HRS.MS.BreakdownS67
