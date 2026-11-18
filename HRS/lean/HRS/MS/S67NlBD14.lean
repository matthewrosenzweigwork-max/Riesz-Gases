import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovForceAux6
import HRS.MS.S67NlBD03
import HRS.MS.S67NlBD14A
import HRS.MS.S67NlBD14B
import HRS.MS.S67NlBD14C
import HRS.MS.S67NlBD14D

/-!
# S6.7 nonlinear breakdown, packet 14: physical cancellation force split

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4221-4245, 4751-4763, row
`S:W:lem:r2mov-global-adjoint` (nonlinear part). Owned definition: `s67bd_F`. The theorem
`s67bd_force_split` is the assembly of the near-integrability (14A), tail/local integrability (14B),
cutoff-correction integration by parts (14C) and algebraic recombination (14D) packets.
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

def s67bd_F (d : ℕ) (s : ℝ) (ρ₀ v : Euc d → ℝ) : Euc d → Euc d :=
  movForce d s (fun x => Real.sqrt (ρ₀ x) * v x)

theorem s67bd_force_split (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (h : Euc d → ℝ) (hh : ContDiff ℝ 1 h) (hI : Integrable h volume) :
    ∀ x : Euc d,
      Integrable (fun y => if ‖x - y‖ ≤ 1 / 4 then
        (h y - h x) • rieszKernelGrad d s (x - y) else
        h y • rieszKernelGrad d s (x - y)) volume ∧
      ∀ i : Fin d,
        Integrable (fun y => movb2_gloc d s (x - y) * s67bd_D i h y) volume ∧
        Integrable (fun y => movb2_kfar d s i (x - y) * h y) volume ∧
        movForce d s h x i = s67bd_local d s h i x + s67bd_far d s h i x := by
  intro x
  have hn := s67bd_near_integrable hd hs0 hsd h hh x
  have ht := s67bd_tail_local_integrable hd hs0 hsd h hh hI x
  exact s67bd_force_recombine hd hs0 hsd h x hn ht.1 ht.2
    (fun i => s67bd_compact_force_ibp hd hs0 hsd h hh hI x i hn (ht.2 i).1)

end HRS.MS.BreakdownS67
