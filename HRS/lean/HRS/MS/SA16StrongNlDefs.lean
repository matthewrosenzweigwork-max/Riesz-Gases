import HRS.MS.SA16StrongDefs

/-!
# S.A.16 strong-limit cores: `nlCut` (literal copy)

Literal copy of `nlCut` from `skeleton/cores/SA16-STRONG-LIMIT.lean` (the other definitions of that skeleton
are in `SA16StrongDefs`).  Later workers needing `nlCut` must import this file, not redeclare it.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16
open HRS HRS.Whole HRS.Whole.AppendixA

/-- Leibniz-first regularization for M=-lam I+A, A skew.
Here `c` is the positive coefficient in -Delta g = c Lambda^theta,
and `gamma = -q09_c s` is 1 at s=0 and s otherwise.
The plus sign before the odd term is forced by grad g=-gamma*K_odd.
This raw cutoff is for consistency only; an energy-compatible cutoff
requires the Coulomb-core correction of SA16-COMPATIBLE-CUTOFF. -/
def nlCut (d : ℕ) (θ δ lam c gamma : ℝ) (M : Matrix (Fin d) (Fin d) ℝ)
    (μ u : Euc d → ℝ) (x : Euc d) : ℝ :=
  lam*c*fracCut d θ δ (fun y => μ y*u y) x +
    gamma * ∑ i : Fin d, ∑ j : Fin d, M j i *
      oddCut d θ δ i
        (fun y => partialDeriv (fun _ : Fin 1 => j) μ y * u y) x

end HRS.Whole.AppendixA.Phase2SA16
