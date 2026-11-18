import HRS.MS.S82RR02

/-!
# S8.2 observed-time layer, packet T8A.C15 (native adapter): exact `PinComparison`

The packet statement is literally the merged `Phase2S82.pointwise_pin_comparison` (S82RR02); the Pro route R09-R12, C05-C13 is not needed.
-/

set_option autoImplicit false
noncomputable section

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_pointwise_pin_comparison (d : ℕ) (hd : 2 ≤ d)
    (a beta C0 : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) :
    ∃ C : ℝ, 0 < C ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ h : ℕ → Euc d → ℝ,
      WeakReferenceSetup d a beta rho q h C0 → PinComparison beta rho q h C :=
  Phase2S82.pointwise_pin_comparison d hd a beta C0 ha hbeta q hq

end HRS.MS.R26T8A
