import HRS.MS.S82RA6

/-!
# S8.2 observed-time layer, packet T8A.R07: native calibrated reference for every `N`
The merged main tree already proves this exact statement as `Phase2S82.calibrated_reference_native` (S82RA6), by a route
different from the packet's R01-R06 chain; this file is the packet-named adapter.
-/

set_option autoImplicit false
noncomputable section

namespace HRS.MS.R26T8A
open HRS.MS.Phase2S82

theorem r26t8a_calibrated_reference_native (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) :
    ∃ C : ℝ, ∃ q : Euc d → ℝ, 0 < C ∧ ∀ rho : Euc d → ℝ,
      HRS.Whole.IsThermalEquilibrium d (criticalS d) a beta rho →
      ∃ h : ℕ → Euc d → ℝ,
        CalibratedReferenceData d a beta rho q h C :=
  calibrated_reference_native d hd a beta ha hbeta

end HRS.MS.R26T8A
