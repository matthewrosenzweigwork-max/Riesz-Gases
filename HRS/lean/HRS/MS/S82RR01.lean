import HRS.MS.S82RA6
import HRS.MS.S82RB4

/-!
# S8.2 R01: assembly `weak_reference_native` (R01A + R01B), as in the Pro skeleton
-/

set_option autoImplicit false
noncomputable section

namespace HRS.MS.Phase2S82
open HRS HRS.Whole

/-- R01 assembly (R01A then R01B). -/
theorem weak_reference_native (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) :
    ∃ C : ℝ, ∃ q : Euc d → ℝ, 0 < C ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∃ h : ℕ → Euc d → ℝ,
        WeakReferenceSetup d a beta rho q h C := by
  obtain ⟨C0, q, hC0, hbase⟩ := calibrated_reference_native d hd a beta ha hbeta
  obtain ⟨C, hC, hpins⟩ := finite_pin_reference_adapter d hd a beta C0 ha hbeta q
  refine ⟨C, q, hC, ?_⟩
  intro rho hrho
  obtain ⟨h, hh⟩ := hbase rho hrho
  exact ⟨h, hpins rho hrho h hh⟩

end HRS.MS.Phase2S82

end
