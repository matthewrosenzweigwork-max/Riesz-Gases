import HRS.MS.SA12X2R36K

/-!
# S.A.12 R36 (SA12X2), part L: jet bound of a regular density (`IsRegularDensityW`)

`IsRegularDensityW r Λ ρ` gives `‖∂^j ρ x‖ ≤ max Λ 0` for all `j ≤ r`, `x`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12

open HRS HRS.Whole

variable {d : ℕ}

theorem sa12x2_density_jet {r : ℕ} {Λ : ℝ} {ρ : Euc d → ℝ} (h : IsRegularDensityW r Λ ρ) :
    ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j ρ x‖ ≤ max Λ 0 := by
  obtain ⟨-, hmem, hsum⟩ := h
  have hle : cbNorm r ρ ≤ max Λ 0 := by
    have h1 : ENNReal.ofReal (cbNorm r ρ) ≤ ENNReal.ofReal Λ := le_trans le_self_add hsum
    have h2 : ENNReal.ofReal Λ ≤ ENNReal.ofReal (max Λ 0) := ENNReal.ofReal_le_ofReal (le_max_left _ _)
    exact (ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).1 (h1.trans h2)
  intro j hj x
  have hbdd := hmem.2 j hj
  have hsingle : ‖iteratedFDeriv ℝ j ρ x‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ j ρ z‖ := le_ciSup hbdd x
  have hsum_le : (⨆ z, ‖iteratedFDeriv ℝ j ρ z‖) ≤ cbNorm r ρ := by
    unfold cbNorm
    exact Finset.single_le_sum (f := fun j' => ⨆ z, ‖iteratedFDeriv ℝ j' ρ z‖)
      (fun j' _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (by omega))
  exact (hsingle.trans hsum_le).trans hle

end HRS.MH.AdjointRd.Phase2SA12
