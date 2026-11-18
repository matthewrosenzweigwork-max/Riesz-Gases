import HRS.MS.SA12X5N0
import HRS.MS.SA12X5Defs

/-!
# S.A.12 X5 P0: `PerData` is monotone in the level
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

theorem sa12x5_perData_mono {s : ℝ} {m : ℕ} {MB Λ ΛV νbar Cb T L : ℝ} {γ : Euc d → ℝ}
    {M : Matrix (Fin d) (Fin d) ℝ} {ν : ℝ} {μ : ℝ → Euc d → ℝ} {V : Euc d → ℝ} {b : ℝ → Euc d → Euc d}
    (h : PerData s (m + 2) MB Λ ΛV νbar Cb T L γ M ν μ V b) : PerData s m MB Λ ΛV νbar Cb T L γ M ν μ V b where
  toPerSmooth := h.toPerSmooth
  hM := h.hM
  hν' := h.hν'
  μ_bdd := fun τ hτ j hj x => h.μ_bdd τ hτ j (by omega) x
  μ_decay := fun τ hτ j hj x => h.μ_decay τ hτ j (by omega) x
  V_bdd := fun j h2 hj x => h.V_bdd j h2 (by omega) x
  b_drift := sa12x5_advDrift_mono (sa12x5_advDrift_mono h.b_drift)

end HRS.MH.AdjointRd.Phase2SA12X5
