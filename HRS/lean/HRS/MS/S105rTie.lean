import HRS.MS.S105rReg2
import HRS.MS.S104bNL10
import HRS.MS.S104bNL11

/-!
# S10.5 (nonlinear), packet S105R-3: the ties of S10.4 / S10.5 with `S105nReg` discharged

`S105rTermReg`: the one remaining analytic input of S10.3 type (`S104bTermRegGen` for small `ε_*`).
`s105r_general_initial_of_orbits`: `type_of% @HRS.Whole.r2_window_general_initial` from `r2_window_orbits` (S10.3) and `S105rTermReg` only.
`s105r_errors_of_orbits`: `type_of% @HRS.Whole.r2_window_errors` from the same two inputs.
-/

noncomputable section

namespace HRS.MS.S105r

open HRS HRS.Whole HRS.MS.S104b HRS.MS.R2WinErr

/-- `S104bTermRegGen` (general-initial-time terminal-time regularity of the nonlinear adjoint orbit) for small `ε_*`, in the form used by
the ties of S104b. -/
def S105rTermReg : Prop :=
  ∀ {d : ℕ}, 2 ≤ d → ∀ (s a β c₁ C₁ : ℝ), 0 ≤ s → s < d → 0 < a → 0 < β → ∃ εn : ℝ, 0 < εn ∧
    ∀ εstar : ℝ, εstar ≤ εn → ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ →
      S104bTermRegGen d s a β ρβ εstar c₁ C₁

theorem s105r_general_initial_of_orbits (h103 : type_of% @HRS.Whole.r2_window_orbits) (hTR : S105rTermReg) :
    type_of% @HRS.Whole.r2_window_general_initial :=
  s104b_general_initial_of_inputs h103 hTR s105r_hReg

theorem s105r_errors_of_orbits (h103 : type_of% @HRS.Whole.r2_window_orbits) (hTR : S105rTermReg) :
    type_of% @HRS.Whole.r2_window_errors :=
  s104b_errors_of_inputs h103 hTR

end HRS.MS.S105r
