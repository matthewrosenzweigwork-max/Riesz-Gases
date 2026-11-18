import HRS.MS.SA16Y6CEx2

/-!
# S.A.16 (SA16Y6) Fin: `adjoint_lp` for `LpCase.iso` and `LpCase.hilbert` at the critical exponent `s = d-1`

The statements are exactly `type_of% (adjoint_lp hd s hs0 hsd m hm p κc MB Λ ΛV G₀ νbar T χ hχ)` for `κc := LpCase.iso`,
`LpCase.hilbert`, under the extra hypothesis `hs1 : s = d - 1` (including `d = 1`, `s = 0`).
-/

set_option autoImplicit false

noncomputable section

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

theorem sa16y6_adjoint_lp_iso (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : s = (d : ℝ) - 1)
    (m : ℕ) (hm : 1 ≤ m) (p : ℝ) [Fact (2 ≤ p)] (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    type_of% (adjoint_lp hd s hs0 hsd m hm p LpCase.iso MB Λ ΛV G₀ νbar T χ hχ) :=
  sa16y6c_adjoint_lp_iso hd s hs0 hsd hs1 m hm p MB Λ ΛV G₀ νbar T χ hχ

theorem sa16y6_adjoint_lp_hilbert (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : s = (d : ℝ) - 1)
    (m : ℕ) (hm : 1 ≤ m) (p : ℝ) [Fact (2 ≤ p)] (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    type_of% (adjoint_lp hd s hs0 hsd m hm p LpCase.hilbert MB Λ ΛV G₀ νbar T χ hχ) :=
  sa16y6c_adjoint_lp_hilbert hd s hs0 hsd hs1 m hm p MB Λ ΛV G₀ νbar T χ hχ

end HRS.Whole.AppendixA.Phase2SA16R
