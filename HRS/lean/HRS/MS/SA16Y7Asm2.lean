import HRS.MS.SA16Y7Asm1
import HRS.MS.SA16Y5Ex3f

/-!
# S.A.16 (SA16Y7) Asm2: the unconditional assembly of the frozen `adjoint_lp`

`sa16y7_adjoint_lp : type_of% @adjoint_lp`.  Case split over `LpCase` and the ranges of `s`
(see `SA16Y7Asm1`; `LpCase.Holds` leaves no gap): `sub` by `sa16y4_adjoint_lp_sub`; `iso`/`hilbert` for
`s < d-1` by SA16Y5, for `s = d-1` by SA16Y6Fin, for `d-1 < s < d` by `sa16y5_adjoint_lp_iso_hi/_hilbert_hi`.
-/

set_option autoImplicit false

noncomputable section

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA

theorem sa16y7_adjoint_lp : type_of% @adjoint_lp :=
  sa16y7_adjoint_lp_of_hi
    (fun {_} hd s hs0 hsd hs1 m hm p _ MB Λ ΛV G₀ νbar T χ hχ =>
      sa16y5_adjoint_lp_iso_hi hd s hs0 hsd hs1 m hm p MB Λ ΛV G₀ νbar T χ hχ)
    (fun {_} hd s hs0 hsd hs1 m hm p _ MB Λ ΛV G₀ νbar T χ hχ =>
      sa16y5_adjoint_lp_hilbert_hi hd s hs0 hsd hs1 m hm p MB Λ ΛV G₀ νbar T χ hχ)

end HRS.Whole.AppendixA.Phase2SA16R
