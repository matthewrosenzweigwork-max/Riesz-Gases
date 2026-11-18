import HRS.MS.SA12X3P2
import HRS.MS.SA12V7

/-!
# S.A.12 (SA12X3): the frozen `adjoint_rd` from the proved periodic approximation sequence

`sa12v_adjoint_rd_of_P2` (P4: limit passage P3 and uniqueness adapter) applied to the proved producer P2
`sequence_from_cell_producers`.
-/

set_option autoImplicit false

noncomputable section

namespace HRS.MH.AdjointRd.Phase2SA12Assembly

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

theorem sa12x3_adjoint_rd_from_cells : type_of% @HRS.Whole.AppendixA.adjoint_rd :=
  sa12v_adjoint_rd_of_P2 (fun d hd s hs0 hsd m hm Rg MB Λ ΛV G₀ νbar T χ hχ =>
    sequence_from_cell_producers d hd s hs0 hsd m hm Rg MB Λ ΛV G₀ νbar T χ hχ)

end HRS.MH.AdjointRd.Phase2SA12Assembly
