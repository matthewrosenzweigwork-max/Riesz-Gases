import HRS.MS.SA12X3Final
import HRS.MS.SA12CompB9

/-!
# S.A.12 (SA12X4): the frozen clause (a) `adjoint_rd_classical`

The proved assembly B9 `adjoint_rd_classical_of_existence` applied to the proved frozen `adjoint_rd`
(`sa12x3_adjoint_rd_from_cells`).
-/

set_option autoImplicit false

noncomputable section

namespace HRS.MH.AdjointRd.Phase2SA12X4

theorem sa12x4_adjoint_rd_classical_tie : type_of% @HRS.Whole.AppendixA.adjoint_rd_classical :=
  HRS.MH.AdjointRd.Phase2SA12Companions.adjoint_rd_classical_of_existence
    HRS.MH.AdjointRd.Phase2SA12Assembly.sa12x3_adjoint_rd_from_cells

end HRS.MH.AdjointRd.Phase2SA12X4
