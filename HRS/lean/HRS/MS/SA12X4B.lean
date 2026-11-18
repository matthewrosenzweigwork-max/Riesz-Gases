import HRS.MS.SA12X3Final
import HRS.MS.SA12CompB10

/-!
# S.A.12 (SA12X4): the frozen clause (b) `adjoint_rd_planewave`

The proved assembly B10 `adjoint_rd_planewave_of_existence` applied to the proved frozen `adjoint_rd`
(`sa12x3_adjoint_rd_from_cells`).
-/

set_option autoImplicit false

noncomputable section

namespace HRS.MH.AdjointRd.Phase2SA12X4

theorem sa12x4_adjoint_rd_planewave_tie : type_of% @HRS.Whole.AppendixA.adjoint_rd_planewave :=
  HRS.MH.AdjointRd.Phase2SA12Companions.adjoint_rd_planewave_of_existence
    HRS.MH.AdjointRd.Phase2SA12Assembly.sa12x3_adjoint_rd_from_cells

end HRS.MH.AdjointRd.Phase2SA12X4
