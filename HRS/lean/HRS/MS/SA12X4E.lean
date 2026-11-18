import HRS.MS.SA12X4P2
import HRS.MS.SA12CompB11

/-!
# S.A.12 (SA12X4): the frozen clause (e) `adjoint_rd_weighted`

The proved assembly B11 `adjoint_rd_weighted_of_sequence` applied to the weighted periodic approximation sequence
`sa12x4_weighted_sequence` (B6).
-/

set_option autoImplicit false

noncomputable section

namespace HRS.MH.AdjointRd.Phase2SA12X4

theorem sa12x4_adjoint_rd_weighted_tie : type_of% @HRS.Whole.AppendixA.adjoint_rd_weighted :=
  HRS.MH.AdjointRd.Phase2SA12Companions.adjoint_rd_weighted_of_sequence
    HRS.MH.AdjointRd.Phase2SA12X4Seq.sa12x4_weighted_sequence

end HRS.MH.AdjointRd.Phase2SA12X4
