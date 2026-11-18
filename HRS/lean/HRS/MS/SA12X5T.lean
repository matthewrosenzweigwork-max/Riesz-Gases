import HRS.MS.SA12X5S6

/-!
# S.A.12 X5 T: tie for `adjoint_rd_stability`
-/

set_option autoImplicit false

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS.MH.AdjointRd.Phase2SA12Stability

theorem sa12x5_adjoint_rd_stability_tie : type_of% @HRS.Whole.AppendixA.adjoint_rd_stability :=
  adjoint_rd_stability_of_sequence sa12x5_paired_approx_seq

end HRS.MH.AdjointRd.Phase2SA12X5
