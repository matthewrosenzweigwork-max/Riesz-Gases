import HRS.MS.SA12DE8F
import HRS.MS.SA12C36

/-!
# S.A.12(c), packet E7.08 (worker S82Z2), part G: the unconditional tie of `adjoint_rd_sobolev`

The periodic box energy statement `Sa12BoxPeriodicStmt` of part C is exactly `sa12c_periodic_box_energy_uloc` (`SA12C36`, E7.03-E7.06),
so `sa12de8_adjoint_rd_sobolev_of_box` gives `type_of% @HRS.Whole.AppendixA.adjoint_rd_sobolev` with no hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace HRS.MS.SA12DE8

open HRS HRS.Whole HRS.Whole.AppendixA

theorem sa12de8_box_periodic : Sa12BoxPeriodicStmt :=
  fun _d hd s hs0 hsd hs1 m hm Rg MB Λ ΛV νbar Cb T χ hχ =>
    HRS.MH.AdjointRd.Phase2SA12C.sa12c_periodic_box_energy_uloc hd s hs0 hsd hs1 m hm Rg MB Λ ΛV νbar Cb T χ hχ

/-- **S.A.12(c)** `adjoint_rd_sobolev`, tied to the frozen statement. -/
theorem sa12de8_adjoint_rd_sobolev : type_of% @HRS.Whole.AppendixA.adjoint_rd_sobolev :=
  sa12de8_adjoint_rd_sobolev_of_box sa12de8_box_periodic

end HRS.MS.SA12DE8
