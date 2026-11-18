import HRS.MS.CritForceAssembly

/-!
# S8.2 T8A B10: the frozen `weighted_critical_forcing`, from the scalar block certificate (B09)
The native assembly `s82_weighted_critical_forcing_of_blocks` proves the exact type of the frozen row from
`S82ScalarBlocks`; B09 (`r26t8a_scalar_blocks`) is the remaining analytic input.  This file takes the certificate as a
hypothesis; the unconditional form `r26t8a_weighted_critical_forcing_final` (B09 plugged in) is in
`R26T8AB10final.lean` once B09 is on the branch.
-/

noncomputable section
set_option autoImplicit false
namespace HRS.MS.R26T8A
open HRS HRS.Whole

theorem r26t8a_weighted_critical_forcing (hB09 : HRS.MS.S82BD.S82ScalarBlocks) :
    type_of% @HRS.Whole.weighted_critical_forcing :=
  HRS.MS.S82BD.s82_weighted_critical_forcing_of_blocks hB09

end HRS.MS.R26T8A

end
