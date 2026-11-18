import HRS.Main.GFFinal5

/-!
# GF-FINAL: sorry-free proofs of the three frozen statements of Theorem 2.1

`GFFinal1`-`GFFinal5` are copies (prefix `gff_`) of the glue/assembly lemmas of `GFSpec4`-`GFSpec7` that depend on the frozen sorried packets of
`GFSpec1`-`GFSpec3`, with each packet replaced by its relocated proof `HRS.GF.<name>_proof` (`_proof'` for `gf_trace_moment`).  No existing file is changed.
-/

namespace HRS.GeneralSetup

theorem general_fluctuation_proof : type_of% @HRS.GeneralSetup.general_fluctuation :=
  @HRS.GF.gff_general_fluctuation

theorem general_fluctuation_transport_proof : type_of% @HRS.GeneralSetup.general_fluctuation_transport :=
  @HRS.GF.gff_general_fluctuation_transport

theorem general_fluctuation_matrix_proof : type_of% @HRS.GeneralSetup.general_fluctuation_matrix :=
  @HRS.GF.gff_general_fluctuation_matrix

example := (@general_fluctuation_proof : type_of% @HRS.GeneralSetup.general_fluctuation)
example := (@general_fluctuation_transport_proof : type_of% @HRS.GeneralSetup.general_fluctuation_transport)
example := (@general_fluctuation_matrix_proof : type_of% @HRS.GeneralSetup.general_fluctuation_matrix)

end HRS.GeneralSetup
