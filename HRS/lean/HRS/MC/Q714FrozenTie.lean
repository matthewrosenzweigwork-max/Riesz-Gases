import HRS.Sections.Sec7Quench
import HRS.MC.Q714AsmFrozen

/-! Ties of `HRS.MC.Q714.Asm.critical_edgeworth_proof` and `critical_edgeworth_equal_temperature_proof` to the frozen statements
`HRS.Sec7.critical_edgeworth` and `HRS.Sec7.critical_edgeworth_equal_temperature` (Corollary 7.14).  Unlike `Q714AsmTie.lean`,
this module imports no sorried file of ours (`HRS.Sections.Sec7Quench` is the frozen module that contains the statements), so it
can be a root import. -/

example := (@HRS.MC.Q714.Asm.critical_edgeworth_proof : type_of% @HRS.Sec7.critical_edgeworth)

example := (@HRS.MC.Q714.Asm.critical_edgeworth_equal_temperature_proof :
  type_of% @HRS.Sec7.critical_edgeworth_equal_temperature)
