import HRS.Appendix.CepaFlow
import HRS.MC.CepB2

/-! Tie of `HRS.MC.CepB2.cepa_log_flow_repaired_proof` to the frozen (repaired, CEPA-LOG-FLOW) statement
`HRS.cepa_log_flow`.  This module imports the sorried frozen module `HRS.Appendix.CepaFlow`; it is not for
root import. -/

example := (@HRS.MC.CepB2.cepa_log_flow_repaired_proof : type_of% @HRS.cepa_log_flow)
