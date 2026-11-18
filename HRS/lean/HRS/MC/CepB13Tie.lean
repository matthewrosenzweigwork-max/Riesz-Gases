import HRS.MC.CepB13
import HRS.Appendix.CepaFlow

/-! Tie: `HRS.MC.CepB13.cepa_noncollision_iff_threshold_proof` has the type of the frozen statement
`HRS.cepa_noncollision_iff_threshold` (`HRS/Appendix/CepaFlow.lean`). -/

example := (@HRS.MC.CepB13.cepa_noncollision_iff_threshold_proof :
  type_of% @HRS.cepa_noncollision_iff_threshold)
