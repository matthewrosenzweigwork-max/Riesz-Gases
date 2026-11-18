import HRS.ME.UnifP8A
import HRS.Main.HeadlineEquilibrium

/-! Tie of the proved `critical_marginal_expansion_unif_proof` to the frozen statement
`HRS.Main.critical_marginal_expansion` (not root-imported: the spec file contains the unproved statement). -/

namespace HRS.ME.Unif

example := (@critical_marginal_expansion_unif_proof : type_of% @HRS.Main.critical_marginal_expansion)

end HRS.ME.Unif
