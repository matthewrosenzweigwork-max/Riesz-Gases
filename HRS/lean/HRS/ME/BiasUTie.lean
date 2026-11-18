import HRS.ME.BiasUC
import HRS.Main.HeadlineEquilibrium

/-! Tie of the proved `critical_bias_constants_unif` to the frozen statement
`HRS.Main.critical_bias_constants` (not root-imported: the frozen file contains `sorry`). -/

namespace HRS.ME.Bias

example := (@critical_bias_constants_unif : type_of% @HRS.Main.critical_bias_constants)

end HRS.ME.Bias
