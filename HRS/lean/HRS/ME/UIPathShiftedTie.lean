import HRS.ME.UIPathShiftedP6
import HRS.ME.UIPath

/-! Tie of `HRS.ME.UIPathShifted.p_assembly` to the frozen `HRS.ui_path_shifted`. -/

namespace HRS.ME.UIPathShifted

variable {d : ℕ}

/-- The assembly has exactly the type of the frozen `HRS.ui_path_shifted`. -/
example := (@p_assembly d : type_of% (@HRS.ui_path_shifted d))

end HRS.ME.UIPathShifted
