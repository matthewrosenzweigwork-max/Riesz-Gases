import HRS.ME.UIPathTightP6
import HRS.ME.UIPath

/-! Tie: `p6_assembly` has exactly the type of the frozen `HRS.ui_path_tight`. -/

example := (@HRS.ME.UIPathTight.p6_assembly : type_of% @HRS.ui_path_tight)
