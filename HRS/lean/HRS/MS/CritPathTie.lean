import HRS.MS.ShiftFldCond
import HRS.MS.WsStatFinal

/-!
# S79: the frozen `critical_path_limit` (S7.9, critical path row)

`critical_path_limit_of_S21` (ShiftFldCond) applied to the proved S2.1(i) `whole_space_stationary_proof` (WsStatFinal).
-/

noncomputable section

namespace HRS.Whole.S79

theorem critical_path_limit_proof : type_of% @HRS.Whole.critical_path_limit :=
  critical_path_limit_of_S21 HRS.MS.S21.whole_space_stationary_proof

example := (@critical_path_limit_proof : type_of% @HRS.Whole.critical_path_limit)

end HRS.Whole.S79
