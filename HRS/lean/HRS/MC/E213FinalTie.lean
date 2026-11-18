import HRS.MC.E213Final
import HRS.Main.HeadlineEdgeworth

/-! Tie: `edgeworth_window_proof` has exactly the type of the frozen statement `HRS.Main.edgeworth_window`. -/

noncomputable section

example : type_of% @HRS.MC.E213Final.edgeworth_window_proof = type_of% @HRS.Main.edgeworth_window := rfl

end
