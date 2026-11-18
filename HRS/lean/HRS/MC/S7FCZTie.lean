import HRS.Sections.Sec7Fields
import HRS.MC.S7FCZ

/-! Tie: `S7FCZ.field_chaos_proof` has exactly the statement of the frozen `HRS.Sec7.field_chaos`. -/

noncomputable section

example := (@HRS.MC.Sec7.S7FCZ.field_chaos_proof : type_of% @HRS.Sec7.field_chaos)

end
