import HRS.Sections.Sec7Static
import HRS.MC.S7S7f

/-!
# Tie of S7f to the sorried frozen statement `HRS.Sec7.static_field` (NOT root-imported)
-/

noncomputable section

example := (@HRS.MC.Sec7.S7f.static_field_proof : type_of% @HRS.Sec7.static_field)
