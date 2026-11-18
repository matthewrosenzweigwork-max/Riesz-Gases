import HRS.Sections.Sec7Static
import HRS.MC.S7S16f

/-!
# Tie of S16f to the sorried frozen statement `HRS.Sec7.slow_correction` (NOT root-imported)
-/

noncomputable section

example := (@HRS.MC.Sec7.S16f.slow_correction_proof : type_of% @HRS.Sec7.slow_correction)
