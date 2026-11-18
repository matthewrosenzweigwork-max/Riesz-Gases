import HRS.Sections.Sec7Fields
import HRS.MC.S7UCZ
import HRS.MC.S7UCZ2

/-! Tie of `HRS.MC.Sec7.S7UCZ.s7_UC_uniform_chaos_proof` to the frozen statement `HRS.Sec7.uniform_chaos` (Proposition 7.9).  Unlike
`S7UCZTie.lean`, this module imports no sorried file of ours (`HRS.Sections.Sec7Fields` is the frozen module that contains the
statement), so it can be a root import. -/

noncomputable section

example := (@HRS.MC.Sec7.S7UCZ.s7_UC_uniform_chaos_proof : type_of% @HRS.Sec7.uniform_chaos)

end
