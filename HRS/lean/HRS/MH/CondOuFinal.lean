import HRS.Main.HeadlineEquilibrium
import HRS.MH.CondOuA
import HRS.MH.CondOuB
import HRS.MH.CondOuP8

noncomputable section

namespace HRS.MH.CondOuFinal

/-- The frozen `HRS.Main.conditioned_ou`: (a) `conditioned_ou_prob_proof`, (b) `conditioned_ou_third_cumulant_proof`,
(c) `p8_assembly`. -/
theorem conditioned_ou_proof : type_of% @HRS.Main.conditioned_ou := by
  intro d hd s hs0 hsd β hβ k hk
  exact ⟨HRS.MH.CondOuP.conditioned_ou_prob_proof hd hs0 hsd β hβ k hk,
    HRS.MH.CondOuP.conditioned_ou_third_cumulant_proof hd hs0 hsd β hβ k hk,
    HRS.MH.CondOuPackets.p8_assembly hd hs0 hsd β hβ k hk⟩

example := (@conditioned_ou_proof : type_of% @HRS.Main.conditioned_ou)

end HRS.MH.CondOuFinal

end
