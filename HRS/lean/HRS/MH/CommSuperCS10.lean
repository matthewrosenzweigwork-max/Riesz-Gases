import HRS.MH.CommSuperDefs
import HRS.MH.CommSuperCS7
import HRS.MH.CommSuperCS8
import HRS.MH.CommSuperCS9

/-!
# CS10: assembly of the frozen `HRS.Whole.whole_commutator_super` from CS7-CS9
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MH.CommSuper

/-- **CS10** (size S).  The frozen `HRS.Whole.whole_commutator_super`, proved from CS7-CS9. -/
theorem whole_commutator_super_of_concentration_proof :
    type_of% @HRS.Whole.whole_commutator_super := by
  intro d hd s hs0 hsd hsc L
  obtain ⟨C₀, C, hcc⟩ := compact_case_proof hd hs0 hsc hsd
  unfold CompactCase at hcc
  refine ⟨C₀, C, hcc.1, hcc.2.1, ?_⟩
  intro Λ hΛ N hN ρ hρ hρΛ hlog X hX v K hK
  refine ⟨(bdd_integrable_proof hd hs0 hsd hρ hρΛ hlog X hX v K hK).2.2, ?_⟩
  exact truncation_limit_proof hd hs0 hsd (by unfold CompactCase; exact hcc) L Λ hΛ N hN ρ hρ hρΛ hlog X hX v K hK

end HRS.MH.CommSuper
