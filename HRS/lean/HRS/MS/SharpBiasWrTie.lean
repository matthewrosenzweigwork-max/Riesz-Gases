import HRS.MS.SharpBias
import HRS.MS.SuppU12
import HRS.Whole.Bias

/-!
# S77: `HRS.Whole.weighted_remainder` (S7.7) from `sharp_bias`

`weighted_remainder_proof : type_of% @HRS.Whole.weighted_remainder` is obtained by instantiating the
conditional `HRS.MS.SuppN.weighted_remainder_of_sharp_bias_proof` (SuppU12) with the hypothesis `hSB`
supplied by `HRS.Whole.S71.sharp_bias_proof` (S7.1).  The hypotheses of the two frozen theorems
(`d, s, β, M, Λ`, density bounds, `N ≥ 1`) match exactly; no statement is adjusted.
-/

noncomputable section

namespace HRS.Whole.S77

/-- **Corollary S7.7** (`HRS.Whole.weighted_remainder`). -/
theorem weighted_remainder_proof : type_of% @HRS.Whole.weighted_remainder := by
  intro d s hd hs hsd β M Λ hβ
  exact HRS.MS.SuppN.weighted_remainder_of_sharp_bias_proof hd hs hsd β M Λ hβ
    (HRS.Whole.S71.sharp_bias_proof hd hs hsd β M Λ hβ)

example := (@weighted_remainder_proof : type_of% @HRS.Whole.weighted_remainder)

end HRS.Whole.S77
