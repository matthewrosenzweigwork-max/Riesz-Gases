import HRS.MS.AdjDecay
import HRS.MS.SuppU15
import HRS.MS.SuppU8
import HRS.Whole.Adjoint

/-!
# AD-T: `sharp_all_sub_proof` (supplement S4.14)

`sharp_all_sub_proof : type_of% @HRS.Whole.sharp_all_sub`, obtained from the merged conditional statement
`HRS.MS.SuppU15.sharp_all_sub_of_decay_and_tail_proof` applied to `HRS.MS.AdjDecay.adjoint_decay_proof` (S4.12)
and `HRS.Whole.sharp_tail_bound_proof` (S4.13 at `a = d + 1`).  The `2 * d / (a - 2)` of the sharp tail bound at
`a = d + 1` is `2 * d / (((d : ℝ) + 1) - 2)` (the form in the U15 hypothesis `hST`).  The tie to the frozen
statement is in the same file (`example`).
-/

noncomputable section

namespace HRS.MS.AdjDecay

open HRS.Whole

theorem sharp_all_sub_proof : type_of% @HRS.Whole.sharp_all_sub := by
  intro d hd θ hθ s M Q c T νstar k L Λ K hs hk
  have hk2 : 2 ≤ k := by
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have h1 : (2 : ℝ) < k := by linarith
    have h2 : (2 : ℕ) < k := by exact_mod_cast h1
    omega
  refine HRS.MS.SuppU15.sharp_all_sub_of_decay_and_tail_proof hd θ hθ s M Q c T νstar k L Λ K hs hk
    (adjoint_decay_proof hd θ hθ s M Q c T νstar k hk2 L Λ K) (fun hs0 => ?_)
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ha : (d : ℝ) < (d : ℝ) + 1 ∧ (d : ℝ) + 1 < (d : ℝ) + 2 := ⟨by linarith, by linarith⟩
  exact sharp_tail_bound_proof hd ((d : ℝ) + 1) s k ha hk hs0

end HRS.MS.AdjDecay

example := (@HRS.MS.AdjDecay.sharp_all_sub_proof : type_of% @HRS.Whole.sharp_all_sub)
