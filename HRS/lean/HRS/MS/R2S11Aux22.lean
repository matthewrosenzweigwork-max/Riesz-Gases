import HRS.MS.R2S11Aux21

/-!
# S11.2: `r2_two_parameter_edgeworth` from S11.1, the Banach Gaussian comparison and the norm bound of `κ_β`

`s11_two_param_of_h11`: the frozen statement (all parts (a), (b), (c)) from
`h11 = type_of% (r2_tensor_relaxation ..)`, `hG : S11GaussCompare ..` and `hK : S11KappaBound ..`.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MS.R2S11

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s11_two_param_of_h11 (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (a β γ : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (hγ : 0 ≤ γ) (hγs : 0 < s → 0 < γ) (T : ℝ) (hT : 0 < T) (lam : ℝ)
    (hlam : 0 < lam)
    (h11 : type_of% (r2_tensor_relaxation hd s hs0 hs a β γ ha hβ hγ hγs T hT lam hlam))
    (hG : S11GaussCompare d s a β γ T lam) (hK : S11KappaBound d s a β γ T lam) :
    type_of% (r2_two_parameter_edgeworth hd s hs0 hs a β γ ha hβ hγ hγs T hT lam hlam) :=
  s11_two_param_of_a hd s hs0 hs a β γ ha hβ hγ hγs T hT lam hlam
    (s11_partA_of_h11 hd s hs0 hs a β γ ha hβ hγ hγs T hT lam hlam h11 hG hK)

end HRS.MS.R2S11
