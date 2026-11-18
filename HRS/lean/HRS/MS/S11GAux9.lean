import HRS.MS.S11GAux1
import HRS.MS.S11GAux7
import HRS.MS.R2S11Aux22

/-!
# S11G: `r2_two_parameter_edgeworth` from `r2_tensor_relaxation` alone

`S11GaussCompare` is proved (`s11g_gaussCompare`); `S11KappaBound` follows from the stationary case `γ = β` of
`r2_tensor_relaxation` (`s11g_kappaBound_of_stationary_relaxation`).  Hence the frozen S11.2 follows from the frozen S11.1
at `γ` and at `γ = β`.
-/

noncomputable section

open HRS.Whole
open HRS (Euc)

namespace HRS.MS.S11G

theorem s11g_two_param_of_relaxation {d : ℕ} (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (a β γ : ℝ) (ha : 0 < a) (hβ : 0 < β) (hγ : 0 ≤ γ) (hγs : 0 < s → 0 < γ) (T : ℝ) (hT : 0 < T)
    (lam : ℝ) (hlam : 0 < lam)
    (h11 : type_of% (r2_tensor_relaxation hd s hs0 hs a β γ ha hβ hγ hγs T hT lam hlam))
    (h11β : type_of% (r2_tensor_relaxation hd s hs0 hs a β β ha hβ hβ.le (fun _ => hβ) T hT lam hlam)) :
    type_of% (r2_two_parameter_edgeworth hd s hs0 hs a β γ ha hβ hγ hγs T hT lam hlam) :=
  HRS.MS.R2S11.s11_two_param_of_h11 hd s hs0 hs a β γ ha hβ hγ hγs T hT lam hlam h11
    (s11g_gaussCompare d s a β γ T lam)
    (s11g_kappaBound_of_stationary_relaxation hd s hs0 hs a β γ ha hβ T hT lam hlam h11β)

end HRS.MS.S11G
