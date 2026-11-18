import HRS.Whole.Basic
import HRS.MS.Canon

/-!
# SUPP-U13: the frozen statement `HRS.Whole.canonicalGibbs_eq_modulatedGibbs`

The frozen statement (`HRS/Whole/Basic.lean`, sorried, not edited) is proved here in the
`type_of%` form.  The proof is the fully proved `HRS.MS.Canon.canonicalGibbs_eq_modulatedGibbs_proof`
(`HRS/MS/Canon.lean`, MS-CANON, already on this branch): it writes `ρ` as the thermal density
`exp(-β(V + g*μ)) / Z`, uses `g(-x) = g(x)` to rewrite `N F_N` as `N⁻¹ ∑_{i<j} g - ∑_i g*μ(x_i) + (N/2) E`,
and so `∏ ρ(x_i) exp(-βN F_N) = Z^{-N} exp(-(βN/2) E) exp(-β H_N)` pointwise; both normalisers then
differ by the same positive constant.
-/

namespace HRS.MS.SuppU13

theorem canonicalGibbs_eq_modulatedGibbs_proof :
    type_of% @HRS.Whole.canonicalGibbs_eq_modulatedGibbs :=
  HRS.MS.Canon.canonicalGibbs_eq_modulatedGibbs_proof

end HRS.MS.SuppU13
