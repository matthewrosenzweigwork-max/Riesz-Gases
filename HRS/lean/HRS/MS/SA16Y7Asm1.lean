import HRS.MS.SA16Y6Fin
import HRS.MS.SA16Y5Ex2
import HRS.MS.SA16Y4Ex2

/-!
# S.A.16 (SA16Y7) assembly of the frozen `adjoint_lp`

Case split of `adjoint_lp` by `κc` and the range of `s`:
* `sub` (`0 ≤ s ≤ d-2`, `p(s+1) > d`): `sa16y4_adjoint_lp_sub` (covers every `s`; the case is vacuous otherwise);
* `iso`, `hilbert` (`d-2 < s < d`): `s < d-1`: `sa16y5_adjoint_lp_iso/_hilbert`; `s = d-1`: `sa16y6_adjoint_lp_iso/_hilbert`;
  `d-1 < s < d`: hypotheses `Sa16y7HiIso`, `Sa16y7HiHilbert` (to be supplied by the d-1<s<d chain, SA16Y5 B9).
Nothing else is needed: `LpCase.Holds` for `iso`/`hilbert` forces `d-2 < s`, and for `sub` the whole range is covered.
-/

set_option autoImplicit false

noncomputable section

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA

/-- The statement the `d-1<s<d` chain has to prove for `LpCase.iso`. -/
def Sa16y7HiIso : Prop :=
  ∀ {d : ℕ} (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (_hs1 : (d : ℝ) - 1 < s) (m : ℕ) (hm : 1 ≤ m)
    (p : ℝ) [Fact (2 ≤ p)] (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ),
    type_of% (adjoint_lp hd s hs0 hsd m hm p LpCase.iso MB Λ ΛV G₀ νbar T χ hχ)

/-- The statement the `d-1<s<d` chain has to prove for `LpCase.hilbert`. -/
def Sa16y7HiHilbert : Prop :=
  ∀ {d : ℕ} (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (_hs1 : (d : ℝ) - 1 < s) (m : ℕ) (hm : 1 ≤ m)
    (p : ℝ) [Fact (2 ≤ p)] (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ),
    type_of% (adjoint_lp hd s hs0 hsd m hm p LpCase.hilbert MB Λ ΛV G₀ νbar T χ hχ)

theorem sa16y7_adjoint_lp_of_hi (hiso : Sa16y7HiIso) (hhil : Sa16y7HiHilbert) :
    type_of% @adjoint_lp := by
  intro d hd s hs0 hsd m hm p _ κc MB Λ ΛV G₀ νbar T χ hχ
  cases κc with
  | sub => exact sa16y4_adjoint_lp_sub hd s hs0 hsd m hm p MB Λ ΛV G₀ νbar T χ hχ
  | iso =>
    rcases lt_trichotomy s ((d : ℝ) - 1) with h | h | h
    · exact sa16y5_adjoint_lp_iso hd s hs0 hsd h m hm p MB Λ ΛV G₀ νbar T χ hχ
    · exact sa16y6_adjoint_lp_iso hd s hs0 hsd h m hm p MB Λ ΛV G₀ νbar T χ hχ
    · exact hiso hd s hs0 hsd h m hm p MB Λ ΛV G₀ νbar T χ hχ
  | hilbert =>
    rcases lt_trichotomy s ((d : ℝ) - 1) with h | h | h
    · exact sa16y5_adjoint_lp_hilbert hd s hs0 hsd h m hm p MB Λ ΛV G₀ νbar T χ hχ
    · exact sa16y6_adjoint_lp_hilbert hd s hs0 hsd h m hm p MB Λ ΛV G₀ νbar T χ hχ
    · exact hhil hd s hs0 hsd h m hm p MB Λ ΛV G₀ νbar T χ hχ

end HRS.Whole.AppendixA.Phase2SA16R
