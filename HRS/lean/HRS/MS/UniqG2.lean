import HRS.MS.UniqG2d
import HRS.MS.UniqG2fcB

/-!
# S.A.33: `uloc_uniqueness`

`uloc_uniqueness_proof` has exactly the binders and conclusion of the frozen
`HRS.Whole.AppendixALemmas.uloc_uniqueness`; it is `uloc_uniqueness_core` (UniqG2d) with the
`R3` decay theorem `g2f_decay` (UniqG2fcB) supplied for the extra hypothesis. The final `example`
checks that the two statements agree.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqG2

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqG2d HRS.MS.UniqG2fc

variable {d : ℕ}

theorem uloc_uniqueness_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (Rg : PDE.Regime) (T Λ ΛV G₀ MB νbar ν₀ : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (M : Matrix (Fin d) (Fin d) ℝ) (V : Euc d → ℝ) (invβ : ℝ) (ρ : ℝ → Euc d → ℝ)
    (hM : PDE.MatBound MB M) (hV : VHypRd (m + 3) ΛV G₀ V) (hν : 0 ≤ invβ ∧ invβ ≤ νbar)
    (hρ : CoeffHypRd s m Λ T ρ)
    (hRg : RdRegimeHolds Rg d s M invβ ν₀) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    (z : ℝ → Euc d → ℝ) (hzb : IsUlBounded χ 1 t z)
    (hz : IsForwardDistSolutionW (⟨s, M, V, invβ⟩ : WholeDyn d) ρ t z) :
    ∀ τ ∈ Set.Icc (0 : ℝ) t, z τ =ᵐ[volume] 0 := by
  refine uloc_uniqueness_core hd s hs0 hsd m hm Rg T Λ ΛV G₀ MB νbar ν₀ χ hχ M V invβ ρ hM hV hν hρ
    hRg t ht z hzb hz ?_
  intro hR3 Cb K χh Ψ hχc hb hΨ hF B hB hzu
  subst hR3
  exact g2f_decay hd (D := (⟨s, M, V, invβ⟩ : WholeDyn d)) hs0 hsd m hm MB Λ ΛV G₀ hM hV hρ ht hχ hν.1
    hb hF hz hB hzu hχc hΨ ν₀ hRg

example := (@uloc_uniqueness_proof : type_of% @HRS.Whole.AppendixALemmas.uloc_uniqueness)

end HRS.MS.UniqG2
