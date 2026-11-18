import HRS.MS.S116P01
import HRS.MS.S104bOrb1

/-!
# S11.6 packet P02 (`R26-T8B.P02`): terminal-time continuity at the base oscillator index

Prefix `s116_`, namespace `HRS.MS.S116`.  From `S104bTermRegGen` (the difference-quotient clause at `a' = 0`, `r = 0`, `j = 0`, evaluated at the point `x`) and
`s116_continuous_of_quotient`: `t ↦ U(0,t) φ_α(x)` (`φ_α = oscTestFun (wholeSpaceIndex d) α`) is continuous on `[0, T]`.
-/

set_option autoImplicit false

noncomputable section

namespace HRS.MS.S116

open HRS HRS.Whole HRS.MS.R2WinErr HRS.MS.R2WinOrbNL

theorem s116_base_continuity {d : ℕ} {a β εstar c₁ C₁ : ℝ}
    {ρβ : Euc d → ℝ} (hR : HRS.MS.R2WinErr.S104bTermRegGen d 0 a β ρβ εstar c₁ C₁)
    (ε : ℝ) (ψ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ)
    (hadm : IsAdmissiblePerturbation ρβ εstar ε ψ)
    (hres : IsResultingSolution d 0 a β ρβ εstar ε ψ c₁ C₁ ρ)
    (T : ℝ) (hT : 0 ≤ T) (α : MultiIndex d) (x : Euc d) :
    ContinuousOn (fun t => propagatorW ((quadraticGradientDyn d 0 a β).coeff ρ) 0 t
      (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) x) (Set.Icc (0 : ℝ) T) := by
  obtain ⟨-, hq, -⟩ := hR ε ψ ρ hadm hres α T hT
  refine s116_continuous_of_quotient T _
    (fun t => propagatorW ((quadraticGradientDyn d 0 a β).coeff ρ) 0 t
      (generatorW ((quadraticGradientDyn d 0 a β).coeff ρ) t
        (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) x) ?_
  intro t ht e he
  obtain ⟨δ, hδ, hh⟩ := hq 0 (by omega) 0 t le_rfl ht.1 ht.2 e he
  refine ⟨δ, hδ, fun h h0 hhd hmem => ?_⟩
  have := hh h h0 hhd hmem.1 hmem.2 0 (Nat.zero_le _) x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  exact this

end HRS.MS.S116

end
