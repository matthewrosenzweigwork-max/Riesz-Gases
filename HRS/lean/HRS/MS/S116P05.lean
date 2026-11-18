import HRS.MS.S116P04
import HRS.MS.S104eCoeff2
import HRS.MS.R2WinOrbTRD7

/-!
# S11.6 packet P05 (`R26-T8B.P05`): homogeneity of the choice-defined propagator on the actual nonlinear coefficient

Prefix `s116_`, namespace `HRS.MS.S116`.  Given the existence of one classical adjoint solution `f` with datum `φ` (so that `propagatorW` is not the junk value `0`),
`c f` is a classical adjoint solution with datum `c φ` (`s103c_lincomb`, legitimate because of the first-jet decay of `ρ t`, `s116_rho_decay`), and uniqueness
(`s104e_unique`) identifies both propagators with `f 0` and `c f 0`.
-/

set_option autoImplicit false

noncomputable section

namespace HRS.MS.S116

open HRS HRS.Whole

theorem s116_propagator_smul {d : ℕ} (hd : 2 ≤ d) {a β εstar c₁ C₁ : ℝ}
    (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρβ : IsThermalEquilibrium d 0 a β ρβ) {ε : ℝ} {ψ : Euc d → ℝ}
    {ρ : ℝ → Euc d → ℝ} (hadm : IsAdmissiblePerturbation ρβ εstar ε ψ)
    (hres : IsResultingSolution d 0 a β ρβ εstar ε ψ c₁ C₁ ρ)
    (t : ℝ) (ht : 0 ≤ t) (φ : Euc d → ℝ)
    (hex : ∃ f : ℝ → Euc d → ℝ, IsClassicalAdjointW ((quadraticGradientDyn d 0 a β).coeff ρ) t φ f)
    (c : ℝ) :
    propagatorW ((quadraticGradientDyn d 0 a β).coeff ρ) 0 t (fun x => c * φ x) =
      fun x => c * propagatorW ((quadraticGradientDyn d 0 a β).coeff ρ) 0 t φ x := by
  have hsd : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨A, -, hA⟩ := s116_rho_decay hd ha hβ hρβ hres
  obtain ⟨f, hf⟩ := hex
  have hL : (d : ℝ) < (d : ℝ) + 1 := by linarith
  have hlc := HRS.MS.R2WinOrbNL.s103c_lincomb (s := 0) (a := a) (β := β) hd le_rfl hsd hL ρ
    (fun τ hτ => hA τ hτ.1) c 0 hf hf
  have hdat : (fun y => c * φ y + 0 * φ y) = fun y => c * φ y := by
    funext y; ring
  rw [hdat] at hlc
  have ht' : t ∈ Set.Icc (0 : ℝ) t := ⟨ht, le_rfl⟩
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
  have u1 := HRS.MS.S104e.s104e_unique hd (s := 0) le_rfl hsd ha hβ εstar c₁ C₁ hρβ hadm hres t ht ht' hf 0 h0
  have u2 := HRS.MS.S104e.s104e_unique hd (s := 0) le_rfl hsd ha hβ εstar c₁ C₁ hρβ hadm hres t ht ht' hlc 0 h0
  rw [u2, u1]
  funext x
  ring

end HRS.MS.S116

end
