import HRS.MS.UlTail
import HRS.MS.UlNormAux2

/-!
# UL-T tie: the orbit data lie in `UlClosure`

`orbitData_ulClosure`: with the hypotheses of `orbitData_decay` (the data of part 2 of S5.1), every
`(generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0)^[a] f` with `f` Schwartz lies in `UlClosure k θ` for
every `k` and every uniformly local cutoff `θ` (`ulClosure_of_decay` of UL-0 with limit `0`).
-/

noncomputable section

namespace HRS.MS.Ul

open HRS HRS.Whole

variable {d : ℕ}

theorem orbitData_ulClosure (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (ν : ℝ)
    (Q : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ) (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ)
    (σ : Euc d → Euc d) (hσ : ∀ i, ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = fun x => σ x i)
    (c : Euc d → Euc d) (hc : c = fun x => σ x - convGradConvW (rieszKernelGrad d s) ρ x)
    (f : SchwartzMap (Euc d) ℝ) (a k : ℕ) (θ : Euc d → ℝ) (hθ : IsUlCutoff θ) :
    UlClosure k θ
      ((fun g x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 g x)^[a] ⇑f) := by
  obtain ⟨hcd, _, hlim⟩ := orbitData_decay hd hs0 hsd ν Q ρ hρ σ hσ c hc f a
  refine ulClosure_of_decay k θ hθ _ 0 hcd (fun ε hε => ?_) (fun j _ _ ε hε => hlim j ε hε)
  obtain ⟨R, hR⟩ := hlim 0 ε hε
  refine ⟨R, fun x hx => ?_⟩
  have := hR x hx
  rw [norm_iteratedFDeriv_zero] at this
  simpa using this

end HRS.MS.Ul
