import HRS.MS.UlClass
import HRS.Whole.Adjoint

/-!
# UL-5 tie: `ul_adjoint_fixed_viscosity` (S5.1, part 1)

`ul_adjoint_fixed_viscosity_proof` has exactly the type of the frozen statement `HRS.Whole.ul_adjoint_fixed_viscosity`
(the frozen declaration is `unproved`; a warning is expected).  `k₀ = ⌊4 + d/2⌋ + 1`; the existence and the bound come
from `ul_evolution_exists`, uniqueness from `ul_evolution_unique`; the bound for an arbitrary evolution follows by
uniqueness.  No restriction on `s ∈ [0,d)` and no extra hypothesis.
-/

noncomputable section

namespace HRS.MS.Ul

open HRS HRS.Whole Set

theorem ul_adjoint_fixed_viscosity_proof : type_of% @HRS.Whole.ul_adjoint_fixed_viscosity := by
  intro d hd s hs0 hsd θ hθ
  refine ⟨⌊(4 : ℝ) + (d : ℝ) / 2⌋₊ + 1, fun k hk T ν Q M ρ c hT hν hρ hc => ?_⟩
  have hk' : (4 : ℝ) + (d : ℝ) / 2 < k :=
    (Nat.lt_floor_add_one _).trans_le (by exact_mod_cast hk)
  obtain ⟨C, hC⟩ := ul_evolution_exists hs0 hsd θ hθ k hk' T ν hT hν Q M ρ hρ.2 c hc
  refine ⟨C, fun t ht f hf => ?_⟩
  obtain ⟨u₀, hu₀, hb₀⟩ := hC t ht f hf
  have huniq : ∀ u u', IsUlBackwardEvolution θ k (fixedViscosityCoeff s M Q ν c ρ) t f u →
      IsUlBackwardEvolution θ k (fixedViscosityCoeff s M Q ν c ρ) t f u' →
      ∀ r ∈ Icc (0 : ℝ) t, u r = u' r := fun u u' hu hu' =>
    ul_evolution_unique hs0 hsd θ hθ k hk' ν hν Q M ρ hρ.2 c hc ht.1 hu hu'
  refine ⟨⟨u₀, hu₀⟩, huniq, fun u hu r hr => ?_⟩
  rw [huniq u u₀ hu hu₀ r hr]
  exact hb₀ r hr

end HRS.MS.Ul
