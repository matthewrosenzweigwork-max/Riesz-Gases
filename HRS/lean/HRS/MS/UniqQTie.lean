import HRS.MS.UniqQAux9
import HRS.MS.OrbFeatTie

/-!
# UNIQ-Q tie: `HRS.Whole.orbit_feature_bounded`

`orbit_feature_bounded_proof` has exactly the binders and conclusion of the frozen
`HRS.Whole.orbit_feature_bounded`: it is `HRS.MS.S52B.orbit_feature_bounded_of_uniq` with the uniqueness hypothesis
`S52bUniq` discharged by `HRS.MS.UniqQ.uniqq_S52bUniq` (packet UNIQ-Q; the bound on `c` comes from
`UlOrb.smooth`).  The final `example` checks that the two statements agree.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.UniqQ

open HRS HRS.Whole HRS.MS.Ul HRS.MS.S52B

variable {d : ℕ}

theorem orbit_feature_bounded_proof (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (k : ℕ)
    (hk : (d : ℝ) / 2 + 6 < k) (m : ℝ) (hm : ((2 * k + 2 * d + 20 : ℕ) : ℝ) + 3 * d + 4 < m)
    (T ν : ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ) (c : Euc d → Euc d)
    (hT : 0 ≤ T) (hν : 0 < ν) (hρ : IsSchwartzDensity ρ)
    (hc : ∃ σ : Euc d → Euc d, (∀ i, ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = fun x => σ x i) ∧
      c = fun x => σ x - convGradConvW (rieszKernelGrad d s) ρ x) :
    ∀ b : ℕ, b + 1 ≤ k → ∃ Cb : ℝ, ∀ a : Fin d, ∀ r ∈ Set.Icc 0 T,
      ContDiff ℝ ((k - 1 : ℕ) : WithTop ℕ∞) (fun x => gradFeature (fixedViscosityCoeff s (-1) Q ν c ρ) m T a r x) ∧
      ∀ x : Euc d, ‖iteratedFDeriv ℝ b
        (fun y => gradFeature (fixedViscosityCoeff s (-1) Q ν c ρ) m T a r y) x‖ ≤ Cb := by
  obtain ⟨σ, hσ, hc'⟩ := hc
  obtain ⟨θ, hθ⟩ := s52b_exists_ulCutoff d
  have O : UlOrb d s ν ρ σ c θ := ⟨hd, hs0, hsd, hν, hρ.2, hσ, hc', hθ⟩
  obtain ⟨Λ, hΛ⟩ := O.smooth.2 0
  have hcb : ∃ Λ : ℝ, ∀ x, ‖c x‖ ≤ Λ := ⟨Λ, fun x => by
    have := hΛ x
    rwa [norm_iteratedFDeriv_zero] at this⟩
  exact orbit_feature_bounded_of_uniq hd s hs0 hsd k hk m hm T ν Q ρ c hT hν hρ ⟨σ, hσ, hc'⟩
    (uniqq_S52bUniq hν hs0 hsd Q hρ.2 hcb T)

example := (@orbit_feature_bounded_proof : type_of% @HRS.Whole.orbit_feature_bounded)

end HRS.MS.UniqQ
