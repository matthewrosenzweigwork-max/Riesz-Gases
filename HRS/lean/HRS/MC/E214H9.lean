import HRS.MC.E214H8
import HRS.MC.E214G6

/-!
# E214H9: the covariance assertion of Corollary 2.14 without hypotheses

`pairHyp_proof` discharges the hypothesis `PairHyp` of `E214H4` by `E214G.p4_pair_proof`, and
`covariance_relaxation_proof` is then `covariance_relaxation_of_p4` with no remaining hypothesis on the path-supremum
estimate.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MC.E214H

open HRS HRS.Main HRS.Sec7 HRS.MC.E213Plan

variable {d : ℕ}

theorem pairHyp_proof (R : Regime d) (T : ℝ) (hT : 0 < T) : PairHyp R T := by
  obtain ⟨Ω, mΩ, P, hP, Y₀, Ys₀, η, ηs, hpair, hsup⟩ :=
    HRS.MC.E214G.p4_pair_proof R (rLvl d) rfl
  obtain ⟨h1, h2, _, h4, h5, _⟩ := hpair
  obtain ⟨C, κ, hC, hκ, h⟩ := hsup hT (le_refl (2 : ℝ))
  exact ⟨Ω, mΩ, P, hP, Y₀, Ys₀, η, ηs, ⟨h1, h2, h4, h5⟩, C, κ, hC, hκ, h⟩

/-- **Covariance assertion of Corollary 2.14** (`HRS.Main.stationary_tensor_relaxation`, second clause). -/
theorem covariance_relaxation_proof (S : PreparedData d) (β₀ m T : ℝ) (hE : EdgeworthHyp S β₀ m)
    (hT : 0 < T) (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ a : ℝ, 0 ≤ a →
      ∀ (ν : Measure (NegSobolev d m)),
        IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0) →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Z₀ Z →
      ∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
        (Zs : ℝ → Ω'' → NegSobolev d m),
        IsStationaryGaussianField P'' S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Zs →
        covDist P' P'' (windowPath m T a Z) (windowPath m T 0 Zs) ≤ C * Real.exp (-c * a) :=
  covariance_relaxation S β₀ m T hE hT ρβ hρβ (pairHyp_proof _ T hT) (bridge_proof S β₀ hE)

end HRS.MC.E214H

end
