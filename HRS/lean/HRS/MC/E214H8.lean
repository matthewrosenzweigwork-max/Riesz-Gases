import HRS.MC.E214H7
import HRS.MC.E214E5

/-!
# E214H8: assembly of the covariance assertion

`covariance_relaxation_of_p4`: the covariance clause of `HRS.Main.stationary_tensor_relaxation`
from the single hypothesis `hp4` = the conclusion of `E214F.p4_pair` at `p = 2` (the path-supremum estimate for
every coupled pair, stated verbatim below), the coupled pair itself being supplied by the proved
`E214E.exists_coupled_pair_proof` and the bridge by `bridge_proof`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MC.E214H

open HRS HRS.Main HRS.Sec7 HRS.MC.E213Plan

variable {d : ℕ}

/-- The conclusion of `HRS.MC.E214F.p4_pair` for `p = 2` (with `IsCoupledPair` unfolded). -/
def P4Stmt (R : Regime d) (T : ℝ) : Prop :=
  ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y₀ Ys₀ : Ω → NegSobolev d (rLvl d)) (η ηs : ℝ → Ω → NegSobolev d (rLvl d)),
    (IsCenteredGaussianWithCov (rLvl d) (P.map Y₀)
        (susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρ₀) R.β₀) ∧
      IsCenteredGaussianWithCov (rLvl d) (P.map Ys₀)
        (susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρβ) R.β) ∧
      IndepFun Y₀ Ys₀ P ∧
      (∀ T : ℝ, IsLinearFluctuationSolution P R.D R.ρ (rLvl d) R.D.invβ T Y₀ η) ∧
      (∀ T : ℝ, IsLinearFluctuationSolution P R.D (fun _ => R.ρβ) (rLvl d) R.D.invβ T Ys₀ ηs) ∧
      IsSameNoise R.D R.ρ (fun _ => R.ρβ) (rLvl d) P Y₀ Ys₀ η ηs) →
    ∀ a : ℝ, 0 ≤ a →
      ∫⁻ ω, (⨆ t ∈ Icc (0 : ℝ) T, ‖η (a + t) ω - ηs (a + t) ω‖ₑ) ^ (2 : ℝ) ∂P ≤
        ENNReal.ofReal ((C * Real.exp (-κ * a)) ^ (2 : ℝ))

theorem pairHyp_of_p4 (R : Regime d) (T : ℝ) (hp4 : P4Stmt R T) : PairHyp R T := by
  obtain ⟨C, κ, hC, hκ, hP4⟩ := hp4
  obtain ⟨Ω, mΩ, P, hP, Y₀, Ys₀, η, ηs, h1, h2, h3, h4, h5, h6⟩ :=
    HRS.MC.E214E.exists_coupled_pair_proof R (rLvl d) rfl
  refine ⟨Ω, mΩ, P, hP, Y₀, Ys₀, η, ηs, ⟨h1, h2, h4, h5⟩, C, κ, hC, hκ, fun a ha => ?_⟩
  exact hP4 P Y₀ Ys₀ η ηs ⟨h1, h2, h3, h4, h5, h6⟩ a ha

/-- **Covariance assertion of Corollary 2.14** (`HRS.Main.stationary_tensor_relaxation`, second clause), from the
path-supremum estimate `P4Stmt` for coupled pairs. -/
theorem covariance_relaxation_of_p4 (S : PreparedData d) (β₀ m T : ℝ) (hE : EdgeworthHyp S β₀ m)
    (hT : 0 < T) (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ)
    (hp4 : P4Stmt (HRS.MC.E213A.regimeOfPrepared S β₀ hE) T) :
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
  covariance_relaxation S β₀ m T hE hT ρβ hρβ (pairHyp_of_p4 _ T hp4) (bridge_proof S β₀ hE)

end HRS.MC.E214H

end
