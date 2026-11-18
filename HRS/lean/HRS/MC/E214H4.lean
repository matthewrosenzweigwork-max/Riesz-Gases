import HRS.MC.E214H3
import HRS.MC.E213U4
import HRS.MC.E213U5a
import HRS.MC.E213U11a
import HRS.MD.EQGaussLift
import HRS.MD.EQGaussWindow
import HRS.Sections.Q41Aux14
import HRS.PDE.MeanFieldThermalUnique

/-!
# E214H4: the covariance assertion of Corollary 2.14

`covariance_relaxation`: the covariance clause of `HRS.Main.stationary_tensor_relaxation`, under two explicit
hypotheses on the coupled pair `(η, η̄)` (to be discharged by `E214E.exists_coupled_pair_proof` and
`E214F.p4_pair`):

* `PairHyp R T`: there is a coupled pair (the conclusions of `exists_coupled_pair_proof`, except
  independence/same-noise, which are not used) with the path-supremum bound at `p = 2` on `[0,T]`;
* `BridgeHyp S β₀ hE`: every such `η̄` is a `HRS.IsStationaryGaussianField` (at level `r = 2d+6`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MC.E214H

open HRS HRS.Main HRS.Sec7 HRS.MC.E213Plan HRS.MC.E213U11

variable {d : ℕ}

/-- The conclusions of `exists_coupled_pair_proof` that are used (laws of the initial fields and the linear
fluctuation equations for `η` and `η̄`). -/
def IsPairData (R : Regime d) (r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Y₀ Ys₀ : Ω → NegSobolev d r) (η ηs : ℝ → Ω → NegSobolev d r) : Prop :=
  IsCenteredGaussianWithCov r (P.map Y₀)
      (susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρ₀) R.β₀) ∧
    IsCenteredGaussianWithCov r (P.map Ys₀)
      (susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρβ) R.β) ∧
    (∀ T : ℝ, IsLinearFluctuationSolution P R.D R.ρ r R.D.invβ T Y₀ η) ∧
    (∀ T : ℝ, IsLinearFluctuationSolution P R.D (fun _ => R.ρβ) r R.D.invβ T Ys₀ ηs)

/-- The path-supremum estimate at `p = 2` (the conclusion of `p4_pair` for `p = 2`, `T`). -/
def SupBound (r T : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (η ηs : ℝ → Ω → NegSobolev d r) : Prop :=
  ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ a : ℝ, 0 ≤ a →
    ∫⁻ ω, (⨆ t ∈ Icc (0 : ℝ) T, ‖η (a + t) ω - ηs (a + t) ω‖ₑ) ^ (2 : ℝ) ∂P ≤
      ENNReal.ofReal ((C * Real.exp (-κ * a)) ^ (2 : ℝ))

/-- Hypothesis A: a coupled pair with the path-supremum bound. -/
def PairHyp (R : Regime d) (T : ℝ) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (Y₀ Ys₀ : Ω → NegSobolev d (HRS.MC.E213Plan.rLvl d)) (η ηs : ℝ → Ω → NegSobolev d (HRS.MC.E213Plan.rLvl d)),
    IsPairData R (HRS.MC.E213Plan.rLvl d) P Y₀ Ys₀ η ηs ∧ SupBound (HRS.MC.E213Plan.rLvl d) T P η ηs

/-- Hypothesis B (the bridge): the stationary half of every such pair is a stationary Gaussian field. -/
def BridgeHyp (S : PreparedData d) (β₀ : ℝ) {m : ℝ} (hE : EdgeworthHyp S β₀ m) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y₀ Ys₀ : Ω → NegSobolev d (HRS.MC.E213Plan.rLvl d)) (η ηs : ℝ → Ω → NegSobolev d (HRS.MC.E213Plan.rLvl d)),
    IsPairData (HRS.MC.E213A.regimeOfPrepared S β₀ hE) (HRS.MC.E213Plan.rLvl d) P Y₀ Ys₀ η ηs →
    IsStationaryGaussianField P S.s S.β S.hs0 S.hsd S.hβ S.V (HRS.MC.E213A.regimeOfPrepared S β₀ hE).ρβ
      (HRS.MC.E213Plan.rLvl d) ηs

theorem thermal_eq (S : PreparedData d) (β₀ : ℝ) {m : ℝ} (hE : EdgeworthHyp S β₀ m)
    (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) :
    ρβ = (HRS.MC.E213A.regimeOfPrepared S β₀ hE).ρβ := by
  obtain ⟨hth, hsm, hpos⟩ := (HRS.MC.E213A.regimeOfPrepared S β₀ hE).thermal
  obtain ⟨hpos', hsm'⟩ := HRS.Q41.q41_thermal_regular S.hd S.hs0 S.hsd S.hβ S.hV hρβ
  exact HRS.PDE.MFThermal.thermal_unique S.hd S.s S.hs0 S.hsd S.β S.hβ S.V _ _ hth
    (HRS.PDE.MFLinear.continuous_of_isSmooth hsm) hpos hρβ
    (HRS.PDE.MFLinear.continuous_of_isSmooth hsm') hpos'

end HRS.MC.E214H

end
