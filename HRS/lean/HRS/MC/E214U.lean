import HRS.MC.E214Final
import HRS.MC.WinJP12

/-!
# E214U: Corollary 2.14 tensor clause without the `WinJCompare` hypothesis

`stationary_tensor_relaxation_proof` is `HRS.MC.E214Final.stationary_tensor_relaxation_cond` with the
hypothesis `hJ` supplied by the proved `HRS.MC.WinJ.p_assembly`.  The statement is the frozen
`HRS.Main.stationary_tensor_relaxation` (checked in `HRS/MC/E214UTie.lean`).  This file imports no sorried module.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214U

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan HRS.MC.E214O

variable {d : ℕ}

/-- Corollary 2.14 (tensor clause) with `hJ` discharged by `WinJ.p_assembly`. -/
theorem stationary_tensor_relaxation_proof (S : PreparedData d) (β₀ m T : ℝ) (hE : EdgeworthHyp S β₀ m)
    (hT : 0 < T) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (K : ℝ → projTensor (PathSpace d m T) 3)
    (ε : ℕ → ℝ) (hK : IsWindowEdgeworth S β₀ m T K ε) :
    ∃ (Kst : projTensor (PathSpace d m T) 3) (C c : ℝ), 0 < C ∧ 0 < c ∧
      (∀ a : ℝ, 0 ≤ a → ‖K a - Kst‖ ≤ C * Real.exp (-c * a)) ∧
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
  HRS.MC.E214Final.stationary_tensor_relaxation_cond S β₀ m T hE hT ρβ hρβ K ε hK
    (fun sd => HRS.MC.WinJ.p_assembly sd T hT)

end HRS.MC.E214U

end
