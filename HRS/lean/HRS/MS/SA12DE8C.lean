import HRS.MS.SA12DE8B
import HRS.MS.SA12X3C15

/-!
# S.A.12(c), packet E7.08 (worker S82Z2), part C: the periodic box energy statement (E7.06 for periodic solutions)

`Sa12BoxPeriodicStmt` is the exact statement that the E7.08 tie needs from E7.06.  It has the shape of `periodic_uloc_bound`
(`SA12X3C15`): the constant `C` and the threshold `L₁` are chosen before `ν₀, L, γ, M, ν, μ, V, b, t, F`, and for every periodic
solution `F` (`IsPerSol`) of a `PerData` problem in a regime that holds
`boxEnergy m L (F τ) ≤ exp (2 · lambdaM C ν₀ θ · τ) · boxEnergy m L (F 0)`, `θ = thetaOrder d s`.
The factor `2` is because the frozen `H^m` bound is for the square root of the energy.  It follows from E7.06 (`sa12c_box_energy_bound`) and
E7.05 (`sa12c_periodic_global_nonlocal_form`) by taking `C` large: `lambdaM C ν₀ θ = C·k(ν₀)` with `k ≥ 1`, so
`2·lambdaM C ν₀ θ ≥ (d+1)^m·sa12cK d m Cb + card E·lambdaM C_near ν₀ θ + Crem` as soon as `C ≥ card E·C_near + (d+1)^m·sa12cK d m Cb + Crem`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.SA12DE8

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12C

/-- **The E7.06 statement for periodic solutions** (an explicit hypothesis of the E7.08 tie until proved). -/
def Sa12BoxPeriodicStmt : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (s : ℝ), 0 ≤ s → s < d → (d : ℝ) < 2 * (s + 1) → ∀ (m : ℕ), 1 ≤ m →
    ∀ (Rg : PDE.Regime) (MB Λ ΛV νbar Cb T : ℝ) (χ : Euc d → ℝ), IsUlocCutoff χ →
    ∃ C L₁ : ℝ, 0 < C ∧ 0 < L₁ ∧ ∀ (ν₀ L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ)
      (μ : ℝ → Euc d → ℝ) (V : Euc d → ℝ) (b : ℝ → Euc d → Euc d), L₁ ≤ L →
      PerData s m MB Λ ΛV νbar Cb T L γ M ν μ V b →
      RdRegimeHolds Rg d s M ν ν₀ → ∀ t ∈ Ioc (0 : ℝ) T, ∀ F : ℝ → Euc d → ℝ,
        IsPerSol m L γ M ν μ b (fun _ _ => 0) t F → ∀ τ ∈ Icc (0 : ℝ) t,
          boxEnergy m L (F τ) ≤
            Real.exp (2 * Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ) * boxEnergy m L (F 0)

end HRS.MS.SA12DE8
