import HRS.MH.AdjointRdDefs
import HRS.Whole.AppendixAAdjoint

/-!
# S.A.12 assembly: the exact definitions of `skeleton/cores/SA12-ASSEMBLY.lean`

`rdProfile` and `ApproximationSequence`, copied verbatim (only the file header differs), so that the
limit assembly P3, the weighted companions B6/B7 and the stability limit S7 share one definition.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Assembly

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

def rdProfile {d : ℕ} (Rg : PDE.Regime) (C ν₀ s : ℝ) (m : ℕ)
    (χ φ : Euc d → ℝ) (τ : ℝ) : ℝ :=
  C*Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s)*τ)*(ulocNormE m χ φ).toReal

/-- Only the already constructed approximants and scalar/test bounds.
There is no whole-space limit or existence conclusion in this record. -/
structure ApproximationSequence {d : ℕ} (χ : Euc d → ℝ) (m : ℕ)
    (coeff : WholeCoeff d) (t : ℝ) (φ : Euc d → ℝ) (profile : ℝ → ℝ) where
  F : ℕ → ℝ → Euc d → ℝ
  datum : ℕ → Euc d → ℝ
  A : ℕ → ℝ → (Euc d → ℝ) → (Euc d → ℝ)
  B : ℝ
  nonneg_B : 0 ≤ B
  profile_bound : ∀ τ ∈ Icc (0 : ℝ) t, profile τ ≤ B
  bound : ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE m χ (F n τ) ≤ ENNReal.ofReal (profile τ)
  weak : ∀ n, IsWeakSol (A n) t (datum n) (F n)
  equi : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∃ K : ℝ, ∀ n,
    ∀ τ ∈ Icc (0 : ℝ) t, ∀ σ ∈ Icc (0 : ℝ) t,
      |(∫ x, F n τ x*ψ x)-∫ x, F n σ x*ψ x| ≤ K*|τ-σ|
  initial_converges : ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
    Tendsto (fun n => ∫ x, datum n x*ψ x) atTop (𝓝 (∫ x, φ x*ψ x))
  operator_measurable : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ σ ∈ Icc (0 : ℝ) t,
    AEStronglyMeasurable (weakOp coeff t σ ψ) volume ∧
      ∀ n, AEStronglyMeasurable (A n σ ψ) volume
  operator_converges : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ δ : ℝ, 0<δ →
    ∀ᶠ n in atTop, ∀ σ ∈ Icc (0 : ℝ) t,
      cellL2Sum (fun x => A n σ ψ x-weakOp coeff t σ ψ x) ≤ ENNReal.ofReal δ
  operator_bound : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∃ K : ℝ,
    ∀ σ ∈ Icc (0 : ℝ) t, cellL2Sum (weakOp coeff t σ ψ) ≤ ENNReal.ofReal K

end HRS.MH.AdjointRd.Phase2SA12Assembly
