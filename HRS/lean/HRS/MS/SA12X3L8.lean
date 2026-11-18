import HRS.MS.SA12X3L8A
import HRS.MS.SA12X3N2

/-!
# S.A.12 L8 (SA12X3): `weak_operator_convergence`

Contract fix (recorded in HANDOFF_SA12X2.md): the uniform bound of the periodic weak operator is asserted for
`L ≥ Lmin` (some `Lmin ≥ max 1 L₀`), the convergence conjunct is exactly the skeleton one.
-/

set_option autoImplicit false
set_option maxHeartbeats 25600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd

variable {d : ℕ}

theorem sa12x3_weak_operator_convergence (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ ΛV G₀ νbar T : ℝ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) (Λ' ΛV' Cb L₀ : ℝ) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T)
    (γ : ℝ → Euc d → ℝ) (μL : ℝ → ℝ → ℝ → Euc d → ℝ) (VL : ℝ → ℝ → Euc d → ℝ)
    (hA : PerApprox s m MB Λ' ΛV' νbar Cb T D μ γ t L₀ μL VL) (ψ : Euc d → ℝ) (hψ : IsCcInfty ψ) :
    ∃ Lmin : ℝ, max 1 L₀ ≤ Lmin ∧
      (∃ K : ℝ, ∀ L : ℝ, Lmin ≤ L → ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) 1 → ∀ σ ∈ Icc (0 : ℝ) t,
        cellL2Sum (weakOpPer L (γ L) D.M D.invβ (μL L ε)
          (fun τ => HRS.Whole.AppendixALemmas.torusDriftL D.M L (γ L) (μL L ε τ) (VL L ε)) σ ψ) ≤
            ENNReal.ofReal K) ∧
      ∀ δ : ℝ, 0 < δ → ∃ L₁ ε₀ : ℝ, 0 < ε₀ ∧ ∀ L : ℝ, L₁ ≤ L → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ∀ σ ∈ Icc (0 : ℝ) t,
        cellL2Sum (fun x => weakOpPer L (γ L) D.M D.invβ (μL L ε)
          (fun τ => HRS.Whole.AppendixALemmas.torusDriftL D.M L (γ L) (μL L ε τ) (VL L ε)) σ ψ x -
            weakOp (D.coeff μ) t σ ψ x) ≤ ENNReal.ofReal δ := by
  obtain ⟨Lmin, c, hLmin, hc, hN1⟩ := sa12x3n_N1 hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T D μ hD Λ' ΛV' Cb L₀ t ht
    γ μL VL hA ψ hψ
  exact ⟨Lmin, hLmin, sa12x3n_L8_of_nonlocal hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T D μ hD Λ' ΛV' Cb L₀ t ht
    γ μL VL hA Lmin hLmin ψ hψ ⟨c, hc, hN1⟩ (sa12x3n_N2 hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T D μ hD Λ' ΛV' Cb L₀ t ht
    γ μL VL hA ψ hψ)⟩

end HRS.MH.AdjointRd.Phase2SA12Limit
