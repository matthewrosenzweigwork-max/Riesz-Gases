import HRS.MS.SA12V3I

/-!
# S.A.12 L8 (SA12V3 worker): `weak_operator_converges` unconditionally

`sa12v3_weak_operator_converges` has the exact statement of the unproved spec theorem `weak_operator_converges`
(`HRS/MH/AdjointRdSpec.lean`): `sa12k_L8_of_nonlocal` with its hypotheses N1, N2 discharged by `sa12v3_N1`, `sa12v3_N2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Pointwise

namespace HRS.MH.AdjointRd.Phase2SA12V3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

set_option maxHeartbeats 4000000 in
theorem sa12v3_weak_operator_converges (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ ΛV G₀ νbar T : ℝ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) (Λ' ΛV' Cb L₀ : ℝ) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T)
    (γ : ℝ → Euc d → ℝ) (μL : ℝ → ℝ → ℝ → Euc d → ℝ) (VL : ℝ → ℝ → Euc d → ℝ)
    (hA : PerApprox s m MB Λ' ΛV' νbar Cb T D μ γ t L₀ μL VL) (ψ : Euc d → ℝ) (hψ : IsCcInfty ψ) :
    (∃ K : ℝ, ∀ L : ℝ, max 1 L₀ ≤ L → ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) 1 → ∀ σ ∈ Icc (0 : ℝ) t,
      cellL2Sum (weakOpPer L (γ L) D.M D.invβ (μL L ε)
        (fun τ => HRS.Whole.AppendixALemmas.torusDriftL D.M L (γ L) (μL L ε τ) (VL L ε)) σ ψ) ≤ ENNReal.ofReal K) ∧
    ∀ δ : ℝ, 0 < δ → ∃ L₁ ε₀ : ℝ, 0 < ε₀ ∧ ∀ L : ℝ, L₁ ≤ L → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ σ ∈ Icc (0 : ℝ) t,
      cellL2Sum (fun x => weakOpPer L (γ L) D.M D.invβ (μL L ε)
        (fun τ => HRS.Whole.AppendixALemmas.torusDriftL D.M L (γ L) (μL L ε τ) (VL L ε)) σ ψ x -
          weakOp (D.coeff μ) t σ ψ x) ≤ ENNReal.ofReal δ :=
  HRS.MH.AdjointRd.Phase2SA12Limit.sa12k_L8_of_nonlocal hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T D μ hD Λ' ΛV' Cb L₀ t ht
    γ μL VL hA ψ hψ (sa12v3_N1 hd s hs0 hsd m MB Λ' ΛV' νbar Cb T D μ t L₀ ht γ μL VL hA ψ hψ)
    (sa12v3_N2 hd s hs0 hsd m MB Λ ΛV G₀ νbar T D μ hD Λ' ΛV' Cb L₀ t ht γ μL VL hA ψ hψ)

end HRS.MH.AdjointRd.Phase2SA12V3
