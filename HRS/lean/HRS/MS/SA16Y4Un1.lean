import HRS.MS.SA16V4

/-!
# S.A.16 (SA16Y4) Un1: the uniqueness clause of `adjoint_lp` from `bounded_lp_uniqueness_bridge`

`sa16y4_lp_unique`: two `IsLpSolutionRd` with the same datum agree a.e. at every time (the weak solution field and the
`W^{m,p}` bound field suffice).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Assembly
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16V Phase2SA16Evolution

theorem sa16y4_lp_unique (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m) (p : ℝ)
    [Fact (2 ≤ p)] (κc : LpCase) (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ) (D : WholeDyn d)
    (μ : ℝ → Euc d → ℝ) (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) (hκ : κc.Holds d s p D.M)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (φ : Euc d → ℝ) (F₁ F₂ : ℝ → Euc d → ℝ)
    (h₁ : IsLpSolutionRd m p χ (D.coeff μ) t φ F₁) (h₂ : IsLpSolutionRd m p χ (D.coeff μ) t φ F₂) :
    ∀ τ ∈ Icc (0 : ℝ) t, F₁ τ =ᵐ[volume] F₂ τ :=
  bounded_lp_uniqueness_bridge d hd s hs0 hsd m hm p κc MB Λ ΛV G₀ νbar T D μ hD hκ t ht φ F₁ F₂ h₁.sol h₂.sol
    h₁.bounded h₂.bounded

end HRS.Whole.AppendixA.Phase2SA16Assembly
