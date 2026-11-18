import HRS.Whole.AppendixAAdjoint

/-!
# S.A.12 L19: scalar time continuity of the weak pairings of a forward solution
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

-- BEGIN SA12.L19
theorem forward_scalar_continuity (C : WholeCoeff d) (t : ℝ) (φ : Euc d → ℝ)
    (G : ℝ → Euc d → ℝ) (hG : IsForwardSolutionRd C t φ G)
    (ψ : Euc d → ℝ) (hψ : IsCcInfty ψ) :
    ContinuousOn (fun τ => ∫ x, G τ x * ψ x) (Icc (0 : ℝ) t) := by
  have hc : ContinuousOn (fun τ => (∫ x, φ x * ψ x) + ∫ σ in Icc (0 : ℝ) τ, forwardWeakTerm C t G ψ σ)
      (Icc (0 : ℝ) t) :=
    (intervalIntegral.continuousOn_primitive_Icc (hG.integrable_σ ψ hψ)).const_add _
  exact hc.congr fun τ hτ => hG.eq ψ hψ τ hτ
-- END SA12.L19

end HRS.MH.AdjointRd.Phase2SA12Limit
