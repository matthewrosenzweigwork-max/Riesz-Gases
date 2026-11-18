import HRS.MS.SA16Y4Ex1
import HRS.MS.SA16Y4Un1

/-!
# S.A.16 (SA16Y4) Ex2: `adjoint_lp` for `LpCase.sub` (existence, bound and uniqueness)

`sa16y4_adjoint_lp_sub` is the statement of `adjoint_lp` (HRS/Whole/AppendixAAdjoint.lean) with `κc := LpCase.sub`, proved
from `sa16y4_sub_exists` (Ex1) and `sa16y4_lp_unique` (Un1).  The frozen theorem quantifies over `κc : LpCase`, so it follows
from this one only together with the `iso` and `hilbert` cases.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Ex2
variable {d : ℕ}

theorem sa16y4_adjoint_lp_sub (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m) (p : ℝ)
    [Fact (2 ≤ p)] (MB Λ ΛV G₀ νbar T : ℝ) (χ : EuclideanSpace ℝ (Fin d) → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : WholeDyn d) (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ),
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ → LpCase.sub.Holds d s p D.M →
      ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, wNormE m p φ < ⊤ →
        (∃ F : ℝ → EuclideanSpace ℝ (Fin d) → ℝ, IsLpSolutionRd m p χ (D.coeff μ) t φ F ∧
          ∀ τ ∈ Set.Icc (0 : ℝ) t, wNormE m p (F τ) ≤
            ENNReal.ofReal (C * Real.exp (C * τ)) * wNormE m p φ) ∧
        ∀ F₁ F₂ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ, IsLpSolutionRd m p χ (D.coeff μ) t φ F₁ →
          IsLpSolutionRd m p χ (D.coeff μ) t φ F₂ →
          ∀ τ ∈ Set.Icc (0 : ℝ) t, F₁ τ =ᵐ[volume] F₂ τ := by
  by_cases hsub : s ≤ (d : ℝ) - 2 ∧ (d : ℝ) < p * (s + 1)
  · obtain ⟨C, hC, H⟩ := sa16y4_sub_exists hd s hs0 hsd m hm p MB Λ ΛV G₀ νbar T χ hχ hsub
    refine ⟨C, hC, fun D μ hD hκ t ht φ hφ => ⟨H D μ hD t ht φ hφ, fun F₁ F₂ h₁ h₂ => ?_⟩⟩
    exact Phase2SA16Assembly.sa16y4_lp_unique d hd s hs0 hsd m hm p LpCase.sub MB Λ ΛV G₀ νbar T χ D μ hD hκ t ht φ
      F₁ F₂ h₁ h₂
  · exact ⟨1, one_pos, fun D μ hD hκ => absurd hκ hsub⟩
end Ex2

end HRS.Whole.AppendixA.Phase2SA16R
