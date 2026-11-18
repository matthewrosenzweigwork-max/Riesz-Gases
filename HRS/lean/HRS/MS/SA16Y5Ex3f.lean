import HRS.MS.SA16Y5Ex2f

/-!
# S.A.16 (SA16Y5) Ex3f: `adjoint_lp` for `LpCase.iso` and `LpCase.hilbert` in the fractional range `d-1 < s < d`

`sa16y5_adjoint_lp_iso_hi`, `sa16y5_adjoint_lp_hilbert_hi`: exactly the statement of `adjoint_lp` (HRS/Whole/AppendixAAdjoint.lean) for `κc := LpCase.iso`, resp.
`LpCase.hilbert`, under the single extra hypothesis `hs1 : d - 1 < s` (in the shape of `sa16y5_adjoint_lp_iso` / `_hilbert`).  Uniqueness: `bounded_lp_uniqueness_bridge`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Ex3f
variable {d : ℕ}

theorem sa16y5_adjoint_lp_iso_hi (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : (d : ℝ) - 1 < s) (m : ℕ)
    (hm : 1 ≤ m) (p : ℝ) [Fact (2 ≤ p)] (MB Λ ΛV G₀ νbar T : ℝ) (χ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : WholeDyn d) (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ),
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ → LpCase.iso.Holds d s p D.M →
      ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, wNormE m p φ < ⊤ →
        (∃ F : ℝ → EuclideanSpace ℝ (Fin d) → ℝ, IsLpSolutionRd m p χ (D.coeff μ) t φ F ∧
          ∀ τ ∈ Set.Icc (0 : ℝ) t, wNormE m p (F τ) ≤
            ENNReal.ofReal (C * Real.exp (C * τ)) * wNormE m p φ) ∧
        ∀ F₁ F₂ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ, IsLpSolutionRd m p χ (D.coeff μ) t φ F₁ →
          IsLpSolutionRd m p χ (D.coeff μ) t φ F₂ →
          ∀ τ ∈ Set.Icc (0 : ℝ) t, F₁ τ =ᵐ[volume] F₂ τ := by
  have hiso : (d : ℝ) - 2 < s := by linarith
  obtain ⟨C, hC, H⟩ := sa16y5f_exists_gen hd s hsd hs1 m hm p MB Λ ΛV G₀ νbar T
    (fun M => ∃ lam : ℝ, 0 ≤ lam ∧ M = -(lam • (1 : Matrix (Fin d) (Fin d) ℝ)))
    (fun Wd hWd => sa16y5f_Hex_iso hd hs0 hsd hs1 m MB Wd hWd) χ hχ
  refine ⟨C, hC, fun D μ hD hκ t ht φ hφ => ?_⟩
  obtain ⟨-, lam, hlam, hMl⟩ := hκ
  exact ⟨H D μ hD ⟨lam, hlam.le, hMl⟩ t ht φ hφ, fun F₁ F₂ h₁ h₂ =>
    Phase2SA16Assembly.sa16y4_lp_unique d hd s hs0 hsd m hm p LpCase.iso MB Λ ΛV G₀ νbar T χ D μ hD
      ⟨hiso, lam, hlam, hMl⟩ t ht φ F₁ F₂ h₁ h₂⟩

theorem sa16y5_adjoint_lp_hilbert_hi (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : (d : ℝ) - 1 < s)
    (m : ℕ) (hm : 1 ≤ m) (p : ℝ) [Fact (2 ≤ p)] (MB Λ ΛV G₀ νbar T : ℝ) (χ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : WholeDyn d) (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ),
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ → LpCase.hilbert.Holds d s p D.M →
      ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, wNormE m p φ < ⊤ →
        (∃ F : ℝ → EuclideanSpace ℝ (Fin d) → ℝ, IsLpSolutionRd m p χ (D.coeff μ) t φ F ∧
          ∀ τ ∈ Set.Icc (0 : ℝ) t, wNormE m p (F τ) ≤
            ENNReal.ofReal (C * Real.exp (C * τ)) * wNormE m p φ) ∧
        ∀ F₁ F₂ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ, IsLpSolutionRd m p χ (D.coeff μ) t φ F₁ →
          IsLpSolutionRd m p χ (D.coeff μ) t φ F₂ →
          ∀ τ ∈ Set.Icc (0 : ℝ) t, F₁ τ =ᵐ[volume] F₂ τ := by
  have hhil : (d : ℝ) - 2 < s := by linarith
  by_cases hp2 : p = 2
  · obtain ⟨C, hC, H⟩ := sa16y5f_exists_gen hd s hsd hs1 m hm p MB Λ ΛV G₀ νbar T
      (fun M => ∃ lam : ℝ, 0 ≤ lam ∧ ∃ A : Matrix (Fin d) (Fin d) ℝ, A.transpose = -A ∧
        M = -(lam • (1 : Matrix (Fin d) (Fin d) ℝ)) + A)
      (fun Wd hWd => sa16y5f_Hex_hilb hd hs0 hsd hs1 hp2 m MB Wd hWd) χ hχ
    refine ⟨C, hC, fun D μ hD hκ t ht φ hφ => ?_⟩
    obtain ⟨-, hp, lam, hlam, A, hA, hMl⟩ := hκ
    exact ⟨H D μ hD ⟨lam, hlam, A, hA, hMl⟩ t ht φ hφ, fun F₁ F₂ h₁ h₂ =>
      Phase2SA16Assembly.sa16y4_lp_unique d hd s hs0 hsd m hm p LpCase.hilbert MB Λ ΛV G₀ νbar T χ D μ hD
        ⟨hhil, hp, lam, hlam, A, hA, hMl⟩ t ht φ F₁ F₂ h₁ h₂⟩
  · exact ⟨1, one_pos, fun D μ hD hκ => absurd hκ.2.1 hp2⟩

end Ex3f

section Check
open HRS.Whole.AppendixA in
example (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : (d : ℝ) - 1 < s) (m : ℕ) (hm : 1 ≤ m)
    (p : ℝ) [Fact (2 ≤ p)] (MB Λ ΛV G₀ νbar T : ℝ) (χ : EuclideanSpace ℝ (Fin d) → ℝ) (hχ : IsUlocCutoff χ) :
    type_of% (HRS.Whole.AppendixA.adjoint_lp hd s hs0 hsd m hm p LpCase.iso MB Λ ΛV G₀ νbar T χ hχ) :=
  sa16y5_adjoint_lp_iso_hi hd s hs0 hsd hs1 m hm p MB Λ ΛV G₀ νbar T χ hχ

open HRS.Whole.AppendixA in
example (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : (d : ℝ) - 1 < s) (m : ℕ) (hm : 1 ≤ m)
    (p : ℝ) [Fact (2 ≤ p)] (MB Λ ΛV G₀ νbar T : ℝ) (χ : EuclideanSpace ℝ (Fin d) → ℝ) (hχ : IsUlocCutoff χ) :
    type_of% (HRS.Whole.AppendixA.adjoint_lp hd s hs0 hsd m hm p LpCase.hilbert MB Λ ΛV G₀ νbar T χ hχ) :=
  sa16y5_adjoint_lp_hilbert_hi hd s hs0 hsd hs1 m hm p MB Λ ΛV G₀ νbar T χ hχ

end Check

end HRS.Whole.AppendixA.Phase2SA16R
