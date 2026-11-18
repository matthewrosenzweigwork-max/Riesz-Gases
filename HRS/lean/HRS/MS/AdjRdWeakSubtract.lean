import HRS.Whole.AppendixAAdjoint

/-!
# S.A.12 U2a: solutions with a common datum subtract to a zero-datum weak solution
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.SA12BD

open HRS HRS.Whole HRS.Whole.AppendixA

theorem sa12_forward_sub (d : ℕ) (C : WholeCoeff d) (t : ℝ)
    (φ : Euc d → ℝ) (F₁ F₂ : ℝ → Euc d → ℝ)
    (h₁ : IsForwardSolutionRd C t φ F₁)
    (h₂ : IsForwardSolutionRd C t φ F₂) :
    IsForwardSolutionRd C t (fun _ => 0) (fun τ x => F₁ τ x - F₂ τ x) := by
  -- pointwise identity for the weak term on `[0,t]`
  have hterm : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ σ ∈ Set.Icc (0 : ℝ) t,
      forwardWeakTerm C t (fun τ x => F₁ τ x - F₂ τ x) ψ σ =
        forwardWeakTerm C t F₁ ψ σ - forwardWeakTerm C t F₂ ψ σ := by
    intro ψ hψ σ hσ
    obtain ⟨a1, a2, a3, a4⟩ := h₁.integrable_x ψ hψ σ hσ
    obtain ⟨b1, b2, b3, b4⟩ := h₂.integrable_x ψ hψ σ hσ
    unfold forwardWeakTerm
    have e2 : ∫ x, (F₁ σ x - F₂ σ x) * Laplacian.laplacian ψ x =
        (∫ x, F₁ σ x * Laplacian.laplacian ψ x) - ∫ x, F₂ σ x * Laplacian.laplacian ψ x := by
      rw [← integral_sub a2 b2]; congr 1; ext x; ring
    have e3 : ∫ x, (F₁ σ x - F₂ σ x) * movDiv (fun y => ψ y • C.drift (t - σ) y) x =
        (∫ x, F₁ σ x * movDiv (fun y => ψ y • C.drift (t - σ) y) x) -
          ∫ x, F₂ σ x * movDiv (fun y => ψ y • C.drift (t - σ) y) x := by
      rw [← integral_sub a3 b3]; congr 1; ext x; ring
    have e4 : ∫ x, (F₁ σ x - F₂ σ x) * nonlocalTestRd C (t - σ) ψ x =
        (∫ x, F₁ σ x * nonlocalTestRd C (t - σ) ψ x) -
          ∫ x, F₂ σ x * nonlocalTestRd C (t - σ) ψ x := by
      rw [← integral_sub a4 b4]; congr 1; ext x; ring
    rw [e2, e3, e4]; ring
  refine ⟨?_, ?_, ?_⟩
  · intro ψ hψ σ hσ
    obtain ⟨a1, a2, a3, a4⟩ := h₁.integrable_x ψ hψ σ hσ
    obtain ⟨b1, b2, b3, b4⟩ := h₂.integrable_x ψ hψ σ hσ
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (a1.sub b1).congr (Filter.Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)
    · exact (a2.sub b2).congr (Filter.Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)
    · exact (a3.sub b3).congr (Filter.Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)
    · exact (a4.sub b4).congr (Filter.Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)
  · intro ψ hψ
    have hI := (h₁.integrable_σ ψ hψ).sub (h₂.integrable_σ ψ hψ)
    refine hI.congr_fun (fun σ hσ => ?_) measurableSet_Icc
    exact (hterm ψ hψ σ hσ).symm
  · intro ψ hψ τ hτ
    have hτt : Set.Icc (0 : ℝ) τ ⊆ Set.Icc (0 : ℝ) t := Set.Icc_subset_Icc_right hτ.2
    have hint1 := (h₁.integrable_σ ψ hψ).mono_set hτt
    have hint2 := (h₂.integrable_σ ψ hψ).mono_set hτt
    obtain ⟨a1, a2, a3, a4⟩ := h₁.integrable_x ψ hψ τ hτ
    obtain ⟨b1, b2, b3, b4⟩ := h₂.integrable_x ψ hψ τ hτ
    have e1 : ∫ x, (F₁ τ x - F₂ τ x) * ψ x = (∫ x, F₁ τ x * ψ x) - ∫ x, F₂ τ x * ψ x := by
      rw [← integral_sub a1 b1]; congr 1; ext x; ring
    have e2 : ∫ σ in Set.Icc (0 : ℝ) τ,
        forwardWeakTerm C t (fun τ x => F₁ τ x - F₂ τ x) ψ σ =
          (∫ σ in Set.Icc (0 : ℝ) τ, forwardWeakTerm C t F₁ ψ σ) -
            ∫ σ in Set.Icc (0 : ℝ) τ, forwardWeakTerm C t F₂ ψ σ := by
      rw [← integral_sub hint1 hint2]
      refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
      exact hterm ψ hψ σ (hτt hσ)
    have q1 := h₁.eq ψ hψ τ hτ
    have q2 := h₂.eq ψ hψ τ hτ
    rw [e1, e2, q1, q2]
    simp

end HRS.MS.SA12BD
