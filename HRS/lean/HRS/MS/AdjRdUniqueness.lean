import HRS.MS.AdjRdWeakSubtract
import HRS.MS.AdjRdZeroDist
import HRS.MS.UniqG2

/-!
# S.A.12 U2: the uniqueness clause of `adjoint_rd` from the S.A.33 engine
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.SA12BD

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

theorem sa12_uniqueness (d : ℕ) (hd : 1 ≤ d) (s : ℝ)
    (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (Rg : PDE.Regime) (MB Λ ΛV G₀ νbar T : ℝ)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (D : WholeDyn d) (ν₀ : ℝ)
    (μ : ℝ → Euc d → ℝ) (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ)
    (hR : RdRegimeHolds Rg d s D.M D.invβ ν₀)
    (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) T) (φ : Euc d → ℝ)
    (F₁ F₂ : ℝ → Euc d → ℝ)
    (h₁ : IsUlocSolutionRd χ m (D.coeff μ) t φ F₁)
    (h₂ : IsUlocSolutionRd χ m (D.coeff μ) t φ F₂) :
    ∀ τ ∈ Set.Icc (0 : ℝ) t, F₁ τ =ᵐ[volume] F₂ τ := by
  obtain ⟨hDs, -, -⟩ := hD.hs
  -- the difference is bounded in `H¹_uloc`
  have hb : IsUlBounded χ 1 t (fun τ x => F₁ τ x - F₂ τ x) := by
    obtain ⟨B₁, hB₁⟩ := h₁.bounded
    obtain ⟨B₂, hB₂⟩ := h₂.bounded
    refine ⟨max B₁ 0 + max B₂ 0, fun τ hτ => ?_⟩
    calc ulocNormE 1 χ (fun x => F₁ τ x - F₂ τ x)
        ≤ ulocNormE 1 χ (F₁ τ) + ulocNormE 1 χ (F₂ τ) := sa12_uloc_sub d 1 χ _ _
      _ ≤ ulocNormE m χ (F₁ τ) + ulocNormE m χ (F₂ τ) :=
          add_le_add (sa12_uloc_mono d m 1 hm χ _) (sa12_uloc_mono d m 1 hm χ _)
      _ ≤ ENNReal.ofReal (max B₁ 0) + ENNReal.ofReal (max B₂ 0) :=
          add_le_add ((hB₁ τ hτ).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
            ((hB₂ τ hτ).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
      _ = ENNReal.ofReal (max B₁ 0 + max B₂ 0) :=
          (ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)).symm
  have hsub := sa12_forward_sub d (D.coeff μ) t φ F₁ F₂ h₁.sol h₂.sol
  have hz := sa12_zero_forward_dist d hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T χ hχ D μ hD t ht
    (fun τ x => F₁ τ x - F₂ τ x) hsub hb
  have htT : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  have hDeq : D = (⟨s, D.M, D.V, D.invβ⟩ : WholeDyn d) := by
    cases D; simp_all
  have key := HRS.MS.UniqG2.uloc_uniqueness_proof hd s hs0 hsd m hm Rg T Λ ΛV G₀ MB νbar ν₀ χ hχ
    D.M D.V D.invβ μ hD.hM hD.hV hD.hν hD.hμ hR t htT (fun τ x => F₁ τ x - F₂ τ x) hb
    (by rw [← hDeq]; exact hz)
  intro τ hτ
  filter_upwards [key τ hτ] with x hx
  simpa [sub_eq_zero] using hx

end HRS.MS.SA12BD
