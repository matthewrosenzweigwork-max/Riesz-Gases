import HRS.MS.AdjRdNorms
import HRS.MS.FcauTie

/-!
# S.A.12 B1: restriction of the standing data and of solutions to a lower Sobolev level
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Companions

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

-- BEGIN SA12.B1
theorem restrict_data_and_solution (s : ℝ) (m k : ℕ) (hkm : k ≤ m)
    (MB Λ ΛV G₀ νbar T : ℝ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) :
    AdjointRdData s k MB Λ ΛV G₀ νbar D T μ ∧
      ∀ χ : Euc d → ℝ, ∀ t : ℝ, ∀ φ : Euc d → ℝ, ∀ F : ℝ → Euc d → ℝ,
        IsUlocSolutionRd χ m (D.coeff μ) t φ F →
        IsUlocSolutionRd χ k (D.coeff μ) t φ F := by
  refine ⟨⟨hD.hs, hD.hM, ?_, ⟨hD.hμ.prob, ?_, hD.hμ.cont⟩, hD.hT, hD.hν⟩, ?_⟩
  · exact ⟨hD.hV.1, fun j hj1 hj2 x => hD.hV.2.1 j hj1 (hj2.trans (by omega)) x, hD.hV.2.2⟩
  · refine ⟨fun t ht => ?_, hD.hμ.regular.2⟩
    obtain ⟨hcb, hfin, hbd⟩ := hD.hμ.regular.1 t ht
    have hw : weightedSupE (k + 3) ((d : ℝ) + 3) (μ t) ≤ weightedSupE (m + 3) ((d : ℝ) + 3) (μ t) :=
      HRS.MS.Fcau.fcau_weightedSupE_mono (by omega) _ _
    have hcbm : cbNorm (k + 3) (μ t) ≤ cbNorm (m + 3) (μ t) := by
      unfold cbNorm
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega)) ?_
      intro j _ _
      exact Real.iSup_nonneg fun x => norm_nonneg _
    refine ⟨⟨hcb.1.of_le (by exact_mod_cast (by omega : k + 3 ≤ m + 3)),
      fun j hj => hcb.2 j (hj.trans (by omega))⟩, lt_of_le_of_lt hw hfin, ?_⟩
    have := ENNReal.toReal_mono hfin.ne hw
    linarith
  · intro χ t φ F hF
    refine ⟨hF.sol, ?_, fun m' hm' z τ₀ hτ₀ ε hε => ?_⟩
    · obtain ⟨B, hB⟩ := hF.bounded
      exact ⟨B, fun τ hτ => (HRS.MS.SA12BD.sa12_uloc_mono d m k hkm χ (F τ)).trans (hB τ hτ)⟩
    · exact hF.cont m' (lt_of_lt_of_le hm' (by exact_mod_cast hkm)) z τ₀ hτ₀ ε hε
-- END SA12.B1

end HRS.MH.AdjointRd.Phase2SA12Companions
