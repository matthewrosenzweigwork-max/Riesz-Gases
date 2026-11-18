import HRS.Whole.AppendixAAdjoint
import HRS.MS.SA12CompB7

/-!
# S.A.12 B11: the weighted clause (e), from the weighted approximation sequence

`WeightedApproxSeqStatement` is the exact statement of B6 `weighted_approximation_sequence` (the unproved producer);
`adjoint_rd_weighted_of_sequence` is the written assembly B11 with B6 as the explicit hypothesis, B7 proved.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Companions

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Assembly

/-- The statement of B6 (`weighted_approximation_sequence`), verbatim. -/
def WeightedApproxSeqStatement : Prop :=
  ∀ {d : ℕ} (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (m : ℕ) (hm : 1 ≤ m) (Rg : PDE.Regime) (MB Λ ΛV G₀ νbar T : ℝ)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ),
    ∃ C : ℝ, 0 < C ∧ ∀ (D : WholeDyn d) (ν₀ : ℝ) (μ : ℝ → Euc d → ℝ),
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ → RdRegimeHolds Rg d s D.M D.invβ ν₀ →
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ φ : Euc d → ℝ, ulocNormE m χ φ < ⊤ →
      ∃ a : ApproximationSequence (d := d) χ m (D.coeff μ) t φ (rdProfile Rg C ν₀ s m χ φ),
        ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, varpiNormE m χ (a.F n τ) ≤
          ENNReal.ofReal (C * Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s) * τ)) * varpiNormE m χ φ

-- BEGIN SA12.B11
theorem adjoint_rd_weighted_of_sequence (hB6 : WeightedApproxSeqStatement) :
    type_of% @HRS.Whole.AppendixA.adjoint_rd_weighted := by
  intro d hd s hs0 hsd m hm Rg MB Λ ΛV G₀ νbar T χ hχ
  obtain ⟨C,hC,hseq⟩ := hB6 hd s hs0 hsd m hm Rg MB Λ ΛV G₀ νbar T χ hχ
  refine ⟨C,hC,?_⟩
  intro D ν₀ μ hD hR t ht φ hφ F hF
  obtain ⟨a,ha⟩ := hseq D ν₀ μ hD hR t ht φ hφ
  exact weighted_bound_from_sequence hd s hs0 hsd m hm Rg MB Λ ΛV G₀ νbar T χ hχ
    D ν₀ μ hD hR t ht φ hφ (rdProfile Rg C ν₀ s m χ φ) a
    (fun τ => ENNReal.ofReal (C*Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s)*τ))*varpiNormE m χ φ)
    ha F hF
-- END SA12.B11

end HRS.MH.AdjointRd.Phase2SA12Companions
