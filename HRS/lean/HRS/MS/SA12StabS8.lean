import HRS.Whole.AppendixAAdjoint
import HRS.MS.SA12StabS7

/-!
# S.A.12 S8: the stability clause (d), from the paired approximation sequence

`PairedApproxSeqStatement` is the exact statement of S6 `paired_approximation_sequence` (the unproved producer);
`adjoint_rd_stability_of_sequence` is the written assembly S8 with S6 as the explicit hypothesis, S7 proved.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Stability

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Assembly

/-- The statement of S6 (`paired_approximation_sequence`), verbatim. -/
def PairedApproxSeqStatement : Prop :=
  ∀ {d : ℕ} (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (m : ℕ) (hm : 1 ≤ m) (Rg : PDE.Regime) (MB Λ ΛV G₀ νbar T : ℝ)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ),
    ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧ ∀ (D₁ D₂ : WholeDyn d) (ν₀ : ℝ) (μ₁ μ₂ : ℝ → Euc d → ℝ),
      AdjointRdData s (m + 2) MB Λ ΛV G₀ νbar D₁ T μ₁ →
      AdjointRdData s (m + 2) MB Λ ΛV G₀ νbar D₂ T μ₂ →
      RdRegimeHolds Rg d s D₁.M D₁.invβ ν₀ → RdRegimeHolds Rg d s D₂.M D₂.invβ ν₀ →
      D₁.M = D₂.M → D₁.V = D₂.V → ∀ δ : ℝ, 0 ≤ δ →
      (∀ r ∈ Icc (0 : ℝ) T, coeffNormE d s m (μ₁ r - μ₂ r) ≤ ENNReal.ofReal δ) →
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ φ : Euc d → ℝ, ulocNormE (m + 2) χ φ < ⊤ →
      ∃ a₁ : ApproximationSequence (d := d) χ (m + 2) (D₁.coeff μ₁) t φ
          (rdProfile Rg C' ν₀ s (m + 2) χ φ),
      ∃ a₂ : ApproximationSequence (d := d) χ (m + 2) (D₂.coeff μ₂) t φ
          (rdProfile Rg C' ν₀ s (m + 2) χ φ),
      ∀ n, ∀ τ ∈ Icc (0 : ℝ) t,
        ulocNormE m χ (fun x => a₁.F n τ x - a₂.F n τ x) ≤
          ENNReal.ofReal (C * τ * Real.exp (Rg.lambdaM C' ν₀ (PDE.thetaOrder d s) * τ) *
            (|D₁.invβ - D₂.invβ| + δ)) * ulocNormE (m + 2) χ φ ∧
        varpiNormE m χ (fun x => a₁.F n τ x - a₂.F n τ x) ≤
          ENNReal.ofReal (C * τ * Real.exp (Rg.lambdaM C' ν₀ (PDE.thetaOrder d s) * τ) *
            (|D₁.invβ - D₂.invβ| + δ)) * varpiNormE (m + 2) χ φ

-- BEGIN SA12.S8
theorem adjoint_rd_stability_of_sequence (hS6 : PairedApproxSeqStatement) :
    type_of% @HRS.Whole.AppendixA.adjoint_rd_stability := by
  intro d hd s hs0 hsd m hm Rg MB Λ ΛV G₀ νbar T χ hχ
  obtain ⟨C,C',hC,hC',hseq⟩ := hS6 hd s hs0 hsd m hm Rg MB Λ ΛV G₀ νbar T χ hχ
  refine ⟨C,C',hC,hC',?_⟩
  intro D₁ D₂ ν₀ μ₁ μ₂ hD₁ hD₂ hR₁ hR₂ hM hV δ hδ hdist t ht φ hφ F₁ F₂ hF₁ hF₂
  obtain ⟨a₁,a₂,ha⟩ := hseq D₁ D₂ ν₀ μ₁ μ₂ hD₁ hD₂ hR₁ hR₂ hM hV δ hδ hdist t ht φ hφ
  exact paired_limit_bounds hd s hs0 hsd m hm Rg MB Λ ΛV G₀ νbar T χ hχ
    D₁ D₂ ν₀ μ₁ μ₂ hD₁ hD₂ hR₁ hR₂ t ht φ hφ
    (rdProfile Rg C' ν₀ s (m+2) χ φ) (rdProfile Rg C' ν₀ s (m+2) χ φ) a₁ a₂
    (fun τ => ENNReal.ofReal (C*τ*Real.exp (Rg.lambdaM C' ν₀ (PDE.thetaOrder d s)*τ)*
      (|D₁.invβ-D₂.invβ|+δ))*ulocNormE (m+2) χ φ)
    (fun τ => ENNReal.ofReal (C*τ*Real.exp (Rg.lambdaM C' ν₀ (PDE.thetaOrder d s)*τ)*
      (|D₁.invβ-D₂.invβ|+δ))*varpiNormE (m+2) χ φ)
    ha F₁ F₂ hF₁ hF₂
-- END SA12.S8

end HRS.MH.AdjointRd.Phase2SA12Stability
