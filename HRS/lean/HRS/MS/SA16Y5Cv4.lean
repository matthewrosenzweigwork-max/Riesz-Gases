import HRS.MS.SA16Y5Cv3

/-!
# S.A.16 (SA16Y5) Cv4: partial derivatives of convolutions with `C_c^∞` functions (K2/K3)

`sa16y5_cv_pd`: `∂^idx (k ⋆ φ) = k ⋆ ∂^idx φ` for a locally integrable kernel `k` and `φ ∈ C_c^∞`.
`sa16y5_cv_cv_eq`: `k₁ ⋆ (k₂ ⋆ φ) = (k₁ ⋆ k₂) ⋆ φ` as functions;
`sa16y5_cv_cv_contDiff`: it is smooth; `sa16y5_pd_cv_cv`: `∂^idx (k₁ ⋆ (k₂ ⋆ φ)) = k₁ ⋆ (k₂ ⋆ ∂^idx φ)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Cv4
variable {d : ℕ}

lemma sa16y5_cv_pd {k φ : Euc d → ℝ} (hk : LocallyIntegrable k volume) (hφ : IsCcInfty φ) :
    ∀ (j : ℕ) (idx : Fin j → Fin d), partialDeriv idx (sa16r_cv k φ) = sa16r_cv k (partialDeriv idx φ) := by
  intro j
  induction j with
  | zero =>
    intro idx
    funext x
    rw [sa16j_pd_zero]
    unfold sa16r_cv
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [sa16j_pd_zero]
  | succ j ih =>
    intro idx
    obtain ⟨i, idx', rfl⟩ : ∃ (i : Fin d) (idx' : Fin j → Fin d), idx = Fin.cons i idx' :=
      ⟨idx 0, Fin.tail idx, (Fin.cons_self_tail idx).symm⟩
    funext x
    rw [sa16s_pd_cons (sa16y5_cv_cc_contDiff hk hφ) i idx' x, ih idx',
      sa16y5_cv_fderiv hk (sa16s_cc_partialDeriv hφ idx') x]
    unfold sa16r_cv
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [sa16s_pd_cons hφ.1 i idx']

lemma sa16y5_cv_cv_eq {k₁ k₂ φ : Euc d → ℝ} (h1 : Integrable k₁) (h2 : Integrable k₂) (hφ : IsCcInfty φ) :
    sa16r_cv k₁ (sa16r_cv k₂ φ) = sa16r_cv (sa16r_cv k₁ k₂) φ :=
  funext (sa16y5_cv_assoc h1 h2 hφ)

lemma sa16y5_cv_cv_contDiff {k₁ k₂ φ : Euc d → ℝ} (h1 : Integrable k₁) (h2 : Integrable k₂)
    (hφ : IsCcInfty φ) : ContDiff ℝ ∞ (sa16r_cv k₁ (sa16r_cv k₂ φ)) := by
  rw [sa16y5_cv_cv_eq h1 h2 hφ]
  exact sa16y5_cv_cc_contDiff (sa16y5_cv_locInt h1 h2).locallyIntegrable hφ

lemma sa16y5_pd_cv_cv {k₁ k₂ φ : Euc d → ℝ} (h1 : Integrable k₁) (h2 : Integrable k₂) (hφ : IsCcInfty φ)
    {j : ℕ} (idx : Fin j → Fin d) :
    partialDeriv idx (sa16r_cv k₁ (sa16r_cv k₂ φ)) = sa16r_cv k₁ (sa16r_cv k₂ (partialDeriv idx φ)) := by
  rw [sa16y5_cv_cv_eq h1 h2 hφ, sa16y5_cv_pd (sa16y5_cv_locInt h1 h2).locallyIntegrable hφ j idx,
    ← sa16y5_cv_cv_eq h1 h2 (sa16s_cc_partialDeriv hφ idx)]

end Cv4

end HRS.Whole.AppendixA.Phase2SA16R
