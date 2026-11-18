import HRS.MS.R26T8AP16f

/-!
# S8.2 T8A P16 (Pro contract): `r26t8a_defect_half_order_nonneg` and the corrected `_full`
Canonical part: P16f; conormal part: P16b.  `_full` has the corrected regularity `Conormal (rawGainReg (gainReg k σ + 2) σ) 0 M σ A F`
(for `σ ≥ 0` this is the Pro hypothesis `Conormal (k+2) 0 M σ A F`); `_nonneg` is the Pro contract verbatim plus `0 ≤ σ`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_defect_half_order_full (d : ℕ) (hd : 2 ≤ d) (k : ℕ)
    (a beta M sigma : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (hM : 0 ≤ M) (hsigma : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      CanonicalPair (HRS.Whole.withDensityReal rho) F →
      Conormal (r26t8a_rawGainReg (r26t8a_gainReg k sigma + 2) sigma) 0 M sigma A F →
      CanonicalPair (HRS.Whole.withDensityReal rho)
        (newtonDefect (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi F) ∧
      Conormal k 0 (M + 2) (sigma - 1 / 2) (C * A)
        (newtonDefect (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi F) := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_defect_half_order_conormal_full d hd k a beta M sigma ha hbeta hM hsigma chi hchi
  exact ⟨C, hC0, fun rho hrho F A hA hFc hF =>
    ⟨r26t8a_defect_canonical_full d hd k a beta M sigma ha hbeta hM hsigma chi hchi rho hrho F A hA hFc hF,
      hC rho hrho F A hA hF⟩⟩

theorem r26t8a_defect_half_order_nonneg (d : ℕ) (hd : 2 ≤ d) (k : ℕ)
    (a beta M sigma : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (hM : 0 ≤ M) (hσ : 0 ≤ sigma) (hsigma : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      CanonicalPair (HRS.Whole.withDensityReal rho) F →
      Conormal (k + 2) 0 M sigma A F →
      CanonicalPair (HRS.Whole.withDensityReal rho)
        (newtonDefect (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi F) ∧
      Conormal k 0 (M + 2) (sigma - 1 / 2) (C * A)
        (newtonDefect (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi F) := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_defect_half_order_full d hd k a beta M sigma ha hbeta hM hsigma chi hchi
  refine ⟨C, hC0, fun rho hrho F A hA hFc hF => hC rho hrho F A hA hFc ?_⟩
  simpa only [r26t8a_gainReg, r26t8a_rawGainReg, if_pos hσ] using hF

end HRS.MS.R26T8A
