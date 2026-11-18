import HRS.MS.R26T8AW4
import HRS.MS.R26T8AZ8

/-!
# S8.2 T8A W5 (= P16 same-k): `r26t8a_defect_half_order_same`, the Pro contract verbatim for every `σ < d`
Canonical part: Z8; conormal part: W4.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_defect_half_order_same (d : ℕ) (hd : 2 ≤ d) (k : ℕ)
    (a beta M sigma : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (hM : 0 ≤ M) (hsigma : sigma < d)
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
  obtain ⟨C, hC0, hC⟩ := r26t8a_defect_half_order_conormal_same d hd k a beta M sigma ha hbeta hM hsigma chi hchi
  exact ⟨C, hC0, fun rho hrho F A hA hFc hF =>
    ⟨r26t8a_defect_canonical_same d hd a beta M sigma ha hbeta hM hsigma chi hchi rho hrho F A hA hFc
      (r26t8a_conormal_mono (by omega : 2 ≤ k + 2) hF),
      hC rho hrho F A hA hF⟩⟩

end HRS.MS.R26T8A
