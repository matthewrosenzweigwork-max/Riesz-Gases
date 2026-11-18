import HRS.MS.R26T8AZ7a

/-!
# S8.2 T8A Z7b (= P09 same-k): `r26t8a_local_newton_bound_same`
The Pro P09 contract verbatim for every `σ < d` (P07 same-k + P08 same-k).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_local_newton_bound_same (d : ℕ) (hd : 2 ≤ d) (k b : ℕ)
    (a beta M sigma : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (hM : 0 ≤ M) (hsigma : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      Conormal k b M sigma A F →
      let mu := HRS.Whole.withDensityReal rho
      (∀ x y, x ≠ y → Integrable (fun z =>
        newtonKernel d beta⁻¹ (x - y - z) * chi z *
          midPair F ((1 / 2 : ℝ) • (x + y)) z)) ∧
      CanonicalPair mu (localNewton mu beta⁻¹ chi F) ∧
      Conormal k (b + 1) M (sigma - 2) (C * A)
        (localNewton mu beta⁻¹ chi F) := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_newton_projection_same d hd k b a beta M sigma ha hbeta hM hsigma chi hchi
  obtain ⟨C1, hC10, hC1⟩ := r26t8a_raw_newton_bound_same d hd k b beta⁻¹ M sigma (inv_pos.2 hbeta) hM
    hsigma chi hchi
  refine ⟨C, hC0, fun rho hrho F A hA hF => ?_⟩
  exact ⟨(hC1 F A hA hF).1, hC rho hrho F A hA hF⟩

end HRS.MS.R26T8A
