import HRS.MS.R26T8AZ7b
import HRS.MS.R26T8AP10a

/-!
# S8.2 T8A Z7c (= P10 same-k): `r26t8a_newton_potential_ibp_same`
Pro P10 contract verbatim for every `σ < d`, hypothesis `Conormal (k+2) b M σ A F`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_newton_potential_ibp_same (d : ℕ) (hd : 2 ≤ d) (k b : ℕ)
    (a beta M sigma : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (hsd : sigma < d) (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      Conormal (k + 2) b M sigma A F →
      let Q := localNewton (HRS.Whole.withDensityReal rho) beta⁻¹ chi F
      ∀ x y, x ≠ y → Integrable (fun z => rieszKernel d (criticalS d) (x - z) *
        (rho z * Laplacian.laplacian (fun w => Q w y) z + inner ℝ (gradient rho z) (pairGradX Q z y))) ∧
        oneJ (critCoeff d a beta rho) (fun w => Q w y) x =
          ∫ z, rieszKernel d (criticalS d) (x - z) *
            (rho z * Laplacian.laplacian (fun w => Q w y) z + inner ℝ (gradient rho z) (pairGradX Q z y)) := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_local_newton_bound_same d hd (k + 2) b a beta M sigma ha hbeta hM hsd chi hchi
  intro rho hrho F A hA hF
  obtain ⟨-, -, hQ⟩ := hC rho hrho F A hA hF
  exact r26t8a_conormal_potential_ibp d hd k (b + 1) a beta M sigma ha hbeta hM hsd rho hrho _ (C * A)
    (mul_nonneg hC0 hA) hQ

end HRS.MS.R26T8A
