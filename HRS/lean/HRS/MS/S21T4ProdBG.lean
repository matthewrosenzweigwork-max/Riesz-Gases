import HRS.MS.S21T4ProdBF
import HRS.MS.S21T4ProdAY
import HRS.MS.R2ChaosAux6

/-!
# R26-T3.S13: Wick coefficients of a finite kernel family

The coefficients of the orthogonal quadratic chaos commute with arbitrary
finite linear combinations of symmetric L² kernels, with the integrability
needed to interchange the sum and the product-measure integral.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos

variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_wick_coeff_family_linear {m : ℕ}
    (a : ℕ → Euc d → ℝ) (ha : ∀ i, IsR2Test (a i))
    (h : Fin m → Euc d → Euc d → ℝ)
    (hh : ∀ k, S94KOK μ (h k)) (α : Fin m → ℝ)
    (i j : ℕ) :
    r2WickCoeff μ a (fun x y => ∑ k, α k * h k x y) i j =
      ∑ k : Fin m, α k * r2WickCoeff μ a (h k) i j := by
  let g : Euc d × Euc d → ℝ := s94E2 μ a (i, j)
  obtain ⟨C, hC⟩ := s94E2_bounded (μ := μ) ha (i, j)
  have hgi : ∀ k : Fin m, Integrable
      (fun q : Euc d × Euc d => α k * (h k q.1 q.2 * g q)) (μ.prod μ) := by
    intro k
    exact (s94_integrable_k_mul μ (hh k).memLp
      (s94E2_measurable ha (i, j)) hC).const_mul _
  have hsum := s21t4_kernel_family_KOK h hh α
  rw [s94_coeff_eq_prod ha hsum.meas hsum.memLp]
  have hpt : (fun q : Euc d × Euc d =>
      (∑ k : Fin m, α k * h k q.1 q.2) * g q) =
      (fun q : Euc d × Euc d =>
        ∑ k : Fin m, α k * (h k q.1 q.2 * g q)) := by
    funext q
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  change (∫ q, (∑ k : Fin m, α k * h k q.1 q.2) * g q ∂(μ.prod μ)) = _
  rw [hpt]
  rw [integral_finset_sum _ fun k _ => hgi k]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_const_mul]
  rw [s94_coeff_eq_prod ha (hh k).meas (hh k).memLp]

end HRS.MS.R26T3
