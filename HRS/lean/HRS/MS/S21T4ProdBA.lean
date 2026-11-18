import HRS.MS.S21T4ProdAZ

/-!
# R26-T3.S13: finite families of Gaussian quadratic polynomials

For a common finite collection of Gaussian coordinates, forming a scalar
linear combination of symmetric coefficient matrices commutes exactly with
forming the corresponding half-Wick quadratic polynomial. This is the
limit-side counterpart of `s21t4_pairEnergy_family_linear`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole

theorem s21t4_finite_rank_polynomial_combination {m r : ℕ}
    (c : Fin m → Fin r → Fin r → ℝ) (α : Fin m → ℝ)
    (z : Fin r → ℝ) (v : Fin r → Fin r → ℝ) :
    (1 / 2 : ℝ) * ∑ i : Fin r, ∑ j : Fin r,
      (∑ k : Fin m, α k * c k i j) * (z i * z j - v i j) =
      ∑ k : Fin m, α k *
        ((1 / 2 : ℝ) * ∑ i : Fin r, ∑ j : Fin r,
          c k i j * (z i * z j - v i j)) := by
  calc
    _ = (1 / 2 : ℝ) * ∑ i : Fin r, ∑ j : Fin r, ∑ k : Fin m,
          α k * (c k i j * (z i * z j - v i j)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    _ = (1 / 2 : ℝ) * ∑ k : Fin m, ∑ i : Fin r, ∑ j : Fin r,
          α k * (c k i j * (z i * z j - v i j)) := by
      congr 1
      calc
        _ = ∑ i : Fin r, ∑ k : Fin m, ∑ j : Fin r,
              α k * (c k i j * (z i * z j - v i j)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hsum : (∑ i : Fin r, ∑ j : Fin r,
          α k * (c k i j * (z i * z j - v i j))) =
          α k * (∑ i : Fin r, ∑ j : Fin r,
            c k i j * (z i * z j - v i j)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      rw [hsum]
      ring

end HRS.MS.R26T3
