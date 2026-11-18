import HRS.MS.S21T4ProdAS

/-! S13: finite families of smooth finite-rank kernels with a shared test basis. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole
variable {d : ℕ}

/-- A linear combination of symmetric finite-rank matrices with common smooth
compact test functions remains in the same admissible class. -/
theorem s21t4_finite_rank_matrix_combination {r m : ℕ}
    (c : Fin r → Fin m → Fin m → ℝ) (u : Fin m → Euc d → ℝ)
    (hu : ∀ i, IsR2Test (u i))
    (hc : ∀ k i j, c k i j = c k j i) (α : Fin r → ℝ) :
    IsR2FiniteRankData (fun i j => ∑ k, α k * c k i j) u := by
  refine ⟨?_, (fun i => (hu i).1), (fun i => (hu i).2)⟩
  intro i j
  simp_rw [hc]

/-- A linear combination of the finite-rank kernels agrees pointwise with the
finite-rank kernel of the combined coefficient matrix. -/
theorem s21t4_finite_rank_kernel_combination {r m : ℕ}
    (c : Fin r → Fin m → Fin m → ℝ) (u : Fin m → Euc d → ℝ)
    (α : Fin r → ℝ) (x y : Euc d) :
    r2FiniteRankKernel (fun i j => ∑ k, α k * c k i j) u x y =
      ∑ k, α k * r2FiniteRankKernel (c k) u x y := by
  unfold r2FiniteRankKernel
  calc
    (∑ i : Fin m, ∑ j : Fin m,
      (∑ k : Fin r, α k * c k i j) * u i x * u j y) =
      ∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin r,
        α k * (c k i j * u i x * u j y) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ i : Fin m, ∑ k : Fin r, ∑ j : Fin m,
        α k * (c k i j * u i x * u j y) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ k : Fin r, ∑ i : Fin m, ∑ j : Fin m,
        α k * (c k i j * u i x * u j y) := Finset.sum_comm
    _ = ∑ k : Fin r, α k *
        (∑ i : Fin m, ∑ j : Fin m, c k i j * u i x * u j y) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]

end HRS.MS.R26T3
