import HRS.MS.S21T4ProdAW

/-! S13: pointwise linearity of the actual finite-family pair energy for integrable kernels. -/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_pairEnergy_family_linear {N m : ℕ}
    (h : Fin m → Euc d → Euc d → ℝ) (hh : ∀ i, S94KOK μ (h i))
    (α : Fin m → ℝ) (X : EucConfig d N) :
    pairEnergy (fun x y => ∑ k, α k * h k x y) X μ =
      ∑ k : Fin m, α k * pairEnergy (h k) X μ := by
  have hs1 : (∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
      ∑ k : Fin m, α k * h k (X i) (X j)) =
      ∑ k : Fin m, α k *
        (∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, h k (X i) (X j)) := by
    calc
      _ = ∑ i : Fin N, ∑ k : Fin m,
            ∑ j ∈ Finset.univ.erase i, α k * h k (X i) (X j) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.sum_comm
      _ = ∑ k : Fin m, ∑ i : Fin N,
            ∑ j ∈ Finset.univ.erase i, α k * h k (X i) (X j) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
  have hs2 : (∑ i : Fin N, ∫ y,
      (∑ k : Fin m, α k * h k (X i) y) ∂μ) =
      ∑ k : Fin m, α k * (∑ i : Fin N, ∫ y, h k (X i) y ∂μ) := by
    simp_rw [s21t4_kernel_family_row_integral h hh α]
    calc
      _ = ∑ k : Fin m, ∑ i : Fin N, α k * ∫ y, h k (X i) y ∂μ :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mul_sum]
  have hs3 := s21t4_kernel_family_double_integral h hh α
  unfold pairEnergy
  simp_rw [hs1, hs2, hs3]
  simp only [Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    mul_add, mul_sub, mul_assoc]
  ring_nf

end HRS.MS.R26T3
