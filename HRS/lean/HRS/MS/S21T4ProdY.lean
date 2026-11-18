import HRS.MS.S21T4ProdX

/-! The exact S9.1 smooth symmetric finite-rank kernels lie in L²(μ⊗μ). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_finite_rank_memLp {m : ℕ}
    (c : Fin m → Fin m → ℝ) (u : Fin m → Euc d → ℝ)
    (hu : IsR2FiniteRankData c u) :
    MemLp (fun z : Euc d × Euc d => r2FiniteRankKernel c u z.1 z.2) 2
      (μ.prod μ) := by
  have hm : ∀ a : Fin m, MemLp (u a) 2 μ := fun a =>
    (hu.smooth a).continuous.memLp_of_hasCompactSupport (hu.compactSupport a)
  unfold r2FiniteRankKernel
  exact memLp_finsetSum _ fun a _ =>
    memLp_finsetSum _ fun b _ =>
      by simpa only [mul_assoc] using (s21t4_separated_kernel_memLp (u a) (u b) (hm a) (hm b)).const_mul (c a b)

theorem s21t4_finite_rank_symmetric {m : ℕ}
    (c : Fin m → Fin m → ℝ) (u : Fin m → Euc d → ℝ)
    (hu : IsR2FiniteRankData c u) (x y : Euc d) :
    r2FiniteRankKernel c u x y = r2FiniteRankKernel c u y x := by
  unfold r2FiniteRankKernel
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  rw [hu.symm b a]
  ring

end HRS.MS.R26T3
