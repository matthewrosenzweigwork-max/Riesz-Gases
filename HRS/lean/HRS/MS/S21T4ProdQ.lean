import HRS.MS.S21T4ProdP

/-! Exact finite-dimensional covariance of the product Gaussian field. -/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

/-- Finite-dimensional polarization of the Bochner integral for arbitrary L² fields. -/
theorem s21t4_expand_integral {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (u : Fin n → Ω → ℝ) (hu : ∀ i, MemLp (u i) 2 P)
    (α β : Fin n → ℝ) :
    (∫ ω, (∑ i : Fin n, α i * u i ω) * (∑ j : Fin n, β j * u j ω) ∂P) =
    ∑ i : Fin n, ∑ j : Fin n, α i * β j * (∫ ω, u i ω * u j ω ∂P) := by
  have hterm : ∀ i j : Fin n, Integrable
      (fun ω => α i * β j * (u i ω * u j ω)) P := fun i j =>
    ((hu i).integrable_mul (hu j)).const_mul _
  have heq : ∀ ω,
     (∑ i : Fin n, α i * u i ω) * (∑ j : Fin n, β j * u j ω) =
      ∑ i : Fin n, ∑ j : Fin n, α i * β j * (u i ω * u j ω) := by
    intro ω
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [heq]
  rw [integral_finset_sum _ fun i _ =>
    integrable_finset_sum _ fun j _ => hterm i j]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finset_sum _ fun j _ => hterm i j]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul]

/-- Polarization of the canonical Gaussian covariance for arbitrary finite
families of L² reference tests, with no change of probability space. -/
theorem s21t4_product_finite_covariance (I : ProductGaussian μ) {n : ℕ}
    (f : Fin n → Euc d → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (α β : Fin n → ℝ) :
    (∫ ω, (∑ i : Fin n, α i * I.η (f i) ω) *
        (∑ j : Fin n, β j * I.η (f j) ω) ∂I.P) =
      (∫ x, (∑ i : Fin n, α i * HRS.Whole.projMean μ (f i) x) *
        (∑ j : Fin n, β j * HRS.Whole.projMean μ (f j) x) ∂μ) := by
  letI := I.mΩ
  letI := I.prob
  have hη : ∀ i, MemLp (I.η (f i)) 2 I.P :=
    fun i => s21t4_eta_memLp I (f i) (hf i)
  have hpm : ∀ i, MemLp (HRS.Whole.projMean μ (f i)) 2 μ :=
    fun i => (hf i).sub (memLp_const _)
  have hcov : ∀ i j : Fin n, (∫ ω, I.η (f i) ω * I.η (f j) ω ∂I.P) =
      (∫ x, HRS.Whole.projMean μ (f i) x * HRS.Whole.projMean μ (f j) x ∂μ) :=
    fun i j => I.covariance (f i) (f j) (hf i) (hf j)
  calc
    _ = ∑ i : Fin n, ∑ j : Fin n, α i * β j *
        (∫ ω, I.η (f i) ω * I.η (f j) ω ∂I.P) :=
          s21t4_expand_integral I.P (fun i => I.η (f i)) hη α β
    _ = ∑ i : Fin n, ∑ j : Fin n, α i * β j *
        (∫ x, HRS.Whole.projMean μ (f i) x *
          HRS.Whole.projMean μ (f j) x ∂μ) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [hcov i j]
    _ = _ := (s21t4_expand_integral μ (fun i => HRS.Whole.projMean μ (f i)) hpm α β).symm

end HRS.MS.R26T3
