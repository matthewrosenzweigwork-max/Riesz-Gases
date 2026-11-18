import HRS.Prob.Gaussian

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory

namespace HRS.Fp81.S21

/-- Fourth-moment control for the difference of two finite quadratic
polynomials in the same standard Gaussian sequence. -/
theorem fp81s21_quadratic_difference_fourth
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : HRS.IsStdGaussianSeq P ξ)
    (c d : ℕ → ℕ → ℝ) (hc : ∀ i j, c i j = c j i)
    (hd : ∀ i j, d i j = d j i) (N : ℕ) :
    Integrable (fun ω => (HRS.quadSum c ξ N ω - HRS.quadSum d ξ N ω) ^ 4) P ∧
    (∫ ω, (HRS.quadSum c ξ N ω - HRS.quadSum d ξ N ω) ^ 4 ∂P) ≤
      15 * (∫ ω, (HRS.quadSum c ξ N ω - HRS.quadSum d ξ N ω) ^ 2 ∂P) ^ 2 := by
  let e : ℕ → ℕ → ℝ := fun i j => c i j - d i j
  have he : ∀ i j, e i j = e j i := fun i j => by simp [e, hc i j, hd i j]
  have hdiff : ∀ ω, HRS.quadSum c ξ N ω - HRS.quadSum d ξ N ω =
      HRS.quadSum e ξ N ω := by
    intro ω
    simp only [HRS.quadSum, e, sub_mul, Finset.sum_sub_distrib]
  have hfour := HRS.quadSum_four hξ e he N
  have htwo := HRS.quadSum_L2 hξ e he N
  rw [HRS.vGauss_eq] at htwo
  simp_rw [hdiff]
  refine ⟨hfour.1, ?_⟩
  rw [htwo]
  nlinarith [hfour.2]

private theorem fp81s21_quadSum_symmetrize
    {Ω : Type*} (ξ : ℕ → Ω → ℝ) (c : ℕ → ℕ → ℝ) (N : ℕ) (ω : Ω) :
    HRS.quadSum (fun i j => (c i j + c j i) / 2) ξ N ω = HRS.quadSum c ξ N ω := by
  classical
  have ht : (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      c j i * (ξ i ω * ξ j ω - if i = j then 1 else 0)) =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        c i j * (ξ i ω * ξ j ω - if i = j then 1 else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp only [mul_comm (ξ j ω) (ξ i ω), eq_comm]
  unfold HRS.quadSum
  have hs : (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      ((c i j + c j i) / 2) * (ξ i ω * ξ j ω - if i = j then 1 else 0)) =
      (1 / 2 : ℝ) * ((∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        c i j * (ξ i ω * ξ j ω - if i = j then 1 else 0)) +
        ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        c j i * (ξ i ω * ξ j ω - if i = j then 1 else 0)) := by
    rw [mul_add]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hs, ht]
  ring

/-- The fourth-moment difference estimate for arbitrary coefficient arrays;
only their symmetric parts contribute to the quadratic polynomials. -/
theorem fp81s21_quadratic_difference_fourth_general
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : HRS.IsStdGaussianSeq P ξ)
    (c d : ℕ → ℕ → ℝ) (N : ℕ) :
    Integrable (fun ω => (HRS.quadSum c ξ N ω - HRS.quadSum d ξ N ω) ^ 4) P ∧
    (∫ ω, (HRS.quadSum c ξ N ω - HRS.quadSum d ξ N ω) ^ 4 ∂P) ≤
      15 * (∫ ω, (HRS.quadSum c ξ N ω - HRS.quadSum d ξ N ω) ^ 2 ∂P) ^ 2 := by
  have h := fp81s21_quadratic_difference_fourth hξ
    (fun i j => (c i j + c j i) / 2) (fun i j => (d i j + d j i) / 2)
    (fun i j => by simp only [add_comm]) (fun i j => by simp only [add_comm]) N
  simpa only [fp81s21_quadSum_symmetrize] using h

#print axioms fp81s21_quadratic_difference_fourth
#print axioms fp81s21_quadratic_difference_fourth_general

end HRS.Fp81.S21
end
