import HRS.Whole.Round2

/-!
# S21G2 J08 -- exact finite-rank pair identity including the deleted diagonal (R26-T3.J08)

`N * pairEnergy (r2FiniteRankKernel c f) X μ = 1/2 ∑∑ c_ij ζ_i ζ_j - 1/2 pair (empirical X) (diag)`,
with `ζ_i = r2EmpDistr μ X (f i)`.  The frozen-skeleton contract has no symmetry hypothesis on `c`; it is
FALSE for non-symmetric `c` (the middle term of `pairEnergy` only integrates the second slot), so
`hc : ∀ i j, c i j = c j i` is added (minimal fix, satisfied by the consumer J11: Hilbert-Schmidt kernels).
Helper names carry the prefix `s21g2_j08_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace HRS.MS.R26T3

private lemma s21g2_j08_pair_emp {d N : ℕ} (X : HRS.Whole.EucConfig d N) {g : Euc d → ℝ}
    (hg : Continuous g) :
    HRS.Whole.pair (HRS.Whole.empirical X) g = (N : ℝ)⁻¹ * ∑ i, g (X i) := by
  unfold HRS.Whole.pair HRS.Whole.empirical
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac' _ _ hg.measurable.stronglyMeasurable]
  · intro i _
    exact integrable_dirac enorm_lt_top

private lemma s21g2_j08_int {d : ℕ} (μ : Measure (Euc d)) [IsProbabilityMeasure μ] {g : Euc d → ℝ}
    (hg : HRS.Whole.IsR2Test g) : Integrable g μ :=
  (hg.1.continuous.integrable_of_hasCompactSupport hg.2)

theorem r26t3_finite_rank_pair {d N k : ℕ} (hN : 0<N)
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (X : HRS.Whole.EucConfig d N)
    (c : Fin k → Fin k → ℝ) (hc : ∀ i j, c i j = c j i) (f : Fin k → Euc d → ℝ)
    (hf : ∀ i, HRS.Whole.IsR2Test (f i)) :
    (N : ℝ)*HRS.Whole.pairEnergy (HRS.Whole.r2FiniteRankKernel c f) X μ=
      (1/2)*∑ i, ∑ j, c i j*HRS.Whole.r2EmpDistr μ X (f i)*HRS.Whole.r2EmpDistr μ X (f j)-
        (1/2)*HRS.Whole.pair (HRS.Whole.empirical X)
          (fun x => HRS.Whole.r2FiniteRankKernel c f x x) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  set m : Fin k → ℝ := fun a => (N : ℝ)⁻¹ * ∑ i, f a (X i) with hm
  set ν : Fin k → ℝ := fun a => ∫ x, f a x ∂μ with hν
  have hcont : ∀ a, Continuous (f a) := fun a => (hf a).1.continuous
  have hpm : ∀ a, HRS.Whole.pair (HRS.Whole.empirical X) (f a) = m a :=
    fun a => s21g2_j08_pair_emp X (hcont a)
  have hsm : ∀ a, ∑ i, f a (X i) = N * m a := fun a => by
    simp only [hm]; field_simp
  have key : ∀ F : Fin N → Fin N → Fin k → Fin k → ℝ,
      ∑ i, ∑ j, ∑ a, ∑ b, F i j a b = ∑ a, ∑ b, ∑ i, ∑ j, F i j a b := fun F => by
    calc ∑ i, ∑ j, ∑ a, ∑ b, F i j a b = ∑ i, ∑ a, ∑ j, ∑ b, F i j a b :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ a, ∑ i, ∑ j, ∑ b, F i j a b := Finset.sum_comm
      _ = ∑ a, ∑ i, ∑ b, ∑ j, F i j a b :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ i, ∑ j, F i j a b := Finset.sum_congr rfl fun a _ => Finset.sum_comm
  have h1 : ∑ i, ∑ j, HRS.Whole.r2FiniteRankKernel c f (X i) (X j) =
      (N : ℝ) ^ 2 * ∑ a, ∑ b, c a b * m a * m b := by
    unfold HRS.Whole.r2FiniteRankKernel
    rw [key (fun i j a b => c a b * f a (X i) * f b (X j)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have : ∑ i, ∑ j, c a b * f a (X i) * f b (X j) =
        c a b * (∑ i, f a (X i)) * ∑ j, f b (X j) := by
      rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, hsm, hsm]; ring
  have hI : ∀ x, ∫ y, HRS.Whole.r2FiniteRankKernel c f x y ∂μ =
      ∑ a, ∑ b, c a b * f a x * ν b := fun x => by
    unfold HRS.Whole.r2FiniteRankKernel
    rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ =>
      ((s21g2_j08_int μ (hf b)).const_mul (c a b * f a x)))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ (fun b _ => (s21g2_j08_int μ (hf b)).const_mul (c a b * f a x))]
    exact Finset.sum_congr rfl fun b _ => by rw [integral_const_mul]
  have h2 : ∑ i, ∫ y, HRS.Whole.r2FiniteRankKernel c f (X i) y ∂μ =
      N * ∑ a, ∑ b, c a b * m a * ν b := by
    simp only [hI]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have : ∑ i, c a b * f a (X i) * ν b = (c a b * ν b) * ∑ i, f a (X i) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hsm]; ring
  have h3 : ∫ x, ∫ y, HRS.Whole.r2FiniteRankKernel c f x y ∂μ ∂μ =
      ∑ a, ∑ b, c a b * ν a * ν b := by
    simp only [hI]
    rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ =>
      ((s21g2_j08_int μ (hf a)).const_mul (c a b * ν b)) |>.congr
        (Filter.Eventually.of_forall fun x => by simp [mul_comm, mul_left_comm, mul_assoc]))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ (fun b _ => ((s21g2_j08_int μ (hf a)).const_mul (c a b * ν b)) |>.congr
        (Filter.Eventually.of_forall fun x => by simp [mul_comm, mul_left_comm, mul_assoc]))]
    refine Finset.sum_congr rfl fun b _ => ?_
    have : (fun x => c a b * f a x * ν b) = fun x => (c a b * ν b) * f a x := by
      ext x; ring
    rw [this, integral_const_mul]; simp only [hν]; ring
  have hdc : Continuous fun x => HRS.Whole.r2FiniteRankKernel c f x x := by
    unfold HRS.Whole.r2FiniteRankKernel
    exact continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ =>
      ((continuous_const.mul (hcont a)).mul (hcont b))
  have hdiag := s21g2_j08_pair_emp X hdc
  have hQ : ∑ a, ∑ b, c a b * ν a * m b = ∑ a, ∑ b, c a b * m a * ν b := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by rw [hc a b]; ring
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
  have hE : ∀ a, HRS.Whole.r2EmpDistr μ X (f a) = Real.sqrt N * (m a - ν a) := fun a => by
    unfold HRS.Whole.r2EmpDistr
    rw [hpm a]; rfl
  have hexp : ∑ a, ∑ b, c a b * HRS.Whole.r2EmpDistr μ X (f a) * HRS.Whole.r2EmpDistr μ X (f b) =
      N * ((∑ a, ∑ b, c a b * m a * m b) - 2 * (∑ a, ∑ b, c a b * m a * ν b) +
        ∑ a, ∑ b, c a b * ν a * ν b) := by
    have : ∀ a b, c a b * HRS.Whole.r2EmpDistr μ X (f a) * HRS.Whole.r2EmpDistr μ X (f b) =
        N * (c a b * m a * m b) - N * (c a b * m a * ν b) - N * (c a b * ν a * m b) +
          N * (c a b * ν a * ν b) := fun a b => by
      rw [hE a, hE b]
      linear_combination (c a b * (m a - ν a) * (m b - ν b)) * hsq
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hQ]; ring
  have hdd : ∑ i, ∑ j ∈ Finset.univ.erase i, HRS.Whole.r2FiniteRankKernel c f (X i) (X j) =
      (N : ℝ) ^ 2 * ∑ a, ∑ b, c a b * m a * m b -
        ∑ i, HRS.Whole.r2FiniteRankKernel c f (X i) (X i) := by
    rw [← h1, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_erase_eq_sub (Finset.mem_univ i)
  unfold HRS.Whole.pairEnergy
  rw [hdd, h2, h3, hexp, hdiag]
  field_simp
  ring

end HRS.MS.R26T3
