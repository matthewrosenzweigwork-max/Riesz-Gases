import HRS.MS.S21G2_S12D
import HRS.MS.S21G2_J08

/-!
# S21G2 S12 (part E) -- closed formula for the statistic `(ζ^f, N 𝖥_N)` (R26-T3.S12)

`pair (empirical X) φ = N⁻¹ ∑ φ(X_k)` for every `φ`; `r2EmpDistr = (√N)⁻¹ ∑ projMean`; and, by J08, the pair statistic is
`½ ∑∑ c ζ^u ζ^u - ½ N⁻¹ ∑ diag(X_k)`.  Helpers `s21g2_s12_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

theorem s21g2_s12_pair_emp {d N : ℕ} (X : HRS.Whole.EucConfig d N) (φ : HRS.Euc d → ℝ) :
    HRS.Whole.pair (HRS.Whole.empirical X) φ = (N : ℝ)⁻¹ * ∑ i, φ (X i) := by
  unfold HRS.Whole.pair HRS.Whole.empirical
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac]
  · intro i _
    exact integrable_dirac enorm_lt_top

theorem s21g2_s12_emp_proj {d M : ℕ} (hM : 0 < M) (μ : Measure (HRS.Euc d)) [IsProbabilityMeasure μ]
    (X : HRS.Whole.EucConfig d M) (φ : HRS.Euc d → ℝ) (hφ : Integrable φ μ) :
    HRS.Whole.r2EmpDistr μ X φ = (Real.sqrt M)⁻¹ * ∑ k, HRS.Whole.projMean μ φ (X k) := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hs : Real.sqrt M ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hM)).ne'
  unfold HRS.Whole.r2EmpDistr
  rw [s21g2_s12_pair_emp]
  simp only [HRS.Whole.projMean, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hsq : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt (Nat.cast_nonneg M)
  set s := Real.sqrt M with hsdef
  have hMs : (M : ℝ) = s * s := hsq.symm
  clear_value s
  rw [hMs] at hM' ⊢
  field_simp

/-- The statistic `(ζ^f, N 𝖥_N)`. -/
def s21g2_s12_Fhat {d n m : ℕ} (μ : MeasureTheory.Measure (HRS.Euc d)) (f : Fin n → HRS.Euc d → ℝ)
    (c : Fin m → Fin m → ℝ) (u : Fin m → HRS.Euc d → ℝ) (M : ℕ) (X : HRS.Whole.EucConfig d M) :
    (Fin n → ℝ) × ℝ :=
  (fun i => HRS.Whole.r2EmpDistr μ X (f i),
    (M : ℝ) * HRS.Whole.pairEnergy (HRS.Whole.r2FiniteRankKernel c u) X μ)

theorem s21g2_s12_Fhat_formula {d n m M : ℕ} (hM : 0 < M) (μ : Measure (HRS.Euc d)) [IsProbabilityMeasure μ]
    {f : Fin n → HRS.Euc d → ℝ} (hf : ∀ i, Integrable (f i) μ) {c : Fin m → Fin m → ℝ}
    (hc : ∀ i j, c i j = c j i) {u : Fin m → HRS.Euc d → ℝ} (hu : ∀ i, HRS.Whole.IsR2Test (u i))
    (X : HRS.Whole.EucConfig d M) :
    s21g2_s12_Fhat μ f c u M X =
      (fun i => (Real.sqrt M)⁻¹ * ∑ k, HRS.Whole.projMean μ (f i) (X k),
       (1 / 2) * ∑ i, ∑ j, c i j * ((Real.sqrt M)⁻¹ * ∑ k, HRS.Whole.projMean μ (u i) (X k)) *
          ((Real.sqrt M)⁻¹ * ∑ k, HRS.Whole.projMean μ (u j) (X k)) -
        (1 / 2) * ((M : ℝ)⁻¹ * ∑ k, HRS.Whole.r2FiniteRankKernel c u (X k) (X k))) := by
  have huI : ∀ i, Integrable (u i) μ := fun i =>
    ((hu i).1.continuous.integrable_of_hasCompactSupport (hu i).2)
  have hdc : Continuous fun x : HRS.Euc d => HRS.Whole.r2FiniteRankKernel c u x x := by
    unfold HRS.Whole.r2FiniteRankKernel
    exact continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ =>
      ((continuous_const.mul (hu a).1.continuous).mul (hu b).1.continuous)
  have hJ := r26t3_finite_rank_pair hM μ X c hc u hu
  refine Prod.ext ?_ ?_
  · funext i
    exact s21g2_s12_emp_proj hM μ X (f i) (hf i)
  · show (M : ℝ) * HRS.Whole.pairEnergy (HRS.Whole.r2FiniteRankKernel c u) X μ = _
    rw [hJ, s21g2_s12_pair_emp]
    simp only [s21g2_s12_emp_proj hM μ X _ (huI _)]

theorem s21g2_s12_Fhat_measurable {d n m M : ℕ} (hM : 0 < M) (μ : Measure (HRS.Euc d)) [IsProbabilityMeasure μ]
    {f : Fin n → HRS.Euc d → ℝ} (hfm : ∀ i, Measurable (f i)) (hf : ∀ i, Integrable (f i) μ)
    {c : Fin m → Fin m → ℝ} (hc : ∀ i j, c i j = c j i) {u : Fin m → HRS.Euc d → ℝ}
    (hu : ∀ i, HRS.Whole.IsR2Test (u i)) :
    Measurable (s21g2_s12_Fhat μ f c u M) := by
  have hpm : ∀ (g : HRS.Euc d → ℝ), Measurable g → ∀ k : Fin M,
      Measurable fun X : HRS.Whole.EucConfig d M => HRS.Whole.projMean μ g (X k) := fun g hg k =>
    (hg.sub measurable_const).comp (measurable_pi_apply k)
  have hdm : ∀ k : Fin M, Measurable fun X : HRS.Whole.EucConfig d M =>
      HRS.Whole.r2FiniteRankKernel c u (X k) (X k) := fun k => by
    unfold HRS.Whole.r2FiniteRankKernel
    exact Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ =>
      (measurable_const.mul ((hu a).1.continuous.measurable.comp (measurable_pi_apply k))).mul
        ((hu b).1.continuous.measurable.comp (measurable_pi_apply k))
  have hform : s21g2_s12_Fhat μ f c u M = fun X => (fun i => (Real.sqrt M)⁻¹ *
      ∑ k, HRS.Whole.projMean μ (f i) (X k),
      (1 / 2) * ∑ i, ∑ j, c i j * ((Real.sqrt M)⁻¹ * ∑ k, HRS.Whole.projMean μ (u i) (X k)) *
          ((Real.sqrt M)⁻¹ * ∑ k, HRS.Whole.projMean μ (u j) (X k)) -
        (1 / 2) * ((M : ℝ)⁻¹ * ∑ k, HRS.Whole.r2FiniteRankKernel c u (X k) (X k))) :=
    funext fun X => s21g2_s12_Fhat_formula hM μ hf hc hu X
  rw [hform]
  have hsu : ∀ i, Measurable fun X : HRS.Whole.EucConfig d M =>
      (Real.sqrt M)⁻¹ * ∑ k, HRS.Whole.projMean μ (u i) (X k) := fun i =>
    measurable_const.mul (Finset.measurable_sum _ fun k _ => hpm _ (hu i).1.continuous.measurable k)
  refine Measurable.prodMk (measurable_pi_iff.2 fun i =>
    measurable_const.mul (Finset.measurable_sum _ fun k _ => hpm _ (hfm i) k)) ?_
  exact (measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    (measurable_const.mul (hsu i)).mul (hsu j))).sub
    (measurable_const.mul (measurable_const.mul (Finset.measurable_sum _ fun k _ => hdm k)))

end HRS.MS.R26T3
