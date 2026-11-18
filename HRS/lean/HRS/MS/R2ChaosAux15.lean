import HRS.MS.R2ChaosAux14

/-!
# HRS.MS.R2ChaosAux15 -- exact expression of `N 𝖥_N^h` for a finite-rank kernel

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

`N 𝖥_N^h(X, μ) = (1/2) ∑ c_ab ξ_a ξ_b - (1/2) μ_N(g)`, `ξ_a = √N (μ_N(u_a) - μ(u_a))`, `g(x) = ∑ c_ab u_a(x) u_b(x)`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

section FRPair

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {m : ℕ} {c : Fin m → Fin m → ℝ} {u : Fin m → Euc d → ℝ}

theorem s94_integral_finiteRank_right (hu : ∀ a, IsR2Test (u a)) (x : Euc d) :
    ∫ y', r2FiniteRankKernel c u x y' ∂μ = ∑ a, ∑ b, c a b * u a x * Whole.pair μ (u b) := by
  unfold r2FiniteRankKernel
  rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ =>
    (s94_test_integrable (hu b) μ).const_mul (c a b * u a x)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finset_sum _ fun b _ => (s94_test_integrable (hu b) μ).const_mul (c a b * u a x)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul]; rfl

theorem s94_integral_finiteRank_both (hu : ∀ a, IsR2Test (u a)) :
    ∫ x', ∫ y', r2FiniteRankKernel c u x' y' ∂μ ∂μ = ∑ a, ∑ b, c a b * Whole.pair μ (u a) * Whole.pair μ (u b) := by
  simp_rw [s94_integral_finiteRank_right hu]
  rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ =>
    ((s94_test_integrable (hu a) μ).const_mul (c a b)).mul_const (Whole.pair μ (u b))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finset_sum _ fun b _ => ((s94_test_integrable (hu a) μ).const_mul (c a b)).mul_const (Whole.pair μ (u b))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_mul_const, integral_const_mul]; rfl

theorem s94_N_pairEnergy_finiteRank (hu : ∀ a, IsR2Test (u a)) (hc : ∀ a b, c a b = c b a) {N : ℕ} (hN : 0 < N)
    (X : EucConfig d N) :
    (N : ℝ) * pairEnergy (r2FiniteRankKernel c u) X μ =
      (1 / 2) * ∑ a, ∑ b, c a b * ((Real.sqrt N * (Whole.pair (Whole.empirical X) (u a) - Whole.pair μ (u a))) *
          (Real.sqrt N * (Whole.pair (Whole.empirical X) (u b) - Whole.pair μ (u b)))) -
        (1 / 2) * Whole.pair (Whole.empirical X) (fun x => ∑ a, ∑ b, c a b * u a x * u b x) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  set Sx : Fin m → ℝ := fun a => ∑ i, u a (X i) with hSx
  set mu : Fin m → ℝ := fun a => Whole.pair μ (u a) with hmu
  set Dx : Fin m → Fin m → ℝ := fun a b => ∑ i, u a (X i) * u b (X i) with hDx
  have hemp : ∀ a, Whole.pair (Whole.empirical X) (u a) = (N : ℝ)⁻¹ * Sx a := fun a => Whole.pair_empirical hN X (u a)
  -- F1
  have hF1a : ∑ i, ∑ j, r2FiniteRankKernel c u (X i) (X j) = ∑ a, ∑ b, c a b * (Sx a * Sx b) := by
    unfold r2FiniteRankKernel
    rw [s94_sum_swap4 (fun i j a b => c a b * u a (X i) * u b (X j))]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hSx, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  have hF1b : ∑ i, r2FiniteRankKernel c u (X i) (X i) = ∑ a, ∑ b, c a b * Dx a b := by
    unfold r2FiniteRankKernel
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hDx, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hF1 : ∑ i, ∑ j ∈ Finset.univ.erase i, r2FiniteRankKernel c u (X i) (X j) =
      ∑ a, ∑ b, c a b * (Sx a * Sx b - Dx a b) := by
    have : ∀ i, ∑ j ∈ Finset.univ.erase i, r2FiniteRankKernel c u (X i) (X j) =
        ∑ j, r2FiniteRankKernel c u (X i) (X j) - r2FiniteRankKernel c u (X i) (X i) :=
      fun i => Finset.sum_erase_eq_sub (Finset.mem_univ i)
    simp_rw [this, Finset.sum_sub_distrib, hF1a, hF1b, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact Finset.sum_congr rfl fun b _ => by ring
  have hF2 : ∑ i, ∫ y, r2FiniteRankKernel c u (X i) y ∂μ = ∑ a, ∑ b, c a b * (Sx a * mu b) := by
    simp_rw [s94_integral_finiteRank_right hu]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hSx, hmu, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hF3 := s94_integral_finiteRank_both (μ := μ) (c := c) hu
  have hswap : ∑ a, ∑ b, c a b * (mu a * Sx b) = ∑ a, ∑ b, c a b * (Sx a * mu b) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hc a b]; ring
  have hg : Whole.pair (Whole.empirical X) (fun x => ∑ a, ∑ b, c a b * u a x * u b x) =
      (N : ℝ)⁻¹ * ∑ a, ∑ b, c a b * Dx a b := by
    rw [Whole.pair_empirical hN, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hDx, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hxi : ∑ a, ∑ b, c a b * ((Real.sqrt N * (Whole.pair (Whole.empirical X) (u a) - Whole.pair μ (u a))) *
          (Real.sqrt N * (Whole.pair (Whole.empirical X) (u b) - Whole.pair μ (u b)))) =
      (N : ℝ)⁻¹ * ∑ a, ∑ b, c a b * (Sx a * Sx b) - ∑ a, ∑ b, c a b * (Sx a * mu b) -
        ∑ a, ∑ b, c a b * (mu a * Sx b) + (N : ℝ) * ∑ a, ∑ b, c a b * (mu a * mu b) := by
    have key : ∀ a b : Fin m, c a b * ((Real.sqrt N * (Whole.pair (Whole.empirical X) (u a) - Whole.pair μ (u a))) *
          (Real.sqrt N * (Whole.pair (Whole.empirical X) (u b) - Whole.pair μ (u b)))) =
        (N : ℝ)⁻¹ * (c a b * (Sx a * Sx b)) - c a b * (Sx a * mu b) - c a b * (mu a * Sx b) +
          (N : ℝ) * (c a b * (mu a * mu b)) := by
      intro a b
      have hs : Real.sqrt N * Real.sqrt N = (N : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg N)
      rw [hemp a, hemp b]
      have e : c a b * ((Real.sqrt N * ((N : ℝ)⁻¹ * Sx a - mu a)) * (Real.sqrt N * ((N : ℝ)⁻¹ * Sx b - mu b))) =
          c a b * ((Real.sqrt N * Real.sqrt N) * (((N : ℝ)⁻¹ * Sx a - mu a) * ((N : ℝ)⁻¹ * Sx b - mu b))) := by ring
      rw [show mu a = Whole.pair μ (u a) from rfl, show mu b = Whole.pair μ (u b) from rfl] at *
      rw [e, hs]
      field_simp
      ring
    simp_rw [key]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hAD : ∑ a, ∑ b, c a b * (Sx a * Sx b - Dx a b) =
      ∑ a, ∑ b, c a b * (Sx a * Sx b) - ∑ a, ∑ b, c a b * Dx a b := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  unfold pairEnergy
  rw [hF1, hF2, hF3, hAD, hg, hxi, hswap]
  field_simp
  ring

end FRPair

end HRS.MS.R2Chaos
