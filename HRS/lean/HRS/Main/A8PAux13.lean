import HRS.Main.A8PAux12

/-!
# Packet A8P, part 13: the scales `σ, A, q` and the pointwise covariance identity
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

theorem a8p_sigma_nonneg (S : MainData d) (N : ℕ) : 0 ≤ S.sigma N :=
  Q54c.sigmaScale_nonneg' (S.hκ N)

theorem a8p_sigma_le_kappa (S : MainData d) (N : ℕ) : S.sigma N ≤ S.κ N :=
  Q54c.sigmaScale_le_kappa'

theorem a8p_q_bounds (S : MainData d) {N : ℕ} (hN : 1 ≤ N) : 0 ≤ S.qN N ∧ S.qN N ≤ 1 :=
  Q54c.qScale_bounds (by omega) (S.hκ N) (S.hinvβ N)

theorem a8p_A_abs_le (S : MainData d) (N : ℕ) : |S.AN N| ≤ 1 :=
  Q54c.Ascale_abs_le (S.hκ N)

theorem a8p_A_mul_kappa (S : MainData d) (N : ℕ) : S.AN N * S.κ N = S.sigma N := by
  have hκ := (S.hκ N).ne'
  unfold MainData.AN Ascale MainData.sigma
  by_cases h0 : S.invβ N = 0
  · simp [h0, sigmaScale]
  · simp [h0, hκ]

theorem a8p_q_eq (S : MainData d) (N : ℕ) : S.qN N = S.sigma N ^ 2 * S.invβ N / N := by
  unfold MainData.qN qScale MainData.sigma
  by_cases h0 : S.invβ N = 0
  · simp [h0]
  · simp [h0]

/-- The scaled noise integrand of the `a`-th statistic. -/
def a8pPhi {Ω : Type*} {N : ℕ} (D : DynData d) (σ t : ℝ) (f : ℝ → Torus d → ℝ)
    (X : ℝ≥0 → Ω → Config d N) : ℝ → Ω → (Fin N × Fin d) → ℝ :=
  fun r ω k => σ * empiricalNoiseIntegrand D t f X r ω k

theorem a8pPhi_cov {Ω : Type*} {N : ℕ} (hN : 1 ≤ N) (D : DynData d) (σ ta tb : ℝ)
    (fa fb : ℝ → Torus d → ℝ) (X : ℝ≥0 → Ω → Config d N) (r : ℝ) (ω : Ω) :
    ∑ k, a8pPhi D σ ta fa X r ω k * a8pPhi D σ tb fb X r ω k =
      if r ∈ Set.Icc 0 ta ∧ r ∈ Set.Icc 0 tb then
        2 * (σ ^ 2 * D.invβ / N) *
          ∫ x, inner ℝ (Torus.grad (fa r) x) (Torus.grad (fb r) x) ∂(empirical (X (Real.toNNReal r) ω))
      else 0 := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  by_cases h : r ∈ Set.Icc 0 ta ∧ r ∈ Set.Icc 0 tb
  · rw [if_pos h, gfb2_integral_empirical, Fintype.sum_prod_type]
    simp only [a8pPhi, empiricalNoiseIntegrand, if_pos h.1, if_pos h.2, a8p_inner_grad]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    have h2 : Real.sqrt (2 * D.invβ) ^ 2 = 2 * D.invβ := Real.sq_sqrt (by linarith [D.hβ])
    have : σ * (Real.sqrt (2 * D.invβ) / N * (Torus.grad (fa r) (X (Real.toNNReal r) ω i)) j) *
        (σ * (Real.sqrt (2 * D.invβ) / N * (Torus.grad (fb r) (X (Real.toNNReal r) ω i)) j)) =
        σ ^ 2 * (Real.sqrt (2 * D.invβ) ^ 2) / (N : ℝ) ^ 2 *
          ((Torus.grad (fa r) (X (Real.toNNReal r) ω i)) j *
            (Torus.grad (fb r) (X (Real.toNNReal r) ω i)) j) := by
      field_simp
    rw [this, h2, a8p_grad_apply, a8p_grad_apply]
    field_simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases ha : r ∈ Set.Icc 0 ta
    · have hb : r ∉ Set.Icc 0 tb := fun hb => h ⟨ha, hb⟩
      simp [a8pPhi, empiricalNoiseIntegrand, hb]
    · simp [a8pPhi, empiricalNoiseIntegrand, ha]

end HRS.Main.A8P
