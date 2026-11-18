import HRS.MS.S111K4B

/-!
# S11.1 / T01 (S11K4), part C: Frobenius estimates and the variance of a centered Gaussian quadratic form

`k4fr M = ∑ M_ij²`.  The transport estimate `k4fr (S A Sᵀ - S' A S'ᵀ) ≤ 4 B² δ² k4fr A` (Pro `R26-T6.W01`/`W02`, here with arbitrary
finite index types), and `E (g·Mg - tr M)² ≤ 2 k4fr M` for the standard Gaussian vector (Pro `W03`/`W04` in the form needed).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace HRS.MS.S111K4

/-- The squared Frobenius norm. -/
def k4fr {p q : Type*} [Fintype p] [Fintype q] (M : Matrix p q ℝ) : ℝ := ∑ i, ∑ j, M i j ^ 2

theorem k4fr_nonneg {p q : Type*} [Fintype p] [Fintype q] (M : Matrix p q ℝ) : 0 ≤ k4fr M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem k4fr_transpose {p q : Type*} [Fintype p] [Fintype q] (M : Matrix p q ℝ) : k4fr Mᵀ = k4fr M := by
  unfold k4fr
  rw [Finset.sum_comm]
  rfl

theorem k4fr_add_le {p q : Type*} [Fintype p] [Fintype q] (M N : Matrix p q ℝ) :
    k4fr (M + N) ≤ 2 * k4fr M + 2 * k4fr N := by
  unfold k4fr
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  simp only [Matrix.add_apply]
  nlinarith [sq_nonneg (M i j - N i j)]

/-- Left multiplication by an operator of norm at most `B` is bounded on the Frobenius norm. -/
theorem k4fr_mul_le {p n q : Type*} [Fintype p] [Fintype n] [Fintype q]
    (S : Matrix p n ℝ) (A : Matrix n q ℝ) (B : ℝ)
    (hS : ∀ x : n → ℝ, ∑ i, (∑ j, S i j * x j) ^ 2 ≤ B ^ 2 * ∑ j, x j ^ 2) :
    k4fr (S * A) ≤ B ^ 2 * k4fr A := by
  unfold k4fr
  have h1 : ∑ i, ∑ k, (S * A) i k ^ 2 = ∑ k, ∑ i, (∑ j, S i j * A j k) ^ 2 := by
    rw [Finset.sum_comm]
    simp only [Matrix.mul_apply]
  have h2 : ∑ k, ∑ i, (∑ j, S i j * A j k) ^ 2 ≤ ∑ k, B ^ 2 * ∑ j, A j k ^ 2 :=
    Finset.sum_le_sum fun k _ => hS (fun j => A j k)
  rw [← Finset.mul_sum] at h2
  rw [h1]
  refine h2.trans (le_of_eq ?_)
  rw [Finset.sum_comm (f := fun j k => A j k ^ 2)]

/-- The transport estimate: `‖S A Sᵀ - S' A S'ᵀ‖² ≤ 4 B² δ² ‖A‖²` when `S, S'` have operator norm `≤ B` and `‖S - S'‖ ≤ δ`. -/
theorem k4fr_transport {p n : Type*} [Fintype p] [Fintype n] (S S' : Matrix p n ℝ) (A : Matrix n n ℝ) (B δ : ℝ)
    (hS : ∀ x : n → ℝ, ∑ i, (∑ j, S i j * x j) ^ 2 ≤ B ^ 2 * ∑ j, x j ^ 2)
    (hS' : ∀ x : n → ℝ, ∑ i, (∑ j, S' i j * x j) ^ 2 ≤ B ^ 2 * ∑ j, x j ^ 2)
    (hD : ∀ x : n → ℝ, ∑ i, (∑ j, (S i j - S' i j) * x j) ^ 2 ≤ δ ^ 2 * ∑ j, x j ^ 2) :
    k4fr (S * A * Sᵀ - S' * A * S'ᵀ) ≤ 4 * B ^ 2 * δ ^ 2 * k4fr A := by
  set D : Matrix p n ℝ := S - S' with hDdef
  have hD' : ∀ x : n → ℝ, ∑ i, (∑ j, D i j * x j) ^ 2 ≤ δ ^ 2 * ∑ j, x j ^ 2 := by
    intro x; simpa [hDdef] using hD x
  have hid : S * A * Sᵀ - S' * A * S'ᵀ = D * (A * Sᵀ) + S' * (A * Dᵀ) := by
    simp only [hDdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.transpose_sub, Matrix.mul_assoc]
    abel
  rw [hid]
  have t1 : k4fr (D * (A * Sᵀ)) ≤ δ ^ 2 * (B ^ 2 * k4fr A) := by
    refine (k4fr_mul_le D _ δ hD').trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [← k4fr_transpose]
    have : (A * Sᵀ)ᵀ = S * Aᵀ := by simp [Matrix.transpose_mul]
    rw [this]
    refine (k4fr_mul_le S _ B hS).trans ?_
    rw [k4fr_transpose]
  have t2 : k4fr (S' * (A * Dᵀ)) ≤ B ^ 2 * (δ ^ 2 * k4fr A) := by
    refine (k4fr_mul_le S' _ B hS').trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [← k4fr_transpose]
    have : (A * Dᵀ)ᵀ = D * Aᵀ := by simp [Matrix.transpose_mul]
    rw [this]
    refine (k4fr_mul_le D _ δ hD').trans ?_
    rw [k4fr_transpose]
  have := k4fr_add_le (D * (A * Sᵀ)) (S' * (A * Dᵀ))
  nlinarith [this, t1, t2]

end HRS.MS.S111K4
