import Mathlib

/-!
# Q54, part 2: finite Young / Schur inequalities on a discrete group

For a nonnegative kernel `κ` on an additive group `G` whose finite partial sums are bounded by `Kκ`, and finite sets
`S, B`:

* `schur_sq_finite`: `∑_{k∈S} (∑_{l∈B} κ(k-l) y_l)² ≤ Kκ² ∑_{l∈B} y_l²` (`ℓ¹ * ℓ² → ℓ²`);
* `schur_form_finite`: `∑_{k∈B}∑_{l∈B} κ(k-l) x_k x_l ≤ Kκ ∑_{k∈B} x_k²`.

All sums are finite, so no summability hypotheses are needed.
-/

noncomputable section

open Finset

namespace HRS.Uniform.Q54

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem sum_shift_le (κ : G → ℝ) (hκ0 : ∀ m, 0 ≤ κ m) (Kκ : ℝ)
    (hK : ∀ F : Finset G, ∑ m ∈ F, κ m ≤ Kκ) (k : G) (B : Finset G) :
    ∑ l ∈ B, κ (k - l) ≤ Kκ := by
  have h : ∑ l ∈ B, κ (k - l) = ∑ m ∈ B.image (fun l => k - l), κ m := by
    rw [Finset.sum_image]
    intro x _ y _ hxy
    simpa using hxy
  rw [h]
  exact hK _

theorem sum_shift_le' (κ : G → ℝ) (hκ0 : ∀ m, 0 ≤ κ m) (Kκ : ℝ)
    (hK : ∀ F : Finset G, ∑ m ∈ F, κ m ≤ Kκ) (l : G) (S : Finset G) :
    ∑ k ∈ S, κ (k - l) ≤ Kκ := by
  have h : ∑ k ∈ S, κ (k - l) = ∑ m ∈ S.image (fun k => k - l), κ m := by
    rw [Finset.sum_image]
    intro x _ y _ hxy
    simpa using hxy
  rw [h]
  exact hK _

theorem schur_sq_finite (κ y : G → ℝ) (hκ0 : ∀ m, 0 ≤ κ m) (hy0 : ∀ l, 0 ≤ y l) (Kκ : ℝ)
    (hK : ∀ F : Finset G, ∑ m ∈ F, κ m ≤ Kκ) (S B : Finset G) :
    ∑ k ∈ S, (∑ l ∈ B, κ (k - l) * y l) ^ 2 ≤ Kκ ^ 2 * ∑ l ∈ B, y l ^ 2 := by
  have hK0 : 0 ≤ Kκ := by simpa using hK ∅
  have hpt : ∀ k, (∑ l ∈ B, κ (k - l) * y l) ^ 2 ≤ Kκ * ∑ l ∈ B, κ (k - l) * y l ^ 2 := by
    intro k
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq B (fun l => Real.sqrt (κ (k - l)))
      (fun l => Real.sqrt (κ (k - l)) * y l)
    have e1 : ∀ l, Real.sqrt (κ (k - l)) * (Real.sqrt (κ (k - l)) * y l) = κ (k - l) * y l := by
      intro l
      rw [← mul_assoc, Real.mul_self_sqrt (hκ0 _)]
    have e2 : ∀ l, Real.sqrt (κ (k - l)) ^ 2 = κ (k - l) := fun l => Real.sq_sqrt (hκ0 _)
    have e3 : ∀ l, (Real.sqrt (κ (k - l)) * y l) ^ 2 = κ (k - l) * y l ^ 2 := by
      intro l; rw [mul_pow, e2]
    simp only [e1, e2, e3] at h1
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_right (sum_shift_le κ hκ0 Kκ hK k B)
      (Finset.sum_nonneg fun l _ => mul_nonneg (hκ0 _) (sq_nonneg _))
  calc ∑ k ∈ S, (∑ l ∈ B, κ (k - l) * y l) ^ 2
      ≤ ∑ k ∈ S, Kκ * ∑ l ∈ B, κ (k - l) * y l ^ 2 := Finset.sum_le_sum fun k _ => hpt k
    _ = Kκ * ∑ l ∈ B, y l ^ 2 * ∑ k ∈ S, κ (k - l) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ ≤ Kκ * ∑ l ∈ B, y l ^ 2 * Kκ := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => ?_) hK0
        exact mul_le_mul_of_nonneg_left (sum_shift_le' κ hκ0 Kκ hK l S) (sq_nonneg _)
    _ = Kκ ^ 2 * ∑ l ∈ B, y l ^ 2 := by
        rw [← Finset.sum_mul]; ring

theorem schur_form_finite (κ x : G → ℝ) (hκ0 : ∀ m, 0 ≤ κ m) (hx0 : ∀ k, 0 ≤ x k) (Kκ : ℝ)
    (hK : ∀ F : Finset G, ∑ m ∈ F, κ m ≤ Kκ) (B : Finset G) :
    ∑ k ∈ B, ∑ l ∈ B, κ (k - l) * x k * x l ≤ Kκ * ∑ k ∈ B, x k ^ 2 := by
  have hpt : ∀ k l, κ (k - l) * x k * x l ≤ κ (k - l) * (x k ^ 2 / 2) + κ (k - l) * (x l ^ 2 / 2) := by
    intro k l
    have := hκ0 (k - l)
    nlinarith [sq_nonneg (x k - x l), mul_nonneg this (sq_nonneg (x k - x l))]
  calc ∑ k ∈ B, ∑ l ∈ B, κ (k - l) * x k * x l
      ≤ ∑ k ∈ B, ∑ l ∈ B, (κ (k - l) * (x k ^ 2 / 2) + κ (k - l) * (x l ^ 2 / 2)) :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hpt k l
    _ = ∑ k ∈ B, (x k ^ 2 / 2) * ∑ l ∈ B, κ (k - l) +
          ∑ l ∈ B, (x l ^ 2 / 2) * ∑ k ∈ B, κ (k - l) := by
        simp only [Finset.sum_add_distrib]
        congr 1
        · refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
    _ ≤ ∑ k ∈ B, (x k ^ 2 / 2) * Kκ + ∑ l ∈ B, (x l ^ 2 / 2) * Kκ := by
        refine add_le_add (Finset.sum_le_sum fun k _ => ?_) (Finset.sum_le_sum fun l _ => ?_)
        · exact mul_le_mul_of_nonneg_left (sum_shift_le κ hκ0 Kκ hK k B) (by positivity)
        · exact mul_le_mul_of_nonneg_left (sum_shift_le' κ hκ0 Kκ hK l B) (by positivity)
    _ = Kκ * ∑ k ∈ B, x k ^ 2 := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring

end HRS.Uniform.Q54
