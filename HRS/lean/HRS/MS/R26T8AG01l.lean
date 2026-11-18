import HRS.MS.R26T8AG01k
import HRS.MS.R26T8AG01c

/-!
# S8.2 observed-time layer, packet T8A.G01 (helper l): sums of inverse distances against the envelope

With `a_ij = 1/‖X i - X j‖` over `i < j`: `A = Σ_i Σ_{j>i} a_ij ≤ N² · 2 env`, `Q = Σ_i Σ_{j>i} a_ij² ≤ N² env`
and `A² ≤ N² Q`, where `env = configPoleEnvelope 2 X`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_g01l_sums {d N : ℕ} (X : EucConfig d N) :
    (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖X i - X j‖) ≤
        (N : ℝ) * (N : ℝ) * (2 * configPoleEnvelope 2 X) ∧
    (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), (1 / ‖X i - X j‖) ^ 2) ≤
        (N : ℝ) * (N : ℝ) * configPoleEnvelope 2 X ∧
    (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖X i - X j‖) ^ 2 ≤
        (N : ℝ) ^ 2 * (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), (1 / ‖X i - X j‖) ^ 2) := by
  set env := configPoleEnvelope 2 X with henv
  have hpair : ∀ i j : Fin N, i < j → 1 / ‖X i - X j‖ ≤ 2 * env ∧ (1 / ‖X i - X j‖) ^ 2 ≤ env :=
    fun i j h => r26t8a_g01k_env X i j h.ne
  have hcard : ∀ i : Fin N, ((Finset.univ.filter (fun j => i < j)).card : ℝ) ≤ (N : ℝ) := by
    intro i
    have h1 := Finset.card_le_univ (Finset.univ.filter (fun j => i < j))
    rw [Fintype.card_fin] at h1
    exact_mod_cast h1
  have hα : ∀ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖X i - X j‖ ≤ (N : ℝ) * (2 * env) := by
    intro i
    calc ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖X i - X j‖
        ≤ ∑ _j ∈ Finset.univ.filter (fun j => i < j), 2 * env :=
          Finset.sum_le_sum fun j hj => (hpair i j (Finset.mem_filter.1 hj).2).1
      _ = ((Finset.univ.filter (fun j => i < j)).card : ℝ) * (2 * env) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (2 * env) := by
          apply mul_le_mul_of_nonneg_right (hcard i)
          have := r26t8a_g01h_env_one_le d N X
          linarith
  have hβ : ∀ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), (1 / ‖X i - X j‖) ^ 2 ≤ (N : ℝ) * env := by
    intro i
    calc ∑ j ∈ Finset.univ.filter (fun j => i < j), (1 / ‖X i - X j‖) ^ 2
        ≤ ∑ _j ∈ Finset.univ.filter (fun j => i < j), env :=
          Finset.sum_le_sum fun j hj => (hpair i j (Finset.mem_filter.1 hj).2).2
      _ = ((Finset.univ.filter (fun j => i < j)).card : ℝ) * env := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * env := by
          apply mul_le_mul_of_nonneg_right (hcard i)
          have := r26t8a_g01h_env_one_le d N X
          linarith
  refine ⟨?_, ?_, ?_⟩
  · calc ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖X i - X j‖
        ≤ ∑ _i : Fin N, (N : ℝ) * (2 * env) := Finset.sum_le_sum fun i _ => hα i
      _ = (N : ℝ) * (N : ℝ) * (2 * env) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  · calc ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), (1 / ‖X i - X j‖) ^ 2
        ≤ ∑ _i : Fin N, (N : ℝ) * env := Finset.sum_le_sum fun i _ => hβ i
      _ = (N : ℝ) * (N : ℝ) * env := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  · -- Cauchy–Schwarz twice
    have hcs1 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin N)))
      (f := fun i => ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖X i - X j‖)
    have hcs2 : ∀ i : Fin N, (∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖X i - X j‖) ^ 2 ≤
        (N : ℝ) * ∑ j ∈ Finset.univ.filter (fun j => i < j), (1 / ‖X i - X j‖) ^ 2 := by
      intro i
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ.filter (fun j => i < j))
        (f := fun j => 1 / ‖X i - X j‖)
      exact h.trans (mul_le_mul_of_nonneg_right (hcard i) (Finset.sum_nonneg fun j _ => sq_nonneg _))
    have hsum : ∑ i : Fin N, (∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖X i - X j‖) ^ 2 ≤
        (N : ℝ) * ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), (1 / ‖X i - X j‖) ^ 2 := by
      calc _ ≤ ∑ i : Fin N, (N : ℝ) * ∑ j ∈ Finset.univ.filter (fun j => i < j), (1 / ‖X i - X j‖) ^ 2 :=
            Finset.sum_le_sum fun i _ => hcs2 i
        _ = (N : ℝ) * ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), (1 / ‖X i - X j‖) ^ 2 :=
            (Finset.mul_sum _ _ _).symm
    have hcard' : ((Finset.univ : Finset (Fin N)).card : ℝ) = (N : ℝ) := by
      rw [Finset.card_univ, Fintype.card_fin]
    rw [hcard'] at hcs1
    calc (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖X i - X j‖) ^ 2
        ≤ (N : ℝ) * ∑ i : Fin N, (∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖X i - X j‖) ^ 2 := hcs1
      _ ≤ (N : ℝ) * ((N : ℝ) * ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), (1 / ‖X i - X j‖) ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (N : ℝ) ^ 2 * (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), (1 / ‖X i - X j‖) ^ 2) := by
          ring

end HRS.MS.R26T8A

end
