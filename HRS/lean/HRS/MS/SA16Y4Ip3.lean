import Mathlib

/-!
# S.A.16 (SA16Y4) Ip3: hat functions (piecewise-linear time interpolation)

`sa16y4_hat N t i σ = max 0 (1 - |σ N / t - i|)`: continuous, nonnegative, `∑_{i ≤ N} hat = 1` on `[0,t]`,
and `hat ≠ 0 → |σ - i t / N| < t / N`.
-/

noncomputable section
set_option autoImplicit false
open Filter Topology Set Finset

namespace HRS.Whole.AppendixA.Phase2SA16R

def sa16y4_hat (N : ℕ) (t : ℝ) (i : ℕ) (σ : ℝ) : ℝ := max 0 (1 - |σ * N / t - i|)

lemma sa16y4_hat_nonneg (N : ℕ) (t : ℝ) (i : ℕ) (σ : ℝ) : 0 ≤ sa16y4_hat N t i σ := le_max_left _ _

lemma sa16y4_hat_continuous (N : ℕ) (t : ℝ) (i : ℕ) : Continuous (sa16y4_hat N t i) := by
  unfold sa16y4_hat
  fun_prop

lemma sa16y4_hat_supp {N : ℕ} {t : ℝ} (hN : 1 ≤ N) (ht : 0 < t) {i : ℕ} {σ : ℝ} (h : sa16y4_hat N t i σ ≠ 0) :
    |σ - i * t / N| < t / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  unfold sa16y4_hat at h
  have h1 : 0 < 1 - |σ * N / t - i| := by
    by_contra hh
    exact h (max_eq_left (not_lt.1 hh))
  have h2 : |σ * N / t - i| < 1 := by linarith
  have h3 : σ * N / t - i = (σ - i * t / N) * (N / t) := by field_simp
  rw [h3, abs_mul, abs_of_pos (div_pos hN0 ht)] at h2
  rw [lt_div_iff₀ hN0]
  rw [← mul_div_assoc, div_lt_one ht] at h2
  exact h2

lemma sa16y4_hat_sum {N : ℕ} {t : ℝ} (hN : 1 ≤ N) (ht : 0 < t) {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) t) :
    ∑ i ∈ range (N + 1), sa16y4_hat N t i σ = 1 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set s : ℝ := σ * N / t with hs
  have hs0 : 0 ≤ s := by rw [hs]; exact div_nonneg (mul_nonneg hσ.1 hN0.le) ht.le
  have hsN : s ≤ N := by
    rw [hs, div_le_iff₀ ht]; nlinarith [hσ.2]
  set k : ℕ := ⌊s⌋₊ with hk
  have hk1 : (k : ℝ) ≤ s := Nat.floor_le hs0
  have hk2 : s < k + 1 := Nat.lt_floor_add_one s
  have hkN : k ≤ N := Nat.floor_le_of_le hsN
  have hpt : ∀ i : ℕ, sa16y4_hat N t i σ = (if i = k then 1 - (s - k) else 0) + (if i = k + 1 then s - k else 0) := by
    intro i
    unfold sa16y4_hat
    rw [← hs]
    rcases lt_trichotomy i k with h | h | h
    · have : (i : ℝ) + 1 ≤ k := by exact_mod_cast h
      have h1 : 1 ≤ |s - i| := by rw [abs_of_nonneg (by linarith)]; linarith
      rw [max_eq_left (by linarith)]
      simp [h.ne, show i ≠ k + 1 by omega]
    · subst h
      rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]
      simp
    · by_cases h2 : i = k + 1
      · subst h2
        push_cast
        rw [abs_of_nonpos (by linarith), max_eq_right (by linarith)]
        simp
        ring
      · have : (k : ℝ) + 2 ≤ i := by exact_mod_cast (by omega : k + 2 ≤ i)
        rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]
        simp [h.ne', h2]
  simp_rw [hpt]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_range]
  rw [if_pos (by omega)]
  by_cases hkN' : k + 1 ≤ N
  · rw [if_pos (by omega)]; ring
  · rw [if_neg (by omega)]
    have hkc : (k : ℝ) = N := by
      have : k = N := by omega
      exact_mod_cast this
    have hsNe : s = N := le_antisymm hsN (hkc ▸ hk1)
    rw [hsNe, hkc]; simp

end HRS.Whole.AppendixA.Phase2SA16R
