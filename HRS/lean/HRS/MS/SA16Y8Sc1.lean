import HRS.MS.SA16Y7K2b

/-!
# S.A.16 (SA16Y8) Sc1: choice of the Morrey scale for the Hölder estimate (classical clause)

`sa16y8_scale`: for `d ≥ 1`, `p > 1`, `n ≥ 1`, `d/p < n` there is `α > 0` such that for every `ρ ∈ (0,1]` there is a scale `r > 0` with
`r^k (r^d)^{-1/p} ρ ≤ ρ^α` for `k < n` and `r^n (r^d)^{-1/p} ≤ ρ^α` (`r = ρ^β`, `β = min 1 (p/(2d))`).
-/

noncomputable section
set_option autoImplicit false
open Filter Topology Set

namespace HRS.Whole.AppendixA.Phase2SA16Q

theorem sa16y8_scale (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 1 < p) (n : ℕ) (hnp : (d : ℝ) / p < n) :
    ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ r : ℝ, 0 < r ∧
      (∀ k : ℕ, k < n → r ^ k * ((r ^ d)⁻¹) ^ (1 / p) * ρ ≤ ρ ^ α) ∧
      r ^ n * ((r ^ d)⁻¹) ^ (1 / p) ≤ ρ ^ α := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hp0 : 0 < p := by linarith
  set β : ℝ := min 1 (p / (2 * d)) with hβ
  have hβ0 : 0 < β := lt_min one_pos (by positivity)
  have hβ1 : β ≤ 1 := min_le_left _ _
  have hβd : β * (d / p) ≤ 1 / 2 := by
    have : β ≤ p / (2 * d) := min_le_right _ _
    calc β * (d / p) ≤ (p / (2 * d)) * (d / p) := by gcongr
      _ = 1 / 2 := by field_simp
  have hn0 : 0 < (n : ℝ) - d / p := by linarith
  refine ⟨min (1 / 2) (β * ((n : ℝ) - d / p)), lt_min (by norm_num) (by positivity), fun ρ hρ hρ1 => ?_⟩
  set α : ℝ := min (1 / 2) (β * ((n : ℝ) - d / p)) with hα
  have hα0 : 0 < α := lt_min (by norm_num) (by positivity)
  refine ⟨ρ ^ β, Real.rpow_pos_of_pos hρ _, fun k hk => ?_, ?_⟩
  · have hr1 : ρ ^ β ≤ 1 := Real.rpow_le_one hρ.le hρ1 hβ0.le
    have hrk : (ρ ^ β) ^ k ≤ 1 := pow_le_one₀ (Real.rpow_nonneg hρ.le _) hr1
    have hrd : ((ρ ^ β) ^ d)⁻¹ ^ (1 / p) = ρ ^ (-(β * (d / p))) := by
      rw [← Real.rpow_natCast (ρ ^ β) d, ← Real.rpow_mul hρ.le, ← Real.rpow_neg hρ.le, ← Real.rpow_mul hρ.le]
      congr 1
      field_simp
    have hpos : 0 ≤ ρ ^ (-(β * (d / p))) := Real.rpow_nonneg hρ.le _
    calc (ρ ^ β) ^ k * ((ρ ^ β) ^ d)⁻¹ ^ (1 / p) * ρ ≤ 1 * ρ ^ (-(β * (d / p))) * ρ := by
          rw [hrd]
          gcongr
      _ = ρ ^ (1 - β * (d / p)) := by
          rw [one_mul, Real.rpow_sub hρ, Real.rpow_one, Real.rpow_neg hρ.le]; ring
      _ ≤ ρ ^ α := by
          refine Real.rpow_le_rpow_of_exponent_ge hρ hρ1 ?_
          have : α ≤ 1 / 2 := min_le_left _ _
          linarith
  · have hrd : ((ρ ^ β) ^ d)⁻¹ ^ (1 / p) = ρ ^ (-(β * (d / p))) := by
      rw [← Real.rpow_natCast (ρ ^ β) d, ← Real.rpow_mul hρ.le, ← Real.rpow_neg hρ.le, ← Real.rpow_mul hρ.le]
      congr 1
      field_simp
    rw [hrd, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le, ← Real.rpow_add hρ]
    refine Real.rpow_le_rpow_of_exponent_ge hρ hρ1 ?_
    have : α ≤ β * ((n : ℝ) - d / p) := min_le_right _ _
    nlinarith [this]

end HRS.Whole.AppendixA.Phase2SA16Q
