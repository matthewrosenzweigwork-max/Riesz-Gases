import Mathlib

/-!
# S11.6 packet P01 (`R26-T8B.P01`): difference quotients imply endpoint-inclusive scalar continuity

Prefix `s116_`, namespace `HRS.MS.S116`.
-/

set_option autoImplicit false

noncomputable section

namespace HRS.MS.S116

theorem s116_continuous_of_quotient (T : ℝ) (f g : ℝ → ℝ)
    (hq : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧
      ∀ h : ℝ, h ≠ 0 → |h| < δ → t + h ∈ Set.Icc (0 : ℝ) T →
        |h⁻¹ * (f (t + h) - f t) - g t| ≤ e) :
    ContinuousOn f (Set.Icc (0 : ℝ) T) := by
  intro t ht
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ₀, hδ₀, hδ⟩ := hq t ht 1 one_pos
  have hK : 0 < |g t| + 1 := by positivity
  refine ⟨min δ₀ (ε / (|g t| + 1)), lt_min hδ₀ (div_pos hε hK), fun x hx hxd => ?_⟩
  rw [Real.dist_eq] at hxd ⊢
  by_cases hxt : x = t
  · simp [hxt, hε]
  · have hh : x - t ≠ 0 := sub_ne_zero.mpr hxt
    have h1 : |x - t| < δ₀ := lt_of_lt_of_le hxd (min_le_left _ _)
    have h2 : |x - t| < ε / (|g t| + 1) := lt_of_lt_of_le hxd (min_le_right _ _)
    have hmem : t + (x - t) ∈ Set.Icc (0 : ℝ) T := by simpa using hx
    have hb := hδ (x - t) hh h1 hmem
    have hb' : |(x - t)⁻¹ * (f x - f t)| ≤ |g t| + 1 := by
      have : |(x - t)⁻¹ * (f (t + (x - t)) - f t)| ≤ |g t| + 1 := by
        calc _ = |((x - t)⁻¹ * (f (t + (x - t)) - f t) - g t) + g t| := by ring_nf
          _ ≤ |(x - t)⁻¹ * (f (t + (x - t)) - f t) - g t| + |g t| := abs_add_le _ _
          _ ≤ 1 + |g t| := add_le_add hb le_rfl
          _ = |g t| + 1 := by ring
      simpa using this
    have hfx : f x - f t = (x - t) * ((x - t)⁻¹ * (f x - f t)) := by field_simp
    calc |f x - f t| = |x - t| * |(x - t)⁻¹ * (f x - f t)| := by rw [hfx, abs_mul]; congr 2; field_simp
      _ ≤ |x - t| * (|g t| + 1) := mul_le_mul_of_nonneg_left hb' (abs_nonneg _)
      _ < ε / (|g t| + 1) * (|g t| + 1) := mul_lt_mul_of_pos_right h2 hK
      _ = ε := by field_simp

end HRS.MS.S116

end
