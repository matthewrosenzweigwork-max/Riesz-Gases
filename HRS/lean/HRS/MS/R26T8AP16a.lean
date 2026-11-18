import HRS.MS.R26T8AP15

/-!
# S8.2 T8A P16a: trading a half power of the pole for the logarithmic degree
`r26t8a_log_pow_bound`: `r^(1/2) (1+|log r|)^b ≤ (5+4b)^b` on `(0,1]`.
`r26t8a_conormal_lower`: `Conormal k b M s A F → Conormal k 0 M (s+1/2) (c_b A) F` with `c_b` independent of `F, A`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_log_pow_bound (b : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    r ^ (1 / 2 : ℝ) * (1 + |Real.log r|) ^ b ≤ (5 + 4 * (b : ℝ)) ^ b := by
  set y : ℝ := 1 / r with hy
  have hy1 : 1 ≤ y := by rw [hy, le_div_iff₀ hr0]; linarith
  have hy0 : 0 < y := by linarith
  have hlog : |Real.log r| = Real.log y := by
    rw [hy, one_div, Real.log_inv, abs_of_nonpos (Real.log_nonpos hr0.le hr1)]
  set ε : ℝ := 1 / (4 * ((b : ℝ) + 1)) with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  have h1 := Real.log_le_rpow_div hy0.le hε0
  have hyε : 1 ≤ y ^ ε := Real.one_le_rpow hy1 hε0.le
  have h2 : 1 + Real.log y ≤ (5 + 4 * (b : ℝ)) * y ^ ε := by
    have : y ^ ε / ε = (4 * ((b : ℝ) + 1)) * y ^ ε := by rw [hε]; field_simp
    nlinarith [Nat.cast_nonneg (α := ℝ) b]
  have h3 : (1 + Real.log y) ^ b ≤ ((5 + 4 * (b : ℝ)) * y ^ ε) ^ b :=
    pow_le_pow_left₀ (by have := Real.log_nonneg hy1; linarith) h2 b
  have h4 : ((5 + 4 * (b : ℝ)) * y ^ ε) ^ b ≤ (5 + 4 * (b : ℝ)) ^ b * y ^ (1 / 4 : ℝ) := by
    have hp : (y ^ ε) ^ b = y ^ (ε * (b : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
    rw [mul_pow, hp]
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hy1 ?_) (by positivity)
    rw [hε]
    have : 1 / (4 * ((b : ℝ) + 1)) * (b : ℝ) = (1 / 4) * ((b : ℝ) / ((b : ℝ) + 1)) := by
      field_simp
    rw [this]
    have : (b : ℝ) / ((b : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    nlinarith
  have h5 : r ^ (1 / 2 : ℝ) * y ^ (1 / 4 : ℝ) ≤ 1 := by
    have : y ^ (1 / 4 : ℝ) = r ^ (-(1 / 4 : ℝ)) := by
      rw [hy, one_div, Real.inv_rpow hr0.le, ← Real.rpow_neg hr0.le]
    rw [this, ← Real.rpow_add hr0]
    have : (1 / 2 : ℝ) + -(1 / 4) = 1 / 4 := by norm_num
    rw [this]
    exact Real.rpow_le_one hr0.le hr1 (by norm_num)
  rw [hlog]
  calc r ^ (1 / 2 : ℝ) * (1 + Real.log y) ^ b ≤ r ^ (1 / 2 : ℝ) * ((5 + 4 * (b : ℝ)) ^ b * y ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (h3.trans h4) (by positivity)
    _ = (5 + 4 * (b : ℝ)) ^ b * (r ^ (1 / 2 : ℝ) * y ^ (1 / 4 : ℝ)) := by ring
    _ ≤ (5 + 4 * (b : ℝ)) ^ b * 1 := mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = _ := mul_one _

theorem r26t8a_conormal_lower (k b : ℕ) (M s : ℝ) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ (A : ℝ), 0 ≤ A → ∀ {F : Euc d → Euc d → ℝ}, Conormal k b M s A F →
      Conormal k 0 M (s + 1 / 2) (c * A) F := by
  refine ⟨(5 + 4 * (b : ℝ)) ^ b, ?_, fun A hA F hF => ?_⟩
  · exact one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) b; linarith)
  set c : ℝ := (5 + 4 * (b : ℝ)) ^ b with hc
  have hc1 : 1 ≤ c := one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) b; linarith)
  refine ⟨hF.1, fun p q hpq X z hz => ?_⟩
  refine (hF.2 p q hpq X z hz).trans ?_
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hr0 : 0 < min 1 ‖z‖ := lt_min one_pos hzn
  have hr1 : min 1 ‖z‖ ≤ 1 := min_le_left _ _
  set r : ℝ := min 1 ‖z‖ with hr
  have hW := r26t8a_pairWeight_nonneg M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)
  have hLb := r26t8a_log_pow_bound b hr0 hr1
  have e : r ^ (-(s + (q : ℝ))) = r ^ (-((s + 1 / 2) + (q : ℝ))) * r ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hr0]; congr 1; ring
  have hX : 0 ≤ r ^ (-((s + 1 / 2) + (q : ℝ))) := Real.rpow_nonneg hr0.le _
  have key : r ^ (-(s + (q : ℝ))) * (1 + |Real.log r|) ^ b ≤ c * r ^ (-((s + 1 / 2) + (q : ℝ))) := by
    rw [e]
    calc r ^ (-((s + 1 / 2) + (q : ℝ))) * r ^ (1 / 2 : ℝ) * (1 + |Real.log r|) ^ b
        = r ^ (-((s + 1 / 2) + (q : ℝ))) * (r ^ (1 / 2 : ℝ) * (1 + |Real.log r|) ^ b) := by ring
      _ ≤ r ^ (-((s + 1 / 2) + (q : ℝ))) * c := mul_le_mul_of_nonneg_left hLb hX
      _ = _ := by ring
  have hfin : 1 + r ^ (-(s + (q : ℝ))) * (1 + |Real.log r|) ^ b ≤
      c * (1 + r ^ (-((s + 1 / 2) + (q : ℝ))) * (1 + |Real.log r|) ^ 0) := by
    simp only [pow_zero, mul_one]
    nlinarith
  calc A * HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) *
        (1 + r ^ (-(s + (q : ℝ))) * (1 + |Real.log r|) ^ b)
      ≤ A * HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) *
        (c * (1 + r ^ (-((s + 1 / 2) + (q : ℝ))) * (1 + |Real.log r|) ^ 0)) :=
        mul_le_mul_of_nonneg_left hfin (mul_nonneg hA hW)
    _ = _ := by ring

end HRS.MS.R26T8A
