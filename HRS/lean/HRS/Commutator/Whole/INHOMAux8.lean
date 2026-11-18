import HRS.Commutator.Whole.INHOMAux7

/-!
# CMX-INHOM auxiliary 8: weight comparisons between `Ḣ^{-α}`, `H^{-α}` and `L²`

Pointwise comparisons of the Fourier weights `(2π|ξ|)^{-2α}` (for `|ξ| ≥ 1/16`), `1` (for `|ξ| ≤ 1/8`),
`|ξ|^{2-4α}` (for `|ξ| ≥ 1`) with the inhomogeneous weight `(1+4π²|ξ|²)^{-α}`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

/-- `(2π|ξ|)^{-2α} ≤ c W^{-α}` for `|ξ| ≥ 1/16`. -/
lemma inhom_w1 {α : ℝ} (hα : 0 < α) (ξ : Euc d) (hξ : 1 / 16 ≤ ‖ξ‖) :
    (2 * Real.pi * ‖ξ‖) ^ (2 * (-α)) ≤
      (1 + 64 / Real.pi ^ 2) ^ α * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-α) := by
  set x : ℝ := 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 with hx
  have hpi : 0 < Real.pi := Real.pi_pos
  have hx0 : 0 < x := by
    have : 0 < ‖ξ‖ := lt_of_lt_of_le (by norm_num) hξ
    positivity
  have hxge : Real.pi ^ 2 / 64 ≤ x := by
    have h1 : (1 / 16 : ℝ) ^ 2 ≤ ‖ξ‖ ^ 2 := pow_le_pow_left₀ (by norm_num) hξ 2
    rw [hx]; nlinarith [sq_nonneg Real.pi]
  have e1 : (2 * Real.pi * ‖ξ‖) ^ (2 * (-α)) = x ^ (-α) := by
    rw [hx, show (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) = (2 * Real.pi * ‖ξ‖) ^ (2 : ℝ) by
      rw [Real.rpow_two]; ring, ← Real.rpow_mul (by positivity)]
  rw [e1]
  have hc : 0 < 1 + 64 / Real.pi ^ 2 := by positivity
  have h2 : 1 + x ≤ (1 + 64 / Real.pi ^ 2) * x := by
    have : 1 ≤ 64 / Real.pi ^ 2 * x := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; nlinarith
    nlinarith
  have h3 : (1 + x) ^ α ≤ (1 + 64 / Real.pi ^ 2) ^ α * x ^ α := by
    rw [← Real.mul_rpow hc.le hx0.le]
    exact Real.rpow_le_rpow (by positivity) h2 hα.le
  rw [Real.rpow_neg hx0.le, Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + x)]
  have h4 : 0 < (1 + x) ^ α := Real.rpow_pos_of_pos (by positivity) _
  have h5 : 0 < x ^ α := Real.rpow_pos_of_pos hx0 _
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ h5 h4]
  nlinarith

/-- `1 ≤ c W^{-α}` for `|ξ| ≤ 1/8`. -/
lemma inhom_w2 {α : ℝ} (hα : 0 < α) (ξ : Euc d) (hξ : ‖ξ‖ ≤ 1 / 8) :
    1 ≤ (1 + Real.pi ^ 2 / 16) ^ α * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-α) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hW : 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 ≤ 1 + Real.pi ^ 2 / 16 := by
    have : ‖ξ‖ ^ 2 ≤ (1 / 8) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hξ 2
    nlinarith [sq_nonneg Real.pi]
  have hW0 : 0 < 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by positivity
  have h1 : (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ α ≤ (1 + Real.pi ^ 2 / 16) ^ α :=
    Real.rpow_le_rpow hW0.le hW hα.le
  rw [Real.rpow_neg hW0.le]
  have h4 : 0 < (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ α := Real.rpow_pos_of_pos hW0 _
  rw [← div_eq_mul_inv, le_div_iff₀ h4]
  simpa using h1

/-- the symbol bound: `|c|² (1-χ)² |ξ_i|² |ξ|^{-4α} ≤ |c|² (1+4π²)^α W^{-α}` for `α ≥ 1`. -/
lemma inhom_w3 {α : ℝ} (hα : 1 ≤ α) (c : ℂ) (i : Fin d) (ξ : Euc d) :
    ‖c * ((1 - chi ξ : ℝ) : ℂ) * ((ξ i * ‖ξ‖ ^ (-(2 * α)) : ℝ) : ℂ)‖ ^ 2 ≤
      ‖c‖ ^ 2 * ((1 + 4 * Real.pi ^ 2) ^ α * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-α)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hα0 : 0 < α := by linarith
  by_cases hξ : ‖ξ‖ ≤ 1
  · have : chi ξ = 1 := cmxFB_chi_one hξ
    rw [this]
    calc _ = (0 : ℝ) := by simp
      _ ≤ _ := by positivity
  · push Not at hξ
    have hn : 0 < ‖ξ‖ := by linarith
    have hchi0 := cmxFB_chi_nonneg ξ
    have hchi1 := cmxFB_chi_le_one ξ
    have h1 : ‖((1 - chi ξ : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
    have h2 : |ξ i| ≤ ‖ξ‖ := by simpa using PiLp.norm_apply_le ξ i
    have h3 : ‖((ξ i * ‖ξ‖ ^ (-(2 * α)) : ℝ) : ℂ)‖ ≤ ‖ξ‖ ^ (1 - 2 * α) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hn _),
        show (1 - 2 * α) = 1 + (-(2 * α)) by ring, Real.rpow_add hn, Real.rpow_one]
      gcongr
    have h4 : ‖c * ((1 - chi ξ : ℝ) : ℂ) * ((ξ i * ‖ξ‖ ^ (-(2 * α)) : ℝ) : ℂ)‖ ≤
        ‖c‖ * ‖ξ‖ ^ (1 - 2 * α) := by
      rw [norm_mul, norm_mul]
      calc ‖c‖ * ‖((1 - chi ξ : ℝ) : ℂ)‖ * ‖((ξ i * ‖ξ‖ ^ (-(2 * α)) : ℝ) : ℂ)‖
          ≤ ‖c‖ * 1 * ‖ξ‖ ^ (1 - 2 * α) := by gcongr
        _ = _ := by ring
    have h5 : (‖c‖ * ‖ξ‖ ^ (1 - 2 * α)) ^ 2 = ‖c‖ ^ 2 * ‖ξ‖ ^ (2 - 4 * α) := by
      rw [mul_pow, ← Real.rpow_natCast (‖ξ‖ ^ (1 - 2 * α)) 2, ← Real.rpow_mul hn.le]
      congr 2; push_cast; ring
    have h6 : ‖ξ‖ ^ (2 - 4 * α) ≤ ‖ξ‖ ^ (-(2 * α)) :=
      Real.rpow_le_rpow_of_exponent_le hξ.le (by linarith)
    have hW0 : 0 < 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by positivity
    have h7 : ‖ξ‖ ^ (-(2 * α)) ≤ (1 + 4 * Real.pi ^ 2) ^ α * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-α) := by
      have hle : 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 ≤ (1 + 4 * Real.pi ^ 2) * ‖ξ‖ ^ 2 := by
        have : 1 ≤ ‖ξ‖ ^ 2 := by nlinarith
        nlinarith
      have h8 : (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ α ≤ (1 + 4 * Real.pi ^ 2) ^ α * ‖ξ‖ ^ (2 * α) := by
        rw [show ‖ξ‖ ^ (2 * α) = (‖ξ‖ ^ (2 : ℝ)) ^ α by rw [Real.rpow_mul hn.le],
          ← Real.mul_rpow (by positivity) (by positivity), Real.rpow_two]
        exact Real.rpow_le_rpow hW0.le hle hα0.le
      rw [Real.rpow_neg hW0.le, Real.rpow_neg hn.le]
      have h9 : 0 < (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ α := Real.rpow_pos_of_pos hW0 _
      have h10 : 0 < ‖ξ‖ ^ (2 * α) := Real.rpow_pos_of_pos hn _
      rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ h10 h9]
      nlinarith
    calc ‖c * ((1 - chi ξ : ℝ) : ℂ) * ((ξ i * ‖ξ‖ ^ (-(2 * α)) : ℝ) : ℂ)‖ ^ 2
        ≤ (‖c‖ * ‖ξ‖ ^ (1 - 2 * α)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h4 2
      _ = ‖c‖ ^ 2 * ‖ξ‖ ^ (2 - 4 * α) := h5
      _ ≤ ‖c‖ ^ 2 * ‖ξ‖ ^ (-(2 * α)) := by gcongr
      _ ≤ _ := by gcongr

end HRS.Commutator.Whole
