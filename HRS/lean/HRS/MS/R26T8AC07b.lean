import HRS.MS.R26T8AC07a
import HRS.MS.S82P2Mom

/-!
# S8.2 observed-time layer, packet T8A.C07b: evaluation of the critical two-centre bound (`p = p' = d/2`)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace HRS.MS.R26T8A

theorem r26t8a_c07b_eval (d : ℕ) (hd : 1 ≤ d) {D R : ℝ} (hD : 0 < D) (hR1 : R ≤ 1) :
    ENNReal.ofReal ((D / 2) ^ (-((d : ℝ) / 2))) *
        ENNReal.ofReal (r26t8a_c08a_const d * ∫ r in (0 : ℝ)..(D / 2), r ^ ((d : ℝ) - 1 - (d : ℝ) / 2)) +
      ENNReal.ofReal ((D / 2) ^ (-((d : ℝ) / 2))) *
        ENNReal.ofReal (r26t8a_c08a_const d * ∫ r in (0 : ℝ)..(D / 2), r ^ ((d : ℝ) - 1 - (d : ℝ) / 2)) +
      ENNReal.ofReal ((D / 2) ^ (-((d : ℝ) / 2 + (d : ℝ) / 2))) *
        ENNReal.ofReal (r26t8a_c08a_const d * ∫ r in (0 : ℝ)..(2 * D), r ^ ((d : ℝ) - 1 - 0)) +
      ENNReal.ofReal (2 ^ ((d : ℝ) / 2)) *
        ENNReal.ofReal (r26t8a_c08a_const d *
          ∫ r in (2 * D)..(max (2 * D) R), r ^ ((d : ℝ) - 1 - ((d : ℝ) / 2 + (d : ℝ) / 2))) ≤
      ENNReal.ofReal (r26t8a_c08a_const d * (2 / ((d : ℝ) / 2) + 4 ^ d / d +
        2 ^ ((d : ℝ) / 2) * |Real.log (min 1 D)|)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set e : ℝ := (d : ℝ) / 2 with he
  have he0 : 0 < e := by positivity
  set ω : ℝ := r26t8a_c08a_const d with hω
  have hω0 : 0 ≤ ω := r26t8a_c08a_const_nonneg d
  have hD2 : 0 < D / 2 := by positivity
  -- first two integrals
  have hI1 : ∫ r in (0 : ℝ)..(D / 2), r ^ ((d : ℝ) - 1 - e) = (D / 2) ^ e / e := by
    have hex : (d : ℝ) - 1 - e + 1 = e := by rw [he]; ring
    rw [integral_rpow (Or.inl (by rw [he]; linarith)), hex, Real.zero_rpow he0.ne']; simp
  have t1 : ENNReal.ofReal ((D / 2) ^ (-e)) * ENNReal.ofReal (ω * ∫ r in (0 : ℝ)..(D / 2),
      r ^ ((d : ℝ) - 1 - e)) = ENNReal.ofReal (ω / e) := by
    rw [hI1, ← ENNReal.ofReal_mul (Real.rpow_nonneg hD2.le _)]
    congr 1
    have : (D / 2) ^ (-e) * (D / 2) ^ e = 1 := by
      rw [← Real.rpow_add hD2]; simp
    calc (D / 2) ^ (-e) * (ω * ((D / 2) ^ e / e)) = ((D / 2) ^ (-e) * (D / 2) ^ e) * (ω / e) := by ring
      _ = ω / e := by rw [this, one_mul]
  -- the third
  have hI3 : ∫ r in (0 : ℝ)..(2 * D), r ^ ((d : ℝ) - 1 - 0) = (2 * D) ^ (d : ℝ) / d := by
    have hex : (d : ℝ) - 1 - 0 + 1 = d := by ring
    rw [integral_rpow (Or.inl (by linarith)), hex, Real.zero_rpow hdR.ne']; simp
  have t3 : ENNReal.ofReal ((D / 2) ^ (-(e + e))) * ENNReal.ofReal (ω * ∫ r in (0 : ℝ)..(2 * D),
      r ^ ((d : ℝ) - 1 - 0)) = ENNReal.ofReal (ω * (4 ^ d / d)) := by
    rw [hI3, ← ENNReal.ofReal_mul (Real.rpow_nonneg hD2.le _)]
    congr 1
    have h2D : (2 * D) = 4 * (D / 2) := by ring
    have hee : e + e = (d : ℝ) := by rw [he]; ring
    rw [hee, h2D, Real.mul_rpow (by norm_num) hD2.le, Real.rpow_natCast]
    have : (D / 2) ^ (-(d : ℝ)) * (D / 2) ^ (d : ℝ) = 1 := by
      rw [← Real.rpow_add hD2]; simp
    calc (D / 2) ^ (-(d : ℝ)) * (ω * (4 ^ d * (D / 2) ^ (d : ℝ) / d)) =
        ((D / 2) ^ (-(d : ℝ)) * (D / 2) ^ (d : ℝ)) * (ω * (4 ^ d / d)) := by ring
      _ = _ := by rw [this, one_mul]
  -- the fourth
  have hI4 : ∫ r in (2 * D)..(max (2 * D) R), r ^ ((d : ℝ) - 1 - (e + e)) =
      Real.log (max (2 * D) R / (2 * D)) := by
    have : (fun r : ℝ => r ^ ((d : ℝ) - 1 - (e + e))) = fun r => r⁻¹ := by
      funext r; rw [show (d : ℝ) - 1 - (e + e) = -1 by rw [he]; ring, Real.rpow_neg_one]
    rw [this]
    exact integral_inv_of_pos (by linarith) (lt_of_lt_of_le (by linarith : (0 : ℝ) < 2 * D) (le_max_left _ _))
  have hlog : Real.log (max (2 * D) R / (2 * D)) ≤ |Real.log (min 1 D)| := by
    rcases le_total R (2 * D) with h | h
    · rw [max_eq_left h, div_self (by positivity), Real.log_one]; exact abs_nonneg _
    · rw [max_eq_right h]
      have hD1 : D < 1 := by
        by_contra hc; push_neg at hc; linarith
      rw [min_eq_right hD1.le]
      have h1 : R / (2 * D) ≤ D⁻¹ := by
        rw [div_le_iff₀ (by positivity)]
        calc R ≤ 1 := hR1
          _ ≤ D⁻¹ * (2 * D) := by
              rw [inv_mul_eq_div, le_div_iff₀ hD]; linarith
      calc Real.log (R / (2 * D)) ≤ Real.log D⁻¹ :=
            Real.log_le_log (div_pos (lt_of_lt_of_le (by linarith : (0:ℝ) < 2 * D) h) (by linarith)) h1
        _ = -Real.log D := Real.log_inv D
        _ ≤ |Real.log D| := neg_le_abs _
  have t4 : ENNReal.ofReal (2 ^ e) * ENNReal.ofReal (ω * ∫ r in (2 * D)..(max (2 * D) R),
      r ^ ((d : ℝ) - 1 - (e + e))) ≤ ENNReal.ofReal (ω * (2 ^ e * |Real.log (min 1 D)|)) := by
    rw [hI4, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : (0 : ℝ) ≤ 2 ^ e := Real.rpow_nonneg (by norm_num) _
    have hlog0 : 0 ≤ Real.log (max (2 * D) R / (2 * D)) := Real.log_nonneg (by
      rw [le_div_iff₀ (by positivity)]; simpa using le_max_left (2 * D) R)
    calc 2 ^ e * (ω * Real.log (max (2 * D) R / (2 * D))) =
        ω * (2 ^ e * Real.log (max (2 * D) R / (2 * D))) := by ring
      _ ≤ ω * (2 ^ e * |Real.log (min 1 D)|) := by gcongr
  have hmin : |Real.log (min 1 D)| = |Real.log (min 1 D)| := rfl
  have hLnn : 0 ≤ |Real.log (min 1 D)| := abs_nonneg _
  rw [t1, t3]
  calc ENNReal.ofReal (ω / e) + ENNReal.ofReal (ω / e) + ENNReal.ofReal (ω * (4 ^ d / d)) +
        ENNReal.ofReal (2 ^ e) * ENNReal.ofReal (ω * ∫ r in (2 * D)..(max (2 * D) R),
          r ^ ((d : ℝ) - 1 - (e + e)))
      ≤ ENNReal.ofReal (ω / e) + ENNReal.ofReal (ω / e) + ENNReal.ofReal (ω * (4 ^ d / d)) +
        ENNReal.ofReal (ω * (2 ^ e * |Real.log (min 1 D)|)) := by gcongr
    _ = ENNReal.ofReal (ω / e + ω / e + ω * (4 ^ d / d) + ω * (2 ^ e * |Real.log (min 1 D)|)) := by
        have h1 : 0 ≤ ω / e := by positivity
        have h3 : 0 ≤ ω * (4 ^ d / d) := by positivity
        have h4 : 0 ≤ ω * (2 ^ e * |Real.log (min 1 D)|) :=
          mul_nonneg hω0 (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hLnn)
        rw [← ENNReal.ofReal_add h1 h1, ← ENNReal.ofReal_add (add_nonneg h1 h1) h3,
          ← ENNReal.ofReal_add (add_nonneg (add_nonneg h1 h1) h3) h4]
    _ = ENNReal.ofReal (ω * (2 / e + 4 ^ d / d + 2 ^ e * |Real.log (min 1 D)|)) := by
        congr 1; ring

end HRS.MS.R26T8A
