import HRS.Main.A8PAux41

/-!
# Packet A8P, part 47: the smoothed absolute value `√(ε² + z²)`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

/-- The smoothed absolute value `G_ε(z) = √(ε² + z²)`. -/
def a8pG1 (ε z : ℝ) : ℝ := Real.sqrt (ε ^ 2 + z ^ 2)

/-- Its derivative `z / √(ε² + z²)`. -/
def a8pG1' (ε z : ℝ) : ℝ := z / Real.sqrt (ε ^ 2 + z ^ 2)

/-- Its second derivative `ε² / √(ε² + z²)³`. -/
def a8pG1'' (ε z : ℝ) : ℝ := ε ^ 2 / Real.sqrt (ε ^ 2 + z ^ 2) ^ 3

theorem a8pG1_pos {ε : ℝ} (hε : 0 < ε) (z : ℝ) : 0 < ε ^ 2 + z ^ 2 := by positivity

theorem a8pG1_hasDerivAt {ε : ℝ} (hε : 0 < ε) (z : ℝ) : HasDerivAt (a8pG1 ε) (a8pG1' ε z) z := by
  have h1 : HasDerivAt (fun z : ℝ => ε ^ 2 + z ^ 2) (2 * z) z := by
    simpa using ((hasDerivAt_pow 2 z).const_add (ε ^ 2))
  have h2 := h1.sqrt (a8pG1_pos hε z).ne'
  unfold a8pG1 a8pG1'
  convert h2 using 1
  field_simp

theorem a8pG1'_hasDerivAt {ε : ℝ} (hε : 0 < ε) (z : ℝ) : HasDerivAt (a8pG1' ε) (a8pG1'' ε z) z := by
  have hs : 0 < Real.sqrt (ε ^ 2 + z ^ 2) := Real.sqrt_pos.2 (a8pG1_pos hε z)
  have h1 : HasDerivAt (fun z : ℝ => ε ^ 2 + z ^ 2) (2 * z) z := by
    simpa using ((hasDerivAt_pow 2 z).const_add (ε ^ 2))
  have h2 := h1.sqrt (a8pG1_pos hε z).ne'
  have h3 : HasDerivAt (fun y : ℝ => y / Real.sqrt (ε ^ 2 + y ^ 2))
      ((1 * Real.sqrt (ε ^ 2 + z ^ 2) - z * (2 * z / (2 * Real.sqrt (ε ^ 2 + z ^ 2)))) /
        Real.sqrt (ε ^ 2 + z ^ 2) ^ 2) z := (hasDerivAt_id z).div h2 hs.ne'
  unfold a8pG1' a8pG1''
  convert h3 using 1
  have hsq : Real.sqrt (ε ^ 2 + z ^ 2) ^ 2 = ε ^ 2 + z ^ 2 := Real.sq_sqrt (a8pG1_pos hε z).le
  rw [eq_div_iff (by positivity)]
  field_simp
  nlinarith [hsq]

theorem a8pG1_contDiff {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 2 (a8pG1 ε) := by
  unfold a8pG1
  exact ((contDiff_const.add (contDiff_id.pow 2)).sqrt (fun z => (a8pG1_pos hε z).ne'))

theorem a8pG1'_abs_le {ε : ℝ} (hε : 0 < ε) (z : ℝ) : |a8pG1' ε z| ≤ 1 := by
  unfold a8pG1'
  have hs : 0 < Real.sqrt (ε ^ 2 + z ^ 2) := Real.sqrt_pos.2 (a8pG1_pos hε z)
  rw [abs_div, abs_of_pos hs, div_le_one hs]
  calc |z| = Real.sqrt (z ^ 2) := (Real.sqrt_sq_eq_abs z).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ε])

theorem a8pG1''_nonneg {ε : ℝ} (hε : 0 < ε) (z : ℝ) : 0 ≤ a8pG1'' ε z := by
  unfold a8pG1''
  have hs : 0 < Real.sqrt (ε ^ 2 + z ^ 2) := Real.sqrt_pos.2 (a8pG1_pos hε z)
  positivity

theorem a8pG1''_ge {ε : ℝ} (hε : 0 < ε) {z : ℝ} (hz : |z| ≤ ε) : 1 / (8 * ε) ≤ a8pG1'' ε z := by
  unfold a8pG1''
  have hs : 0 < Real.sqrt (ε ^ 2 + z ^ 2) := Real.sqrt_pos.2 (a8pG1_pos hε z)
  have hz2 : z ^ 2 ≤ ε ^ 2 := by
    have := sq_le_sq' (by linarith [abs_le.1 hz |>.1]) (abs_le.1 hz |>.2)
    exact this
  have hle : Real.sqrt (ε ^ 2 + z ^ 2) ≤ 2 * ε := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have h3 : Real.sqrt (ε ^ 2 + z ^ 2) ^ 3 ≤ (2 * ε) ^ 3 := pow_le_pow_left₀ hs.le hle 3
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [h3, sq_nonneg ε, mul_pos hε hε]

theorem a8pG1_lip {ε : ℝ} (hε : 0 < ε) (z w : ℝ) : |a8pG1 ε z - a8pG1 ε w| ≤ |z - w| := by
  unfold a8pG1
  set a := Real.sqrt (ε ^ 2 + z ^ 2) with ha
  set b := Real.sqrt (ε ^ 2 + w ^ 2) with hb
  have ha0 : 0 < a := Real.sqrt_pos.2 (a8pG1_pos hε z)
  have hb0 : 0 < b := Real.sqrt_pos.2 (a8pG1_pos hε w)
  have ha2 : a ^ 2 = ε ^ 2 + z ^ 2 := Real.sq_sqrt (a8pG1_pos hε z).le
  have hb2 : b ^ 2 = ε ^ 2 + w ^ 2 := Real.sq_sqrt (a8pG1_pos hε w).le
  have hza : |z| ≤ a := by
    calc |z| = Real.sqrt (z ^ 2) := (Real.sqrt_sq_eq_abs z).symm
      _ ≤ a := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ε])
  have hwb : |w| ≤ b := by
    calc |w| = Real.sqrt (w ^ 2) := (Real.sqrt_sq_eq_abs w).symm
      _ ≤ b := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ε])
  have hkey : (a - b) * (a + b) = (z - w) * (z + w) := by nlinarith
  have hab : 0 < a + b := by linarith
  have hzw : |z + w| ≤ a + b := (abs_add_le z w).trans (by linarith)
  refine le_of_mul_le_mul_right ?_ hab
  have e1 : |a - b| * (a + b) = |(a - b) * (a + b)| := by
    rw [abs_mul, abs_of_pos hab]
  rw [e1, hkey, abs_mul]
  exact mul_le_mul_of_nonneg_left hzw (abs_nonneg _)

end HRS.Main.A8P
