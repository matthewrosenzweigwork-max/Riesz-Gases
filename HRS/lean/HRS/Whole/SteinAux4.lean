import HRS.Whole.SteinAux3

/-!
# Packet STEIN, auxiliary file 4: the smooth truncation `t ↦ R arctan (t / R)`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ContDiff

namespace HRS.Whole.Stein

/-- Smooth bounded truncation, `atr R t = R arctan (t / R)`. -/
def atr (R t : ℝ) : ℝ := R * Real.arctan (t / R)

/-- Its derivative. -/
def datr (R t : ℝ) : ℝ := 1 / (1 + (t / R) ^ 2)

lemma atr_contDiff (R : ℝ) {m : WithTop ℕ∞} : ContDiff ℝ m (atr R) := by
  unfold atr
  exact contDiff_const.mul (Real.contDiff_arctan.comp (contDiff_id.div_const R))

lemma hasDerivAt_atr {R : ℝ} (hR : R ≠ 0) (t : ℝ) : HasDerivAt (atr R) (datr R t) t := by
  unfold atr datr
  have h1 : HasDerivAt (fun t : ℝ => t / R) (1 / R) t := (hasDerivAt_id t).div_const R
  have h2 := (h1.arctan).const_mul R
  convert h2 using 1
  field_simp

lemma datr_pos (R t : ℝ) : 0 < datr R t := by unfold datr; positivity

lemma datr_le_one (R t : ℝ) : datr R t ≤ 1 := by
  unfold datr
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg (t / R)]

lemma abs_datr_le (R t : ℝ) : |datr R t| ≤ 1 := by
  rw [abs_of_pos (datr_pos R t)]; exact datr_le_one R t

lemma datr_lip {R : ℝ} (hR : 0 < R) (s t : ℝ) : |datr R s - datr R t| ≤ |s - t| / R := by
  unfold datr
  set x := s / R with hx
  set y := t / R with hy
  have hxy : |s - t| / R = |x - y| := by
    rw [hx, hy, ← sub_div, abs_div, abs_of_pos hR]
  rw [hxy]
  have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have h2 : (0 : ℝ) < 1 + y ^ 2 := by positivity
  rw [div_sub_div _ _ h1.ne' h2.ne', abs_div, abs_of_pos (mul_pos h1 h2), div_le_iff₀ (mul_pos h1 h2)]
  have e : 1 * (1 + y ^ 2) - (1 + x ^ 2) * 1 = (x - y) * (-(x + y)) := by ring
  rw [e, abs_mul, abs_neg]
  have h3 : |x + y| ≤ (1 + x ^ 2) * (1 + y ^ 2) := by
    have a1 : |x| ≤ (1 + x ^ 2) / 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (|x| - 1), sq_abs x, abs_nonneg x, neg_abs_le x, le_abs_self x]
    have a2 : |y| ≤ (1 + y ^ 2) / 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (|y| - 1), sq_abs y, abs_nonneg y, neg_abs_le y, le_abs_self y]
    have a3 := abs_add_le x y
    nlinarith [sq_nonneg x, sq_nonneg y, mul_nonneg (sq_nonneg x) (sq_nonneg y)]
  calc |x - y| * |x + y| ≤ |x - y| * ((1 + x ^ 2) * (1 + y ^ 2)) :=
        mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    _ = _ := by ring

lemma abs_arctan_le (s : ℝ) : |Real.arctan s| ≤ |s| := by
  have h : ‖Real.arctan s - Real.arctan 0‖ ≤ 1 * ‖s - 0‖ := by
    refine Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := Real.arctan) (C := 1)
      (s := Set.univ) (fun x _ => Real.differentiableAt_arctan x) (fun x _ => ?_) convex_univ
      (Set.mem_univ _) (Set.mem_univ _)
    rw [Real.deriv_arctan]
    simp only [norm_div, norm_one, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity : (0 : ℝ) < 1 + x ^ 2)]
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg x]
  simpa using h

lemma abs_atr_le (R t : ℝ) (hR : 0 < R) : |atr R t| ≤ |t| := by
  unfold atr
  rw [abs_mul, abs_of_pos hR]
  calc R * |Real.arctan (t / R)| ≤ R * |t / R| := mul_le_mul_of_nonneg_left (abs_arctan_le _) hR.le
    _ = |t| := by rw [abs_div, abs_of_pos hR]; field_simp

lemma abs_atr_le_bound (R t : ℝ) (hR : 0 < R) : |atr R t| ≤ R * (Real.pi / 2) := by
  unfold atr
  rw [abs_mul, abs_of_pos hR]
  refine mul_le_mul_of_nonneg_left ?_ hR.le
  rw [abs_le]
  exact ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩

lemma atr_tendsto (t : ℝ) : Tendsto (fun R : ℝ => atr R t) atTop (𝓝 t) := by
  by_cases ht : t = 0
  · subst ht; simp [atr]
  · have h0 := (Real.hasDerivAt_arctan 0).tendsto_slope_zero
    have hlim : Tendsto (fun R : ℝ => t / R) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact tendsto_const_nhds.div_atTop tendsto_id
      · filter_upwards [eventually_gt_atTop 0] with R hR
        exact div_ne_zero ht hR.ne'
    have h1 := (h0.comp hlim).const_mul t
    simp only [Real.arctan_zero, zero_add, sub_zero, smul_eq_mul, Function.comp_def,
      one_div, one_pow, add_zero, div_one] at h1
    rw [show t * (1 + (0 : ℝ) ^ 2)⁻¹ = t by norm_num] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    unfold atr
    field_simp

end HRS.Whole.Stein
