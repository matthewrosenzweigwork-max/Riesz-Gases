import HRS.MS.CritForceMom5

/-!
# S8.2 NormalForm packet R03, part 6: the repulsion cutoff and the pole-power rows

Profile bounds for `pole^k exp(-A r^{-s})` (`k = 2, 4`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MS.S82N

open HRS HRS.Whole

variable {d : ℕ}

lemma s82n_exp_neg_le (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t) ≤ (k : ℝ) ^ k / (1 + t) ^ k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : (t / k + 1) ^ k ≤ Real.exp t := by
    have h2 : t / k + 1 ≤ Real.exp (t / k) := Real.add_one_le_exp _
    have h3 : Real.exp t = Real.exp (t / k) ^ k := by
      rw [← Real.exp_nat_mul]; congr 1; field_simp
    rw [h3]; exact pow_le_pow_left₀ (by positivity) h2 k
  have h4 : (1 + t) ^ k ≤ (k : ℝ) ^ k * (t / k + 1) ^ k := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ k
    have : (k : ℝ) * (t / k + 1) = t + k := by field_simp
    rw [this]; linarith
  have h5 : (1 + t) ^ k ≤ (k : ℝ) ^ k * Real.exp t :=
    h4.trans (by gcongr)
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  linarith

lemma s82n_exp_neg_le_one_add (t : ℝ) (ht : 0 ≤ t) : Real.exp (-t) ≤ 1 / (1 + t) := by
  have := s82n_exp_neg_le 1 le_rfl t ht
  simpa using this

/-- E3 profile: `r^{d-1} (1 + r^{-s})² exp(-A r^{-s}) ≤ 2 r^{d-1} + 2 r^{s-1}/(r^s + A)`. -/
lemma s82n_E3_profile (hd : 2 ≤ d) (A r : ℝ) (hA : 0 < A) (hr : 0 < r) :
    r ^ (d - 1) * ((1 + r ^ (-s82n_critS d)) ^ 2 * Real.exp (-(A * r ^ (-s82n_critS d)))) ≤
      2 * r ^ (d - 1) + 2 * (r ^ (s82n_critS d - 1) / (r ^ s82n_critS d + A) ^ 1) := by
  obtain ⟨f1, f2, f3, -⟩ := s82n_rpow_forms (by omega : 1 ≤ d) r hr
  have hs := s82n_critS_pos (by omega : 1 ≤ d)
  set w := r ^ s82n_critS d with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos hr _
  have hP0 : 0 ≤ r ^ (d - 1) := by positivity
  rw [f3]
  set t := A * w⁻¹ with ht
  have ht0 : 0 ≤ t := by positivity
  have he := s82n_exp_neg_le_one_add t ht0
  have hsq : (1 + w⁻¹) ^ 2 ≤ 2 + 2 * (w⁻¹) ^ 2 := by nlinarith [sq_nonneg (1 - w⁻¹)]
  have h1 : (1 + w⁻¹) ^ 2 * Real.exp (-t) ≤ (2 + 2 * (w⁻¹) ^ 2) * (1 / (1 + t)) := by
    gcongr
  have h2 : r ^ (d - 1) * ((2 + 2 * (w⁻¹) ^ 2) * (1 / (1 + t))) =
      2 * r ^ (d - 1) * (1 / (1 + t)) + 2 * (r ^ (s82n_critS d - 1) / (w + A) ^ 1) := by
    rw [f1, f2, ht]
    field_simp
  have h3 : 2 * r ^ (d - 1) * (1 / (1 + t)) ≤ 2 * r ^ (d - 1) := by
    have : 1 / (1 + t) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    nlinarith
  calc r ^ (d - 1) * ((1 + w⁻¹) ^ 2 * Real.exp (-t)) ≤
        r ^ (d - 1) * ((2 + 2 * (w⁻¹) ^ 2) * (1 / (1 + t))) := by gcongr
    _ = _ := h2
    _ ≤ _ := by linarith

/-- E4 profile: `r^{d-1} (1 + r^{-s})⁴ exp(-A r^{-s}) ≤ 8 r^{d-1} + 216 r^{s-1}/(r^s + A)³`. -/
lemma s82n_E4_profile (hd : 2 ≤ d) (A r : ℝ) (hA : 0 < A) (hr : 0 < r) :
    r ^ (d - 1) * ((1 + r ^ (-s82n_critS d)) ^ 4 * Real.exp (-(A * r ^ (-s82n_critS d)))) ≤
      8 * r ^ (d - 1) + 216 * (r ^ (s82n_critS d - 1) / (r ^ s82n_critS d + A) ^ 3) := by
  obtain ⟨f1, f2, f3, -⟩ := s82n_rpow_forms (by omega : 1 ≤ d) r hr
  have hs := s82n_critS_pos (by omega : 1 ≤ d)
  set w := r ^ s82n_critS d with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos hr _
  have hP0 : 0 ≤ r ^ (d - 1) := by positivity
  rw [f3]
  set t := A * w⁻¹ with ht
  have ht0 : 0 ≤ t := by positivity
  have he3 := s82n_exp_neg_le 3 (by norm_num) t ht0
  have he0 : Real.exp (-t) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have hu : 0 ≤ w⁻¹ := by positivity
  have hsq : (1 + w⁻¹) ^ 4 ≤ 8 + 8 * (w⁻¹) ^ 4 := by
    nlinarith [sq_nonneg (1 - w⁻¹), sq_nonneg (1 + w⁻¹), sq_nonneg (1 - (w⁻¹) ^ 2),
      sq_nonneg (w⁻¹), pow_nonneg hu 3, pow_nonneg hu 4, mul_nonneg hu (sq_nonneg (1 - w⁻¹))]
  have hP1 : r ^ (d - 1) * ((1 + w⁻¹) ^ 4 * Real.exp (-t)) ≤
      r ^ (d - 1) * ((8 + 8 * (w⁻¹) ^ 4) * Real.exp (-t)) := by gcongr
  have hP2 : r ^ (d - 1) * ((8 + 8 * (w⁻¹) ^ 4) * Real.exp (-t)) =
      8 * r ^ (d - 1) * Real.exp (-t) + 8 * r ^ (d - 1) * (w⁻¹) ^ 4 * Real.exp (-t) := by ring
  have hP3 : 8 * r ^ (d - 1) * Real.exp (-t) ≤ 8 * r ^ (d - 1) := by
    have := mul_le_mul_of_nonneg_left he0 (by positivity : 0 ≤ 8 * r ^ (d - 1))
    simpa using this
  have hP4 : 8 * r ^ (d - 1) * (w⁻¹) ^ 4 * Real.exp (-t) ≤
      8 * r ^ (d - 1) * (w⁻¹) ^ 4 * (((3 : ℕ) : ℝ) ^ 3 / (1 + t) ^ 3) := by gcongr
  have hP5 : 8 * r ^ (d - 1) * (w⁻¹) ^ 4 * (((3 : ℕ) : ℝ) ^ 3 / (1 + t) ^ 3) =
      216 * (r ^ (s82n_critS d - 1) / (w + A) ^ 3) := by
    rw [f1, f2, ht]
    push_cast
    field_simp
    ring
  linarith

end HRS.MS.S82N
