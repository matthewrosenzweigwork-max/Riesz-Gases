import HRS.Sections.AdjKBAux4

/-!
# ADJKB Aux5: constants and the assembled Kolmogorov-Chentsov tightness criterion
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

lemma adjkb_level_identity {T : ℝ} (hT : 0 < T) (M r p q : ℝ) (hr : 0 < r) (n : ℕ) :
    (2 : ℝ) ^ n * (M * (T / 2 ^ n) ^ q / (r ^ n) ^ p) =
      M * T ^ q * (2 / (2 ^ q * r ^ p)) ^ n := by
  have e1 : (T / 2 ^ n) ^ q = T ^ q / ((2 : ℝ) ^ q) ^ n := by
    rw [Real.div_rpow hT.le (by positivity)]
    congr 1
    rw [← Real.rpow_natCast (2 : ℝ) n, ← Real.rpow_mul (by norm_num), mul_comm,
      Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have e2 : (r ^ n) ^ p = (r ^ p) ^ n := by
    rw [← Real.rpow_natCast r n, ← Real.rpow_mul hr.le, mul_comm, Real.rpow_mul hr.le,
      Real.rpow_natCast]
  have h2q : 0 < (2 : ℝ) ^ q := by positivity
  have hrp : 0 < r ^ p := Real.rpow_pos_of_pos hr p
  rw [e1, e2, div_pow, mul_pow]
  field_simp

lemma adjkb_consts (p q : ℝ) (hp : 0 < p) (hq : 1 < q) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ 2 / ((2 : ℝ) ^ q * r ^ p) < 1 := by
  set e : ℝ := (q - 1) / (2 * p) with he
  have hepos : 0 < e := by rw [he]; apply div_pos <;> linarith
  refine ⟨(1 / 2 : ℝ) ^ e, by positivity, Real.rpow_lt_one (by norm_num) (by norm_num) hepos, ?_⟩
  have h1 : ((1 / 2 : ℝ) ^ e) ^ p = (1 / 2 : ℝ) ^ ((q - 1) / 2) := by
    rw [← Real.rpow_mul (by norm_num)]
    congr 1
    rw [he]; field_simp
  rw [h1]
  have h2 : (1 / 2 : ℝ) ^ ((q - 1) / 2) = ((2 : ℝ) ^ ((q - 1) / 2))⁻¹ := by
    rw [one_div, Real.inv_rpow (by norm_num)]
  have h3 : (2 : ℝ) ^ q * ((2 : ℝ) ^ ((q - 1) / 2))⁻¹ = (2 : ℝ) ^ ((q + 1) / 2) := by
    rw [← Real.rpow_neg (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1; ring
  rw [h2, h3]
  have h4 : (2 : ℝ) ^ (1 : ℝ) < (2 : ℝ) ^ ((q + 1) / 2) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  rw [Real.rpow_one] at h4
  rw [div_lt_one (by linarith)]
  exact h4

end HRS.AdjK
