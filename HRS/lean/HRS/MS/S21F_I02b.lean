import HRS.MS.S21F_I02a
import HRS.MS.R2InterpAux3

/-!
# S21F, packet R26-T3.I02 (part b): real-series facts for the cosine synthesis

`w_n = (1+n²)^{-3/8}`: `∑ w_n² < ∞`; `|cos_n(u)| ≤ A := T^{-1/2} + (2/T)^{1/2}`; and the Hölder estimate
`∑_n w_n ‖slice_n z‖ ≤ (∑ w²)^{1/2} ‖z‖`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3
open HRS HRS.Whole

def s21f_w (n : ℕ) : ℝ := (1 + (n : ℝ) ^ 2) ^ (-(3 / 8 : ℝ))

theorem s21f_w_pos (n : ℕ) : 0 < s21f_w n := Real.rpow_pos_of_pos (by positivity) _

theorem s21f_w_sq (n : ℕ) : s21f_w n ^ 2 = (1 + (n : ℝ) ^ 2) ^ (-(3 / 4 : ℝ)) := by
  unfold s21f_w
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num

theorem s21f_w_sq_summable : Summable fun n : ℕ => s21f_w n ^ 2 := by
  have h1 : Summable fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ (-(3 / 2 : ℝ)) :=
    (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by norm_num))
  refine Summable.of_nonneg_of_le (fun n => (sq_nonneg _)) (fun n => ?_) (h1.mul_left (2 ^ (3 / 4 : ℝ)))
  rw [s21f_w_sq]
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hx : ((n : ℝ) + 1) ^ 2 / 2 ≤ 1 + (n : ℝ) ^ 2 := by nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have h2 := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < ((n : ℝ) + 1) ^ 2 / 2) hx
    (by norm_num : -(3 / 4 : ℝ) ≤ 0)
  refine h2.trans (le_of_eq ?_)
  have h2n : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by positivity
  have ha : (((n : ℝ) + 1) ^ 2) ^ (-(3 / 4 : ℝ)) = ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]; norm_num
  have hb : (2 : ℝ) ^ (-(3 / 4 : ℝ)) = ((2 : ℝ) ^ (3 / 4 : ℝ))⁻¹ := Real.rpow_neg (by norm_num) _
  rw [Real.div_rpow h2n (by norm_num), ha, hb, div_inv_eq_mul, mul_comm]
  push_cast
  rfl

theorem s21f_cos_bound {T : ℝ} (hT : 0 < T) (n : ℕ) (u : ℝ) :
    |r26t3_cosine T n u| ≤ (Real.sqrt T)⁻¹ + Real.sqrt (2 / T) := by
  unfold r26t3_cosine
  have h1 : 0 ≤ (Real.sqrt T)⁻¹ := by positivity
  have h2 : 0 ≤ Real.sqrt (2 / T) := Real.sqrt_nonneg _
  split_ifs
  · rw [abs_of_nonneg h1]; linarith
  · rw [abs_mul, abs_of_nonneg h2]
    have := Real.abs_cos_le_one ((n : ℝ) * Real.pi * u / T)
    nlinarith

theorem s21f_cos_cont (T : ℝ) (n : ℕ) : Continuous (r26t3_cosine T n) := by
  unfold r26t3_cosine
  split_ifs <;> fun_prop

/-- Hölder: `∑ w_n ‖slice_n z‖ ≤ (∑ w²)^{1/2} ‖z‖`, and the series is summable. -/
theorem s21f_holder {d : ℕ} {m : ℝ} (e : ℕ ≃ ℕ × MultiIndex d) (z : SeqL2) :
    Summable (fun n : ℕ => s21f_w n * ‖s21f_slice (m := m) e n z‖) ∧
      ∑' n : ℕ, s21f_w n * ‖s21f_slice (m := m) e n z‖ ≤ Real.sqrt (∑' n : ℕ, s21f_w n ^ 2) * ‖z‖ := by
  obtain ⟨hs, hsum⟩ := s21f_slice_sq (m := m) e z
  have hp : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hf : Summable fun n : ℕ => s21f_w n ^ (2 : ℝ) := by
    simpa [Real.rpow_two] using s21f_w_sq_summable
  have hg : Summable fun n : ℕ => ‖s21f_slice (m := m) e n z‖ ^ (2 : ℝ) := by
    simpa [Real.rpow_two] using hs
  obtain ⟨h1, h2⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hp (fun n => (s21f_w_pos n).le)
    (fun n => norm_nonneg _) hf hg
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  have hsum' : ∑' n : ℕ, ‖s21f_slice (m := m) e n z‖ ^ (2 : ℝ) = ‖z‖ ^ 2 := by
    simpa [Real.rpow_two] using hsum
  have hw' : ∑' n : ℕ, s21f_w n ^ (2 : ℝ) = ∑' n : ℕ, s21f_w n ^ 2 := by simp [Real.rpow_two]
  rw [hsum', hw', ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]

end HRS.MS.R26T3
