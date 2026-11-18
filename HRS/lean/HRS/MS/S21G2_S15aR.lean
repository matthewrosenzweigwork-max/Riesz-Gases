import Mathlib

/-!
# S21G2 S15a (part R) -- real-variable helpers for the exponential tilt limit (R26-T3.S15a)

`s21g2_s15a_approx` (two-parameter approximation), the truncated weight `min (e^{-v}) L`, its tail bound
`e^{-v} - min (e^{-v}) L ≤ L^{1-r} e^{-r v}` and `e^{-v} ≤ 1 + e^{-r v}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

section Real

/-- An abstract two-parameter approximation lemma. -/
theorem s21g2_s15a_approx {a : ℕ → ℝ} {a' : ℝ} {b : ℕ → ℕ → ℝ} {b' δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0)) (hb : ∀ M, Tendsto (b M) atTop (𝓝 (b' M)))
    (h1 : ∀ M N, |a N - b M N| ≤ δ M) (h2 : ∀ M, |a' - b' M| ≤ δ M) : Tendsto a atTop (𝓝 a') := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := (hδ.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 3))).exists
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 (hb M) (ε / 3) (by linarith)
  refine ⟨N0, fun N hN => ?_⟩
  have := hN0 N hN
  rw [Real.dist_eq] at this ⊢
  have e1 := h1 M N
  have e2 := h2 M
  calc |a N - a'| = |(a N - b M N) + (b M N - b' M) + (b' M - a')| := by ring_nf
    _ ≤ |a N - b M N| + |b M N - b' M| + |b' M - a'| := abs_add_three _ _ _
    _ < ε := by rw [abs_sub_comm (b' M) a']; linarith

/-- The truncated weight `min (e^{-v}) L`. -/
def s21g2_s15a_psi (L v : ℝ) : ℝ := min (Real.exp (-v)) L

theorem s21g2_s15a_psi_cont (L : ℝ) : Continuous (s21g2_s15a_psi L) := by
  unfold s21g2_s15a_psi; fun_prop

theorem s21g2_s15a_psi_le (L v : ℝ) : s21g2_s15a_psi L v ≤ Real.exp (-v) := min_le_left _ _

theorem s21g2_s15a_psi_nonneg {L : ℝ} (hL : 0 ≤ L) (v : ℝ) : 0 ≤ s21g2_s15a_psi L v :=
  le_min (Real.exp_pos _).le hL

theorem s21g2_s15a_psi_le_L (L v : ℝ) : s21g2_s15a_psi L v ≤ L := min_le_right _ _

theorem s21g2_s15a_tail {L r : ℝ} (hL : 0 < L) (hr : 1 < r) (v : ℝ) :
    Real.exp (-v) - s21g2_s15a_psi L v ≤ L ^ (1 - r) * Real.exp (-r * v) := by
  unfold s21g2_s15a_psi
  have hx := Real.exp_pos (-v)
  have hxr : Real.exp (-r * v) = Real.exp (-v) ^ r := by
    rw [← Real.exp_mul]; ring_nf
  rcases le_or_gt (Real.exp (-v)) L with h | h
  · rw [min_eq_left h, sub_self]; positivity
  · rw [min_eq_right h.le, hxr]
    have h1 : Real.exp (-v) ^ (1 - r) ≤ L ^ (1 - r) :=
      Real.rpow_le_rpow_of_nonpos hL h.le (by linarith)
    have h2 : Real.exp (-v) = Real.exp (-v) ^ (1 - r) * Real.exp (-v) ^ r := by
      rw [← Real.rpow_add hx]; simp
    calc Real.exp (-v) - L ≤ Real.exp (-v) := by linarith
      _ = Real.exp (-v) ^ (1 - r) * Real.exp (-v) ^ r := h2
      _ ≤ L ^ (1 - r) * Real.exp (-v) ^ r := by gcongr

theorem s21g2_s15a_exp_le {r : ℝ} (hr : 1 ≤ r) (v : ℝ) :
    Real.exp (-v) ≤ 1 + Real.exp (-r * v) := by
  rcases le_or_gt (-v) 0 with h | h
  · have := Real.exp_le_one_iff.2 h
    have := Real.exp_pos (-r * v)
    linarith
  · have : -v ≤ -r * v := by nlinarith
    have := Real.exp_le_exp.2 this
    linarith [Real.exp_pos (-v)]

end Real

end HRS.MS.R26T3
