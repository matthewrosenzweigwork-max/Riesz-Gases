import HRS.Energy.Coercivity
import HRS.Energy.Modulated
import HRS.Whole.AppendixBEnergy

/-!
# U15 auxiliary lemmas: conversion `oNΛ → oN`, monotonicity of the transport bound
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.SuppU15

open HRS HRS.Whole

variable {d : ℕ}

/-- `oNΛ d s C₀ Λ N ≤ oN d s (C₀ Λ^{s/d} + log Λ/(2d)) N` for `Λ ≥ 1`, `N ≥ 1`, `0 ≤ s`, `d ≥ 1`. -/
lemma u15_oNΛ_le (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (C₀ Λ : ℝ) (hΛ : 1 ≤ Λ) {N : ℕ} (hN : 1 ≤ N) :
    oNΛ d s C₀ Λ N ≤ oN d s (C₀ * Λ ^ (s / d) + Real.log Λ / (2 * d)) N := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hΛpos : 0 < Λ := lt_of_lt_of_le one_pos hΛ
  have hlogΛ : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  unfold oNΛ oN
  by_cases h0 : s = 0
  · subst h0
    simp only [if_true, zero_div, Real.rpow_zero, mul_one, zero_sub, Real.rpow_neg_one]
    rw [Real.log_mul hNpos.ne' hΛpos.ne']
    field_simp
    linarith
  · simp only [h0, if_false, zero_add, add_zero]
    have : 0 ≤ Real.log Λ / (2 * d) := by positivity
    have hp : 0 < (N : ℝ) ^ (s / d - 1) := Real.rpow_pos_of_pos hNpos _
    nlinarith

lemma u15_hasFrac_mono {α p : ℝ} {v : Euc d → Euc d} {K K' : ℝ}
    (h : HasFracTransportBound α p v K) (hK : K ≤ K') : HasFracTransportBound α p v K' := by
  obtain ⟨L, F, hF, hl, hw, hLK⟩ := h
  exact ⟨L, F, hF, hl, hw, hLK.trans hK⟩

end HRS.MS.SuppU15
