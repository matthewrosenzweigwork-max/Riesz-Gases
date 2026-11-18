import Mathlib

/-!
# S11.2 (b), (c): the real-analysis reduction

From either `√N e^{-2κ u_N} → 0` or `u_N ≥ (1/(4κ) + δ) log N`, both `√N e^{-2κ u_N}` and `e^{-c u_N}` tend to `0`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Filter Topology

namespace HRS.MS.R2S11

theorem s11_exp_tendsto_of_ge_log {κ δ c : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) (hc : 0 < c) (uN : ℕ → ℝ)
    (hu : ∀ N : ℕ, 2 ≤ N → (1 / (4 * κ) + δ) * Real.log N ≤ uN N) :
    Tendsto (fun N : ℕ => Real.sqrt N * Real.exp (-2 * κ * uN N)) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => Real.exp (-c * uN N)) atTop (𝓝 0) := by
  have hN0 : ∀ N : ℕ, 2 ≤ N → (0 : ℝ) < N := fun N hN => Nat.cast_pos.2 (by omega)
  have hE : 0 < 1 / (4 * κ) + δ := by positivity
  have key : ∀ a : ℝ, 0 < a → ∀ N : ℕ, 2 ≤ N →
      Real.exp (-a * uN N) ≤ (N : ℝ) ^ (-(a * (1 / (4 * κ) + δ))) := by
    intro a ha N hN
    have h1 : -a * uN N ≤ -(a * (1 / (4 * κ) + δ)) * Real.log N := by
      have := hu N hN
      nlinarith
    calc Real.exp (-a * uN N) ≤ Real.exp (-(a * (1 / (4 * κ) + δ)) * Real.log N) := Real.exp_le_exp.2 h1
      _ = (N : ℝ) ^ (-(a * (1 / (4 * κ) + δ))) := by
          rw [Real.rpow_def_of_pos (hN0 N hN)]; congr 1; ring
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  refine ⟨?_, ?_⟩
  · have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(2 * κ * δ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by positivity)).comp hnat
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun N => by positivity) ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have h2 := key (2 * κ) (by positivity) N hN
    have e : -2 * κ * uN N = -(2 * κ) * uN N := by ring
    rw [e]
    calc Real.sqrt N * Real.exp (-(2 * κ) * uN N)
        ≤ Real.sqrt N * (N : ℝ) ^ (-(2 * κ * (1 / (4 * κ) + δ))) :=
          mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
      _ = (N : ℝ) ^ (-(2 * κ * δ)) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add (hN0 N hN)]
          congr 1
          field_simp
          ring
  · have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(c * (1 / (4 * κ) + δ)))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by positivity)).comp hnat
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun N => (Real.exp_pos _).le) ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact key c hc N hN

theorem s11_exp_tendsto_of_sqrt {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c) (uN : ℕ → ℝ)
    (h : Tendsto (fun N : ℕ => Real.sqrt N * Real.exp (-2 * κ * uN N)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => Real.exp (-c * uN N)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => Real.exp (-2 * κ * uN N)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
      (Eventually.of_forall fun N => (Real.exp_pos _).le) ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have : (1 : ℝ) ≤ Real.sqrt N := by
      rw [Real.one_le_sqrt]; exact_mod_cast hN
    nlinarith [Real.exp_pos (-2 * κ * uN N)]
  have h2 := h1.rpow_const (p := c / (2 * κ)) (Or.inr (by positivity))
  rw [Real.zero_rpow (by positivity)] at h2
  refine h2.congr fun N => ?_
  rw [← Real.exp_mul]
  congr 1
  field_simp

end HRS.MS.R2S11
