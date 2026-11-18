import Mathlib

/-!
# S2.1(iii) packet G5: the abstract passage `R_N ≤ α_N + C_L e_N(L+T) + C e^{-cL}` ⟹ one sequence `ε_N → 0`

Paper, section 7 (`eq:remainder`): for every fixed `L > 0` the uniform remainder obeys `R_N ≤ α_N + A_N^L + C e^{-cL}` with `α_N → 0`, `A_N^L → 0`; first `N → ∞`, then `L → ∞`.
Then `ε_N := sup R_N` (finite for every `N ≥ 2`) tends to zero and dominates every error.  Index type `ι` = (window start `b ≥ 0`, test function `Φ` in the `C_b^5` ball).
-/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace HRS.MS.S21E

/-- First `N → ∞` at fixed `L`, then `L → ∞`: the remainder is eventually below every `η > 0`, uniformly over the index. -/
theorem s21e_uniform_of_decomp {ι : Type*} (E : ℕ → ι → ℝ) (C c : ℝ) (hc : 0 < c)
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 0))
    (hdec : ∀ L : ℝ, 0 < L → ∃ A : ℕ → ℝ, Tendsto A atTop (𝓝 0) ∧
      ∀ N : ℕ, 2 ≤ N → ∀ i, E N i ≤ α N + A N + C * Real.exp (-c * L)) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 2 ≤ N → ∀ i, E N i ≤ η := by
  intro η hη
  -- choose `L` with `C e^{-cL} ≤ η/3`
  have hexp : Tendsto (fun L : ℝ => |C| * Real.exp (-c * L)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun L : ℝ => -c * L) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by linarith)
    have h2 := Real.tendsto_exp_atBot.comp h1
    simpa using h2.const_mul |C|
  obtain ⟨L₀, hL₀⟩ := (hexp.eventually (gt_mem_nhds (show (0 : ℝ) < η / 3 by positivity))).exists_forall_of_atTop
  set L : ℝ := max L₀ 1 with hL
  have hLpos : 0 < L := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hCL : C * Real.exp (-c * L) ≤ η / 3 := by
    have := hL₀ L (le_max_left _ _)
    calc C * Real.exp (-c * L) ≤ |C| * Real.exp (-c * L) := by
          gcongr; exact le_abs_self C
      _ ≤ η / 3 := this.le
  obtain ⟨A, hA, hdecL⟩ := hdec L hLpos
  have h1 : ∀ᶠ N in atTop, α N < η / 3 := hα.eventually (gt_mem_nhds (by positivity))
  have h2 : ∀ᶠ N in atTop, A N < η / 3 := hA.eventually (gt_mem_nhds (by positivity))
  obtain ⟨N₀, hN₀⟩ := (h1.and h2).exists_forall_of_atTop
  refine ⟨N₀, fun N hN hN2 i => ?_⟩
  have := hdecL N hN2 i
  have hh := hN₀ N hN
  linarith [hh.1, hh.2]

/-- One sequence `ε_N → 0` dominating the errors `E N i` for `N ≥ 2` (finite for each `N ≥ 2`, uniform smallness for large `N`). -/
theorem s21e_eps_of_uniform {ι : Type*} (E : ℕ → ι → ℝ) (hE0 : ∀ N i, 0 ≤ E N i)
    (hfin : ∀ N : ℕ, 2 ≤ N → ∃ M : ℝ, ∀ i, E N i ≤ M)
    (hlim : ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 2 ≤ N → ∀ i, E N i ≤ η) :
    ∃ εN : ℕ → ℝ, Tendsto εN atTop (𝓝 0) ∧ ∀ N : ℕ, 2 ≤ N → ∀ i, E N i ≤ εN N := by
  classical
  refine ⟨fun N => if 2 ≤ N then ⨆ i, E N i else 0, ?_, ?_⟩
  · rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨N₀, hN₀⟩ := hlim (η / 2) (by positivity)
    refine ⟨max N₀ 2, fun N hN => ?_⟩
    have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
    have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
    simp only [if_pos hN2, Real.dist_eq, sub_zero]
    have hle : (⨆ i, E N i) ≤ η / 2 := by
      by_cases hne : Nonempty ι
      · exact ciSup_le fun i => hN₀ N hN0 hN2 i
      · haveI : IsEmpty ι := not_nonempty_iff.1 hne
        rw [Real.iSup_of_isEmpty]; positivity
    have h0 : 0 ≤ (⨆ i, E N i) := Real.iSup_nonneg fun i => hE0 N i
    rw [abs_of_nonneg h0]
    linarith
  · intro N hN i
    simp only [if_pos hN]
    obtain ⟨M, hM⟩ := hfin N hN
    exact le_ciSup ⟨M, by rintro _ ⟨j, rfl⟩; exact hM j⟩ i

/-- Both steps together. -/
theorem s21e_eps_of_decomp {ι : Type*} (E : ℕ → ι → ℝ) (hE0 : ∀ N i, 0 ≤ E N i) (C c : ℝ) (hc : 0 < c)
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 0))
    (hdec : ∀ L : ℝ, 0 < L → ∃ A : ℕ → ℝ, Tendsto A atTop (𝓝 0) ∧
      ∀ N : ℕ, 2 ≤ N → ∀ i, E N i ≤ α N + A N + C * Real.exp (-c * L))
    (hfin : ∀ N : ℕ, 2 ≤ N → ∃ M : ℝ, ∀ i, E N i ≤ M) :
    ∃ εN : ℕ → ℝ, Tendsto εN atTop (𝓝 0) ∧ ∀ N : ℕ, 2 ≤ N → ∀ i, E N i ≤ εN N :=
  s21e_eps_of_uniform E hE0 hfin (s21e_uniform_of_decomp E C c hc α hα hdec)

end HRS.MS.S21E
