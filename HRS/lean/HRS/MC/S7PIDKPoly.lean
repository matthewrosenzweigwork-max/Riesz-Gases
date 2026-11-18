import HRS.MC.S7PIDPPoly

/-!
# Packet PI-D, sub-packet K (part 1): the polygonal interpolation of a continuous function converges to it

For `c < c'`, `t ∈ [c,c']` and a function `F : ℝ → E` continuous at `t` within `[c,c']`, the polygonal interpolation of the
dyadic node values `F (gridPt c c' n i)` evaluated at `t` converges to `F t` as `n → ∞` (two-term hat formula).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDK

open HRS HRS.Sec7 HRS.MC.Sec7.PID

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem S7PIDK_polyAt_tendsto (c c' : ℝ) (hc : 0 ≤ c) (hcc : c < c') (F : ℝ → E) (t : ℝ) (ht : t ∈ Set.Icc c c')
    (hF : ContinuousWithinAt F (Set.Icc c c') t) :
    Tendsto (fun n : ℕ => polyAt c c' n (fun i => F (gridPt c c' n i)) t) atTop (𝓝 (F t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨η, hη, hηF⟩ := Metric.continuousWithinAt_iff.1 hF (ε / 2) (half_pos hε)
  have hΔ : 0 < c' - c := sub_pos.2 hcc
  -- choose `N` with `(c'-c)/2^N < η`
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hη hΔ) (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨N, fun n hn => ?_⟩
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hδ : (c' - c) / 2 ^ n < η := by
    have h1 : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    have h3 : (1 / 2 : ℝ) ^ n < η / (c' - c) := lt_of_le_of_lt h1 hN
    rw [lt_div_iff₀ hΔ] at h3
    calc (c' - c) / 2 ^ n = (1 / 2 : ℝ) ^ n * (c' - c) := by rw [one_div, inv_pow]; field_simp
      _ < η := h3
  -- the position
  set X : ℝ := (max c (min t c') - c) / (c' - c) * (2 : ℝ) ^ n with hX
  have hmm : max c (min t c') = t := by
    rw [min_eq_left ht.2, max_eq_right ht.1]
  have hX' : X = (t - c) / (c' - c) * 2 ^ n := by rw [hX, hmm]
  obtain ⟨hX0, hXN⟩ := S7PIDP.S7PIDP_X_bounds c c' t hc hcc.le n
  rw [← hX] at hX0 hXN
  have hsum := S7PIDP.S7PIDP_hat_sum (2 ^ n) X hX0 hXN (fun i => F (gridPt c c' n i))
  have hpa : polyAt c c' n (fun i => F (gridPt c c' n i)) t =
      (1 - (X - (⌊X⌋₊ : ℝ))) • F (gridPt c c' n ⌊X⌋₊) + (X - (⌊X⌋₊ : ℝ)) • F (gridPt c c' n (⌊X⌋₊ + 1)) := by
    unfold polyAt
    exact hsum
  set j : ℕ := ⌊X⌋₊ with hj
  set θ : ℝ := X - (j : ℝ) with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith [Nat.floor_le hX0]
  have hθ1 : θ < 1 := by rw [hθ]; linarith [Nat.lt_floor_add_one X]
  have hjN : (j : ℝ) ≤ 2 ^ n := by
    have : (j : ℝ) ≤ X := Nat.floor_le hX0
    have h4 : X ≤ ((2 ^ n : ℕ) : ℝ) := hXN
    push_cast at h4
    linarith
  have ht_eq : t = c + (c' - c) * X / 2 ^ n := by
    rw [hX']; field_simp; ring
  have hg : ∀ i : ℕ, gridPt c c' n i = c + (c' - c) * i / 2 ^ n := fun i => rfl
  have hmemg : ∀ i : ℕ, (i : ℝ) ≤ 2 ^ n → gridPt c c' n i ∈ Set.Icc c c' := by
    intro i hi
    rw [hg]
    constructor
    · have : 0 ≤ (c' - c) * i / 2 ^ n := by positivity
      linarith
    · have : (c' - c) * i / 2 ^ n ≤ c' - c := by
        rw [div_le_iff₀ h2]
        nlinarith [mul_le_mul_of_nonneg_left hi hΔ.le]
      linarith
  have hA : ‖F (gridPt c c' n j) - F t‖ ≤ ε / 2 := by
    have hd : dist (gridPt c c' n j) t < η := by
      rw [Real.dist_eq, hg, ht_eq]
      have e : c + (c' - c) * (j : ℝ) / 2 ^ n - (c + (c' - c) * X / 2 ^ n) = -((c' - c) * θ / 2 ^ n) := by
        rw [hθ]; field_simp; ring
      rw [e, abs_neg, abs_of_nonneg (by positivity)]
      calc (c' - c) * θ / 2 ^ n ≤ (c' - c) * 1 / 2 ^ n := by gcongr
        _ < η := by rw [mul_one]; exact hδ
    have := hηF (hmemg j hjN) hd
    rw [dist_eq_norm] at this
    exact this.le
  have hB : ‖θ • (F (gridPt c c' n (j + 1)) - F t)‖ ≤ θ * (ε / 2) := by
    rcases eq_or_lt_of_le hθ0 with h0 | hpos
    · rw [← h0]; simp
    · have hj1 : j + 1 ≤ 2 ^ n := S7PIDP.S7PIDP_floor_lt (2 ^ n) X hX0 hXN hpos
      have hj1' : ((j + 1 : ℕ) : ℝ) ≤ 2 ^ n := by exact_mod_cast hj1
      have hd : dist (gridPt c c' n (j + 1)) t < η := by
        rw [Real.dist_eq, hg, ht_eq]
        have e : c + (c' - c) * ((j + 1 : ℕ) : ℝ) / 2 ^ n - (c + (c' - c) * X / 2 ^ n) =
            (c' - c) * (1 - θ) / 2 ^ n := by
          rw [hθ]; push_cast; field_simp; ring
        rw [e, abs_of_nonneg (by have : 0 ≤ 1 - θ := by linarith
                                 positivity)]
        calc (c' - c) * (1 - θ) / 2 ^ n ≤ (c' - c) * 1 / 2 ^ n := by
              gcongr; linarith
          _ < η := by rw [mul_one]; exact hδ
      have := hηF (hmemg (j + 1) hj1') hd
      rw [dist_eq_norm] at this
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ0]
      exact mul_le_mul_of_nonneg_left this.le hθ0
  have hA' : ‖(1 - θ) • (F (gridPt c c' n j) - F t)‖ ≤ (1 - θ) * (ε / 2) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    exact mul_le_mul_of_nonneg_left hA (by linarith)
  rw [dist_eq_norm, hpa]
  have e2 : (1 - θ) • F (gridPt c c' n j) + θ • F (gridPt c c' n (j + 1)) - F t =
      (1 - θ) • (F (gridPt c c' n j) - F t) + θ • (F (gridPt c c' n (j + 1)) - F t) := by
    simp only [smul_sub]
    have : F t = (1 - θ) • F t + θ • F t := by rw [← add_smul]; simp
    conv_lhs => rw [this]
    abel
  rw [e2]
  calc _ ≤ ‖(1 - θ) • (F (gridPt c c' n j) - F t)‖ + ‖θ • (F (gridPt c c' n (j + 1)) - F t)‖ := norm_add_le _ _
    _ ≤ (1 - θ) * (ε / 2) + θ * (ε / 2) := add_le_add hA' hB
    _ = ε / 2 := by ring
    _ < ε := half_lt_self hε

end HRS.MC.Sec7.S7PIDK

end
