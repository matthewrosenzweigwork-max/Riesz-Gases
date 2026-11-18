import HRS.MS.ShiftFldAux6

/-!
# S79: `critical_path_limit` from S2.1(i) (`whole_space_stationary`)

`critical_path_limit_of_S21 : type_of% @whole_space_stationary → type_of% @critical_path_limit`.

At `s = 2d/3` one has `p = 3/2`, so the shift `N^{3/2-p} b` is the fixed bias `b`, `θ_{d,s} > 0` (`s78_biasTheta_pos`), `δ_N = N^{-1/2}`,
`w_N → 0`; S2.1(i) with the fixed constants `C₀, C` (chosen before `N`) and `s79_core` (window `a₀ = 0`) give
`W_1(Law(√N(μ_N^· - μ)), Law(Z + b)) ≤ C(δ_N^{3/20} + √w_N) + K N^{-θ} → 0`, and `W_1 → 0` implies convergence of
`∫ F dLaw` for bounded continuous `F` (`HRS.Main.therm_convergesInLaw_of_W1`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole.S79

open HRS (Euc)

variable {d : ℕ} {s : ℝ}

theorem s79_biasP_critical (hd : 2 ≤ d) (hs : s = 2 * (d : ℝ) / 3) : biasP d s = 3 / 2 := by
  have : (0 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  unfold biasP
  rw [hs]
  field_simp

theorem s79_tendsto_sqrt_zero {f : ℕ → ℝ} (h : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun N => Real.sqrt (f N)) atTop (𝓝 0) := by
  have := (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at this
  exact this

/-- The right-hand side of the `W_1` bound tends to `0` at `s = 2d/3`. -/
theorem s79_rates_tendsto (hd : 2 ≤ d) (hs : s = 2 * (d : ℝ) / 3) (C₀ C K : ℝ) :
    Tendsto (fun N : ℕ => C * (deltaN d s N ^ ((3 : ℝ) / 20) +
        Real.sqrt (localizationRate d s C₀ N))) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => K * (N : ℝ) ^ (-biasTheta d s)) atTop (𝓝 0) := by
  have hd0 : (0 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hs2 : (d : ℝ) / 2 < s := by rw [hs]; linarith
  have hsd : s < d := by rw [hs]; linarith
  have hθ := HRS.Whole.S78.s78_biasTheta_pos hd hs2 hsd
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hnegpow : ∀ y : ℝ, 0 < y → Tendsto (fun N : ℕ => (N : ℝ) ^ (-y)) atTop (𝓝 0) :=
    fun y hy => (tendsto_rpow_neg_atTop hy).comp hcast
  -- δ_N^{3/20}
  have h1 : Tendsto (fun N : ℕ => deltaN d s N ^ ((3 : ℝ) / 20)) atTop (𝓝 0) := by
    have hp := s79_biasP_critical hd hs
    have e : ∀ N : ℕ, deltaN d s N ^ ((3 : ℝ) / 20) = (N : ℝ) ^ (-(3 / 40 : ℝ)) := by
      intro N
      rw [HRS.Whole.S78.s78_deltaN_eq hs2, hp, ← Real.rpow_mul (Nat.cast_nonneg N)]
      congr 1; norm_num
    simp_rw [e]
    exact hnegpow _ (by norm_num)
  -- w_N → 0
  have h2 : Tendsto (fun N : ℕ => localizationRate d s C₀ N) atTop (𝓝 0) := by
    have hs0 : s ≠ 0 := by rw [hs]; positivity
    have ho : Tendsto (fun N : ℕ => oN d s C₀ N) atTop (𝓝 0) := by
      have e : ∀ N : ℕ, oN d s C₀ N = C₀ * (N : ℝ) ^ (-(1 / 3 : ℝ)) := by
        intro N
        rw [oN_eq, if_neg hs0, add_zero]
        congr 2
        rw [hs]; field_simp; ring
      simp_rw [e]
      simpa using (hnegpow (1 / 3) (by norm_num)).const_mul C₀
    have hsq : Tendsto (fun N : ℕ => Real.sqrt (oN d s C₀ N)) atTop (𝓝 0) := by
      exact s79_tendsto_sqrt_zero ho
    have hn : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / (d : ℝ)))) atTop (𝓝 0) :=
      hnegpow _ (by positivity)
    have hsum := hn.add hsq
    rw [add_zero] at hsum
    unfold localizationRate
    have hq : (0 : ℝ) ≤ 4 / ((d : ℝ) + 4) := by positivity
    have := ((Real.continuous_rpow_const hq).tendsto 0).comp hsum
    rwa [Real.zero_rpow (by positivity)] at this
  have h3 : Tendsto (fun N : ℕ => Real.sqrt (localizationRate d s C₀ N)) atTop (𝓝 0) := by
    exact s79_tendsto_sqrt_zero h2
  have h4 := hnegpow (biasTheta d s) hθ
  exact ⟨by simpa using ((h1.add h3).const_mul C), by simpa using (h4.const_mul K)⟩

end HRS.Whole.S79
