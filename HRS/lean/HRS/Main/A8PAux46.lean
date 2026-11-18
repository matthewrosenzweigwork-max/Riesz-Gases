import HRS.Main.A8PAux45

/-!
# Packet A8P, part 46: the master rate tends to zero
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

theorem a8p_q_E_le (S : MainData d) {B : ℝ} (hB : ∀ N, S.invβ N ≤ B) {N : ℕ} (hN : 1 ≤ N) {E : ℝ}
    (hE : 0 ≤ E) : S.qN N * E ≤ Real.sqrt B * (S.sigma N * E) := by
  obtain ⟨hq0, hq1⟩ := a8p_q_bounds S hN
  have hσ := a8p_sigma_nonneg S N
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hinv := S.hinvβ N
  set x : ℝ := S.sigma N * S.invβ N / N with hx
  have hx0 : 0 ≤ x := by positivity
  have hxq : S.qN N * E = x * (S.sigma N * E) := by
    rw [a8p_q_eq, hx]; ring
  have hx2 : x ^ 2 ≤ B := by
    have : x ^ 2 = S.qN N * (S.invβ N / N) := by
      rw [hx, a8p_q_eq]; ring
    rw [this]
    have h1 : S.invβ N / N ≤ B := by
      refine (div_le_self hinv hNr).trans (hB N)
    calc S.qN N * (S.invβ N / N) ≤ 1 * (S.invβ N / N) :=
          mul_le_mul_of_nonneg_right hq1 (by positivity)
      _ ≤ B := by linarith
  have hxB : x ≤ Real.sqrt B := Real.le_sqrt_of_sq_le hx2
  rw [hxq]
  exact mul_le_mul_of_nonneg_right hxB (by positivity)

theorem a8p_rate_tendsto (S : MainData d) (hd : 1 ≤ d) (ε 𝔈 : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) (hσE : Tendsto (fun N => S.sigma N * 𝔈 N) atTop (𝓝 0))
    (h𝔈 : ∀ N, 1 ≤ N → 0 ≤ 𝔈 N) :
    Tendsto (fun N => masterRate d (ε N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := S.invβ_bdd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  -- the term `√q 𝔈^{1/4}`
  have hy : Tendsto (fun N : ℕ => Real.sqrt (S.qN N) * (𝔈 N) ^ ((1 : ℝ) / 4)) atTop (𝓝 0) := by
    set y : ℕ → ℝ := fun N => Real.sqrt (S.qN N) * (𝔈 N) ^ ((1 : ℝ) / 4) with hydef
    have hz : Tendsto (fun N : ℕ => y N ^ 4) atTop (𝓝 0) := by
      have hup : Tendsto (fun N : ℕ => Real.sqrt B * (S.sigma N * 𝔈 N)) atTop (𝓝 0) := by
        simpa using hσE.const_mul (Real.sqrt B)
      refine squeeze_zero' ?_ ?_ hup
      · exact Filter.Eventually.of_forall fun N => by positivity
      · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
        have hq := a8p_q_bounds S hN
        have h4 : y N ^ 4 = S.qN N ^ 2 * 𝔈 N := by
          simp only [hydef]
          rw [mul_pow]
          congr 1
          · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hq.1]
          · rw [← Real.rpow_natCast, ← Real.rpow_mul (h𝔈 N hN)]
            norm_num
        rw [h4]
        refine le_trans ?_ (a8p_q_E_le S hB hN (h𝔈 N hN))
        have := h𝔈 N hN
        nlinarith [mul_nonneg hq.1 this, mul_le_mul_of_nonneg_right hq.2 (mul_nonneg hq.1 this)]
    have hy0 : ∀ N, 1 ≤ N → 0 ≤ y N := fun N hN =>
      mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (h𝔈 N hN) _)
    have hroot : Tendsto (fun N : ℕ => (y N ^ 4) ^ ((4 : ℕ)⁻¹ : ℝ)) atTop (𝓝 0) := by
      have := hz.rpow_const (p := ((4 : ℕ)⁻¹ : ℝ)) (Or.inr (by positivity))
      simpa using this
    refine hroot.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact Real.pow_rpow_inv_natCast (hy0 N hN) (by norm_num)
  -- the term `√q N^{-1/(2d)}`
  have hu : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 : ℝ) / (2 * d))) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (y := 1 / (2 * (d : ℝ))) (by positivity)).comp
      tendsto_natCast_atTop_atTop
    refine this.congr fun N => ?_
    simp only [Function.comp]
    congr 1
    ring
  have hb : Tendsto (fun N : ℕ => Real.sqrt (S.qN N) * (N : ℝ) ^ (-(1 : ℝ) / (2 * d))) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hu
    · exact Filter.Eventually.of_forall fun N => mul_nonneg (Real.sqrt_nonneg _)
        (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      have hq := a8p_q_bounds S hN
      have : Real.sqrt (S.qN N) ≤ 1 := Real.sqrt_le_one.2 hq.2 |> fun h => by simpa using h
      exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg N) _) this
  have hsum := (hε.add (hy.add hb)).add hσE
  simp only [add_zero] at hsum
  refine hsum.congr fun N => ?_
  unfold masterRate
  ring

end HRS.Main.A8P
