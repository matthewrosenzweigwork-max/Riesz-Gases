import HRS.Main.A1014Aux3

/-!
# Packet A1014, part 6: arithmetic of the Wasserstein rate

* `a1014_inf_tail`: a bound `W ≤ ofReal (B + c₃ · tail)` with arbitrarily small `c₃ · tail` gives `W ≤ ofReal B`;
* `a1014_sqrt_rate`: `√(q(√𝔈 + N^{-1/d})) ≤ √q (𝔈^{1/4} + N^{-1/(2d)})`;
* `a1014_rate_final`: the sum of the three explicit terms is bounded by a constant times `masterRate`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Main.A1014

variable {d : ℕ}

theorem a1014_inf_tail {W : ℝ≥0∞} {B c3 : ℝ} (hB : 0 ≤ B)
    (h : ∀ ε' : ℝ, 0 < ε' → ∃ tl : ℝ, 0 ≤ tl ∧ c3 * tl ≤ ε' ∧
      W ≤ ENNReal.ofReal (B + c3 * tl)) : W ≤ ENNReal.ofReal B := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨tl, htl, hle, hW⟩ := h (ε : ℝ) (by exact_mod_cast hε)
  refine hW.trans ?_
  calc ENNReal.ofReal (B + c3 * tl) ≤ ENNReal.ofReal (B + (ε : ℝ)) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal B + ENNReal.ofReal (ε : ℝ) := ENNReal.ofReal_add hB (by positivity)
    _ = ENNReal.ofReal B + ε := by rw [ENNReal.ofReal_coe_nnreal]

theorem a1014_sqrt_rate (hd : 1 ≤ d) {q 𝔈 : ℝ} (hq : 0 ≤ q) (h𝔈 : 0 ≤ 𝔈) {N : ℕ} (hN : 1 ≤ N) :
    Real.sqrt (q * (Real.sqrt 𝔈 + (N : ℝ) ^ (-(1 : ℝ) / d))) ≤
      Real.sqrt q * (𝔈 ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / (2 * d))) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h4 : 0 ≤ 𝔈 ^ ((1 : ℝ) / 4) := Real.rpow_nonneg h𝔈 _
  have h4sq : (𝔈 ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt 𝔈 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h𝔈, Real.sqrt_eq_rpow]
    congr 1; norm_num
  have h2 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / (2 * d)) := Real.rpow_nonneg hNr.le _
  have h2sq : ((N : ℝ) ^ (-(1 : ℝ) / (2 * d))) ^ 2 = (N : ℝ) ^ (-(1 : ℝ) / d) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
    congr 1
    field_simp
    norm_num
  rw [Real.sqrt_mul hq]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  rw [← h4sq, ← h2sq]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  nlinarith [mul_nonneg h4 h2]

theorem a1014_rate_final {Ktr c1 c2 εf q σ 𝔈 E : ℝ} {N : ℕ} (hd : 1 ≤ d) (hN : 1 ≤ N)
    (hKtr : 0 ≤ Ktr) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hεf : 0 ≤ εf) (hq : 0 ≤ q) (hσ : 0 ≤ σ)
    (h𝔈 : 0 ≤ 𝔈) (hE : 0 ≤ E) :
    Ktr * εf + c1 * (σ * E) + Real.sqrt (c2 * (q * (Real.sqrt 𝔈 + (N : ℝ) ^ (-(1 : ℝ) / d)))) ≤
      (Ktr + c1 + Real.sqrt c2) * masterRate d εf q σ 𝔈 E N := by
  have hsr := a1014_sqrt_rate hd hq h𝔈 hN
  have h1 : Real.sqrt (c2 * (q * (Real.sqrt 𝔈 + (N : ℝ) ^ (-(1 : ℝ) / d)))) ≤
      Real.sqrt c2 * (Real.sqrt q * (𝔈 ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / (2 * d)))) := by
    rw [Real.sqrt_mul hc2]
    exact mul_le_mul_of_nonneg_left hsr (Real.sqrt_nonneg _)
  have hX : 0 ≤ Real.sqrt q * (𝔈 ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / (2 * d))) := by
    have : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / (2 * d)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    have : 0 ≤ 𝔈 ^ ((1 : ℝ) / 4) := Real.rpow_nonneg h𝔈 _
    positivity
  have hσE : 0 ≤ σ * E := mul_nonneg hσ hE
  unfold masterRate
  have hs2 := Real.sqrt_nonneg c2
  nlinarith [mul_nonneg hKtr hX, mul_nonneg hKtr hσE, mul_nonneg hc1 hX, mul_nonneg hc1 hεf,
    mul_nonneg hs2 hεf, mul_nonneg hs2 hσE]

end HRS.Main.A1014
