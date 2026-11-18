import HRS.Main.ThermLin2E1b
import HRS.Main.ThermLin2Ba6
import HRS.Main.ThermLin2Ly3
import HRS.Main.ThermLin2Mo4
import HRS.Main.ThermLin2Mo8

/-!
# THERMLIN2 E1c: `tl2_zero_start_comparison` (E1)

Route (`t25p_stage2` with the evolution `W` of `tl2_Wpkg_proof`, `X₀ = X₀' = 0`, `Mart = G`, `Cb = tl2CbDens`, `Z = Zw`
a measurable modification of the stochastic convolution of `G` against `W`, `Rr = Zs - Zw`, `Xp = Zs`):

* the pathwise bound of the remainder `Zs - Zw` is the PLAN STATEMENT `tl2_remainder_bound` (B5), **used as a black box**
  (it is being proved elsewhere; the orchestrator swaps it for its `_proof` version at integration);
* moments: `tl2_Zw_moment_proof`; noise cost: `tl2_noise_cost_proof`; `Cb`: `tl2_CbDens_det_proof`; the hypothesis `hid`:
  `tl2_zero_start_law_unique_proof` (`X₀' = 0` forces `ξ = 0` a.s.); decay constant of `Vev`: `tl2_Vev_decay_proof`.
* the constants `C, c` depend only on `(S, m, T, ρβ)`: `K = max K₀ Cw` is common to `V` (decay `K₀ e^{-c₀ t}`) and `W`
  (bound `Cw`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P

variable {d : ℕ}

/-- `(∫ B^p)^{1/p} ≤ x` for `p ∈ {1,2}` from the second moment bound. -/
lemma tl2E1_p_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {B : Ω → ℝ≥0∞}
    (hB : AEMeasurable B P) {x : ℝ≥0∞} (hsq : ∫⁻ ω, B ω ^ 2 ∂P ≤ x ^ 2) {p : ℝ} (hp : p = 1 ∨ p = 2) :
    (∫⁻ ω, B ω ^ p ∂P) ^ (1 / p) ≤ x := by
  have h2 : (∫⁻ ω, B ω ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤ x := by
    calc (∫⁻ ω, B ω ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤ (x ^ 2) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hsq (by norm_num)
      _ = x := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        simp
  rcases hp with rfl | rfl
  · simp only [ENNReal.rpow_one, div_one]
    exact (tl2E1_l1_le_l2 P hB).trans h2
  · simpa [ENNReal.rpow_two] using h2

/-- Square root of the noise cost. -/
lemma tl2E1_sqrt_le {X : ℝ≥0∞} {Cn cn a : ℝ} (hCn : 0 ≤ Cn) (hX : X ≤ ENNReal.ofReal (Cn * Real.exp (-cn * a))) :
    X ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt Cn * Real.exp (-(cn / 2) * a)) := by
  have hq : (Real.sqrt Cn * Real.exp (-(cn / 2) * a)) ^ 2 = Cn * Real.exp (-cn * a) := by
    rw [mul_pow, Real.sq_sqrt hCn, ← Real.exp_nat_mul]
    congr 2
    push_cast; ring
  calc X ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal (Cn * Real.exp (-cn * a))) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hX (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt Cn * Real.exp (-(cn / 2) * a)) := by
        rw [← hq, ENNReal.ofReal_pow (by positivity), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        simp

end HRS.ThermLin.Plan2
