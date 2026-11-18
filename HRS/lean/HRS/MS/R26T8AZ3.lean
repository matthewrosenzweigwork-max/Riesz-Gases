import HRS.MS.R26T8AZ3a

/-!
# S8.2 T8A Z3: derivative of the Newton convolution of a bounded source with an integrable gradient singularity
`r26t8a_Z3_conv_hasFDeriv`: `G` supported in `|w| ≤ 2`, `C^1` off `0`, `|G| ≤ c0`, `‖DG(w)‖ ≤ c1 |w|^{-s1}` (`0 < s1 < d`).  Then for `z ≠ 0`
`HasFDerivAt (z' ↦ ∫ K(z'-v) G(v) dv) (∫ K(z-v) • DG(v) dv) z`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_Z3_swap {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] (K : Euc d → ℝ) (φ : Euc d → E')
    (x : Euc d) : ∫ t, K t • φ (x - t) = ∫ v, K (x - v) • φ v := by
  have := integral_sub_left_eq_self (μ := (volume : Measure (Euc d))) (fun v => K (x - v) • φ v) x
  simpa [sub_sub_cancel] using this

theorem r26t8a_Z3_vol_tail (hd : 2 ≤ d) :
    Tendsto (fun N : ℕ => (2 : ℝ) ^ N * (volume (ball (0 : Euc d) (3 * (1 / 2 : ℝ) ^ N))).toReal) atTop (𝓝 0) := by
  haveI := r26t8a_nontrivial hd
  set V1 : ℝ := (volume (ball (0 : Euc d) 1)).toReal with hV1
  have hq : (1 / 2 : ℝ) ^ d * 2 = (1 / 2) ^ (d - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    simp [pow_succ]
  have heq : ∀ N : ℕ, (2 : ℝ) ^ N * (volume (ball (0 : Euc d) (3 * (1 / 2 : ℝ) ^ N))).toReal =
      3 ^ d * V1 * ((1 / 2 : ℝ) ^ (d - 1)) ^ N := by
    intro N
    rw [Measure.addHaar_ball volume (0 : Euc d) (by positivity), finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), mul_pow, ← pow_mul, mul_comm N d, pow_mul, ← hq,
      mul_pow]
    ring
  simp only [heq]
  have h1 : Tendsto (fun N : ℕ => ((1 / 2 : ℝ) ^ (d - 1)) ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (pow_lt_one₀ (by norm_num) (by norm_num) (by omega))
  simpa using h1.const_mul (3 ^ d * V1)

end HRS.MS.R26T8A
