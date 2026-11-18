import HRS.MS.R26T8AZ0
import HRS.MS.R26T8AP07i
import HRS.MS.R26T8AP01a

/-!
# S8.2 T8A Z2: differentiating the Newton convolution of a bounded source that is `C^1` off the origin
`r26t8a_Z2_conv_hasFDeriv`: `G` bounded, `C^1` off `0`, supported in `|w| ≤ 2`, `‖DG(w)‖ ≤ c1 |w|^{-s1}` with `0 < s1 < d`.
Then `z' ↦ ∫ K(z'-v) G(v) dv` is differentiable at every `z ≠ 0` with derivative `∫ K(z-v) • DG(v) dv` (no boundary term at the singular point).
Proof: `G_N = (1 - chi(2^N .)) G` is `C^1` with compact support, so Mathlib's convolution derivative applies; `G_N → G` and the derivatives
converge uniformly near `z` (the difference is supported in `|v| ≤ 3 (1/2)^N`, where `K(z'-v)` is bounded).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_Z2_GN_contDiff {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {G : Euc d → ℝ}
    (hG1 : ContDiffOn ℝ 1 G {0}ᶜ) (hGc : ∀ w, 2 < ‖w‖ → G w = 0) (N : ℕ) :
    ContDiff ℝ 1 (fun w => (1 - chi ((2 : ℝ) ^ N • w)) * G w) ∧
      HasCompactSupport (fun w => (1 - chi ((2 : ℝ) ^ N • w)) * G w) := by
  have hχ : ContDiff ℝ 1 (fun w : Euc d => chi ((2 : ℝ) ^ N • w)) :=
    (hchi.1.of_le (by exact_mod_cast le_top)).comp (contDiff_const_smul _)
  refine ⟨?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = 0
    · subst hx
      have hev : (fun w : Euc d => (1 - chi ((2 : ℝ) ^ N • w)) * G w) =ᶠ[𝓝 0] fun _ => 0 := by
        have hball : ball (0 : Euc d) ((1 / 2 : ℝ) ^ N) ∈ 𝓝 (0 : Euc d) := ball_mem_nhds _ (by positivity)
        filter_upwards [hball] with w hw
        rw [mem_ball_zero_iff] at hw
        have h1 : ‖((2 : ℝ) ^ N) • w‖ ≤ 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
          have : (2 : ℝ) ^ N * (1 / 2) ^ N = 1 := by rw [← mul_pow]; norm_num
          nlinarith [norm_nonneg w, pow_pos (by norm_num : (0 : ℝ) < 2) N]
        rw [hchi.2.2.2.1 _ h1]; simp
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · exact (contDiffAt_const.sub hχ.contDiffAt).mul (hG1.contDiffAt (isOpen_compl_singleton.mem_nhds hx))
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) 2) fun w hw => ?_
    have : 2 < ‖w‖ := by simpa [mem_closedBall_zero_iff] using hw
    simp [hGc w this]

end HRS.MS.R26T8A
