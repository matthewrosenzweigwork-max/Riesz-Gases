import HRS.MS.WadAux19
import HRS.MS.UlTailAux1
import HRS.Whole.MovtrAux2
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# S8.3, packet D4 (part 1): the Hölder-1/2 bound of the cancellation convolution

`s84_conv_bound`: for `0 < s`, `s + 1/2 < d`, a scalar `u` with `|u(y)| ≤ A (1+‖y‖)^{-(d+1)}` and the
local Hölder bound `|u(x-z) - u(x)| ≤ H ‖z‖^{1/2}` (`‖z‖ ≤ 1/4`), the cancellation convolution
`convGradConvW (∇g_s) u` is bounded by `C(A+H)` with `C = C(d,s)`.  This is the estimate behind
`‖𝓑 f‖ ≲ ‖f‖_{C^{1,α}}` of the TeX (`S:Q:eq:B-regularity`, `S:Q:eq:CZ-subtract`), valid for all `d ≥ 2`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.MS.Wad

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

/-- The constant of `s84_conv_bound`. -/
def s84_Cconv (d : ℕ) (s : ℝ) : ℝ :=
  s * (∫ z in ball (0 : Euc d) 1, ‖z‖ ^ (-(s + 1 / 2))) +
    s * 4 ^ (s + 1) * ∫ y : Euc d, (1 + ‖y‖) ^ (-((d : ℝ) + 1))

theorem s84_int_far (d : ℕ) : Integrable (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) volume := by
  refine integrable_one_add_norm (E := Euc d) (μ := volume) (r := (d : ℝ) + 1) ?_
  simp

theorem s84_Cconv_nonneg (d : ℕ) {s : ℝ} (hs0 : 0 ≤ s) : 0 ≤ s84_Cconv d s := by
  unfold s84_Cconv
  refine add_nonneg (mul_nonneg hs0 (setIntegral_nonneg measurableSet_ball fun z _ =>
    Real.rpow_nonneg (norm_nonneg _) _)) (mul_nonneg (mul_nonneg hs0 (by positivity))
    (integral_nonneg fun y => Real.rpow_nonneg (by positivity) _))

theorem s84_conv_bound (hd : 2 ≤ d) {s A H : ℝ} (hs0 : 0 < s) (hs : s + 1 / 2 < (d : ℝ))
    (hA0 : 0 ≤ A) (hH0 : 0 ≤ H) {u : Euc d → ℝ}
    (hA : ∀ y, |u y| ≤ A * (1 + ‖y‖) ^ (-((d : ℝ) + 1)))
    (hH : ∀ z : Euc d, ‖z‖ ≤ 1 / 4 → ∀ x, |u (x - z) - u x| ≤ H * ‖z‖ ^ (1 / 2 : ℝ)) (x : Euc d) :
    ‖convGradConvW (rieszKernelGrad d s) u x‖ ≤ s84_Cconv d s * (A + H) := by
  have hd1 : 1 ≤ d := by omega
  set I₁ : ℝ := ∫ z in ball (0 : Euc d) 1, ‖z‖ ^ (-(s + 1 / 2)) with hI₁
  set I₂ : ℝ := ∫ y : Euc d, (1 + ‖y‖) ^ (-((d : ℝ) + 1)) with hI₂
  have hI₁0 : 0 ≤ I₁ := setIntegral_nonneg measurableSet_ball fun z _ => Real.rpow_nonneg (norm_nonneg _) _
  have hI₂0 : 0 ≤ I₂ := integral_nonneg fun y => Real.rpow_nonneg (by positivity) _
  have hint1 : IntegrableOn (fun z : Euc d => ‖z‖ ^ (-(s + 1 / 2))) (ball (0 : Euc d) 1) volume :=
    ult_ball_int hd1 (by linarith) hs
  set g1 : Euc d → ℝ := (ball (0 : Euc d) 1).indicator (fun z => s * H * ‖z‖ ^ (-(s + 1 / 2))) with hg1
  set g2 : Euc d → ℝ := fun z => s * 4 ^ (s + 1) * A * (1 + ‖x - z‖) ^ (-((d : ℝ) + 1)) with hg2
  have hg1i : Integrable g1 volume :=
    (integrable_indicator_iff measurableSet_ball).2 (hint1.const_mul (s * H))
  have hg2i : Integrable g2 volume := by
    have := (s84_int_far d).comp_sub_left x
    exact this.const_mul _
  have hg10 : ∀ z, 0 ≤ g1 z := fun z => by
    rw [hg1]
    refine Set.indicator_nonneg (fun z _ => ?_) z
    exact mul_nonneg (mul_nonneg hs0.le hH0) (Real.rpow_nonneg (norm_nonneg _) _)
  have hnorm : ‖convGradConvW (rieszKernelGrad d s) u x‖ ≤ ∫ z, (g1 z + g2 z) := by
    unfold convGradConvW
    rw [← integral_sub_left_eq_self _ volume x]
    refine norm_integral_le_of_norm_le (hg1i.add hg2i) ?_
    filter_upwards [u2_ae_ne_zero hd1] with z hz
    have hzp : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hGn : ‖rieszKernelGrad d s z‖ = s * ‖z‖ ^ (-s - 1) := by
      rw [movtr_rieszKernelGrad_norm s hs0.le hz]
      unfold movtr_sigma
      simp [hs0.ne']
    simp only [sub_sub_cancel]
    by_cases hzn : ‖z‖ ≤ 1 / 4
    · rw [if_pos hzn, norm_smul, hGn, Real.norm_eq_abs]
      have hn : g1 z = s * H * ‖z‖ ^ (-(s + 1 / 2)) := by
        rw [hg1, Set.indicator_of_mem]
        rw [mem_ball_zero_iff]; linarith
      have h1 : |u (x - z) - u x| * (s * ‖z‖ ^ (-s - 1)) ≤ s * H * ‖z‖ ^ (-(s + 1 / 2)) := by
        calc |u (x - z) - u x| * (s * ‖z‖ ^ (-s - 1)) ≤ (H * ‖z‖ ^ (1 / 2 : ℝ)) * (s * ‖z‖ ^ (-s - 1)) :=
              mul_le_mul_of_nonneg_right (hH z hzn x) (by positivity)
          _ = s * H * (‖z‖ ^ (1 / 2 : ℝ) * ‖z‖ ^ (-s - 1)) := by ring
          _ = s * H * ‖z‖ ^ (-(s + 1 / 2)) := by
              rw [← Real.rpow_add hzp]; congr 2; ring
      have hg2n : 0 ≤ g2 z := by
        rw [hg2]; exact mul_nonneg (mul_nonneg (mul_nonneg hs0.le (by positivity)) hA0)
          (Real.rpow_nonneg (by positivity) _)
      linarith
    · push Not at hzn
      rw [if_neg (not_le.2 hzn), norm_smul, hGn, Real.norm_eq_abs]
      have hg1n := hg10 z
      have h2 : ‖z‖ ^ (-s - 1) ≤ 4 ^ (s + 1) := by
        have : ‖z‖ ^ (-s - 1) ≤ (1 / 4 : ℝ) ^ (-s - 1) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hzn.le (by linarith)
        refine this.trans (le_of_eq ?_)
        rw [show (-s - 1) = -(s + 1) by ring, Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num),
          inv_inv]
      calc |u (x - z)| * (s * ‖z‖ ^ (-s - 1)) ≤ (A * (1 + ‖x - z‖) ^ (-((d : ℝ) + 1))) * (s * 4 ^ (s + 1)) :=
            mul_le_mul (hA (x - z)) (mul_le_mul_of_nonneg_left h2 hs0.le) (by positivity) (by positivity)
        _ = g2 z := by rw [hg2]; ring
        _ ≤ g1 z + g2 z := by linarith
  refine hnorm.trans ?_
  rw [integral_add hg1i hg2i]
  have e1 : ∫ z, g1 z = s * H * I₁ := by
    rw [hg1, integral_indicator measurableSet_ball, integral_const_mul]
  have e2 : ∫ z, g2 z = s * 4 ^ (s + 1) * A * I₂ := by
    rw [hg2, integral_const_mul, integral_sub_left_eq_self (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) volume x]
  rw [e1, e2]
  unfold s84_Cconv
  have h4 : 0 ≤ s * 4 ^ (s + 1) := by positivity
  nlinarith [mul_nonneg hA0 (mul_nonneg h4 hI₂0), mul_nonneg hH0 (mul_nonneg hs0.le hI₁0),
    mul_nonneg hA0 (mul_nonneg hs0.le hI₁0), mul_nonneg hH0 (mul_nonneg h4 hI₂0)]

end HRS.MS.Wad
