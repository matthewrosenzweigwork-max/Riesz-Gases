import HRS.MS.WadAux32

/-!
# S8.3, packet D7b (Route A): linearity of the first-order remainder `𝓑` on `C²_b`

For `h` of class `C²` with bounded `Dh, D²h` the cancellation integrals in `s84_Bop` are absolutely
convergent (`s84_conv_integrable`), hence `s84_Bop ρ (h₁ - h₂) = s84_Bop ρ h₁ - s84_Bop ρ h₂`
(`s84_Bop_sub`).  This is what lets the a priori estimate be applied to differences of classical solutions.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.MS.Wad

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

/-- Absolute convergence of the cancellation convolution. -/
theorem s84_conv_integrable (hd : 2 ≤ d) {s A H : ℝ} (hs0 : 0 < s) (hs : s + 1 / 2 < (d : ℝ))
    (hA0 : 0 ≤ A) (hH0 : 0 ≤ H) {u : Euc d → ℝ} (hum : Measurable u)
    (hA : ∀ y, |u y| ≤ A * (1 + ‖y‖) ^ (-((d : ℝ) + 1)))
    (hH : ∀ z : Euc d, ‖z‖ ≤ 1 / 4 → ∀ x, |u (x - z) - u x| ≤ H * ‖z‖ ^ (1 / 2 : ℝ)) (x : Euc d) :
    Integrable (fun y : Euc d => (if ‖x - y‖ ≤ 1 / 4 then (u y - u x) • rieszKernelGrad d s (x - y)
      else u y • rieszKernelGrad d s (x - y))) volume := by
  have hd1 : 1 ≤ d := by omega
  have hint1 : IntegrableOn (fun z : Euc d => ‖z‖ ^ (-(s + 1 / 2))) (ball (0 : Euc d) 1) volume :=
    ult_ball_int hd1 (by linarith) hs
  set g1 : Euc d → ℝ := (ball (0 : Euc d) 1).indicator (fun z => s * H * ‖z‖ ^ (-(s + 1 / 2))) with hg1
  set g2 : Euc d → ℝ := fun z => s * 4 ^ (s + 1) * A * (1 + ‖x - z‖) ^ (-((d : ℝ) + 1)) with hg2
  have hg1i : Integrable g1 volume :=
    (integrable_indicator_iff measurableSet_ball).2 (hint1.const_mul (s * H))
  have hg2i : Integrable g2 volume := ((s84_int_far d).comp_sub_left x).const_mul _
  have hg10 : ∀ z, 0 ≤ g1 z := fun z => by
    rw [hg1]
    refine Set.indicator_nonneg (fun z _ => ?_) z
    exact mul_nonneg (mul_nonneg hs0.le hH0) (Real.rpow_nonneg (norm_nonneg _) _)
  have hGm : Measurable (rieszKernelGrad d s) := movtr_rieszKernelGrad_measurable s
  set F : Euc d → Euc d := fun z => if ‖z‖ ≤ 1 / 4 then (u (x - z) - u x) • rieszKernelGrad d s z
    else u (x - z) • rieszKernelGrad d s z with hF
  have hFm : Measurable F := by
    refine Measurable.ite (measurableSet_le measurable_norm measurable_const) ?_ ?_
    · exact (((hum.comp (measurable_const.sub measurable_id)).sub measurable_const)).smul hGm
    · exact (hum.comp (measurable_const.sub measurable_id)).smul hGm
  have hFi : Integrable F volume := by
    refine (hg1i.add hg2i).mono' hFm.aestronglyMeasurable ?_
    filter_upwards [u2_ae_ne_zero hd1] with z hz
    have hzp : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hGn : ‖rieszKernelGrad d s z‖ = s * ‖z‖ ^ (-s - 1) := by
      rw [movtr_rieszKernelGrad_norm s hs0.le hz]
      unfold movtr_sigma
      simp [hs0.ne']
    by_cases hzn : ‖z‖ ≤ 1 / 4
    · rw [hF]; simp only [if_pos hzn]
      rw [norm_smul, hGn, Real.norm_eq_abs]
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
      simp only [Pi.add_apply]
      linarith
    · push Not at hzn
      rw [hF]; simp only [if_neg (not_le.2 hzn)]
      rw [norm_smul, hGn, Real.norm_eq_abs]
      have hg1n := hg10 z
      have h2 : ‖z‖ ^ (-s - 1) ≤ 4 ^ (s + 1) := by
        have : ‖z‖ ^ (-s - 1) ≤ (1 / 4 : ℝ) ^ (-s - 1) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hzn.le (by linarith)
        refine this.trans (le_of_eq ?_)
        rw [show (-s - 1) = -(s + 1) by ring, Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num),
          inv_inv]
      simp only [Pi.add_apply]
      calc |u (x - z)| * (s * ‖z‖ ^ (-s - 1)) ≤ (A * (1 + ‖x - z‖) ^ (-((d : ℝ) + 1))) * (s * 4 ^ (s + 1)) :=
            mul_le_mul (hA (x - z)) (mul_le_mul_of_nonneg_left h2 hs0.le) (by positivity) (by positivity)
        _ = g2 z := by rw [hg2]; ring
        _ ≤ g1 z + g2 z := by linarith
  have := hFi.comp_sub_left x
  refine this.congr (Eventually.of_forall fun y => ?_)
  simp only [hF, sub_sub_cancel]

/-- Linearity of the cancellation convolution on absolutely convergent inputs. -/
theorem s84_conv_sub {s : ℝ} {u₁ u₂ : Euc d → ℝ} (x : Euc d)
    (h₁ : Integrable (fun y : Euc d => (if ‖x - y‖ ≤ 1 / 4 then (u₁ y - u₁ x) • rieszKernelGrad d s (x - y)
      else u₁ y • rieszKernelGrad d s (x - y))) volume)
    (h₂ : Integrable (fun y : Euc d => (if ‖x - y‖ ≤ 1 / 4 then (u₂ y - u₂ x) • rieszKernelGrad d s (x - y)
      else u₂ y • rieszKernelGrad d s (x - y))) volume) :
    convGradConvW (rieszKernelGrad d s) (fun y => u₁ y - u₂ y) x =
      convGradConvW (rieszKernelGrad d s) u₁ x - convGradConvW (rieszKernelGrad d s) u₂ x := by
  unfold convGradConvW
  rw [← integral_sub h₁ h₂]
  congr 1
  funext y
  by_cases hy : ‖x - y‖ ≤ 1 / 4
  · simp only [if_pos hy]
    rw [← sub_smul]; congr 1; ring
  · simp only [if_neg hy]
    rw [← sub_smul]

end HRS.MS.Wad
