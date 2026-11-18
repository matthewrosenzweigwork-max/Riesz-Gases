import HRS.MS.SA16ZT4

/-!
# S.A.16 (SA16Z) T5: the truncated principal value converges to `∂_i (g ⋆ f)`

`sa16z_pv_tendsto`: for `f ∈ C_c^∞`, `0 ≤ s < d`:
`∫_{|z|>ε} K_i(z) f(x - z) dz → ∂_i (g ⋆ f)(x)` as `ε → 0+` (`K_i = ∂_i g`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution RealInnerProductSpace

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section T5
variable {d : ℕ} {s : ℝ}

theorem sa16z_R3_tendsto (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {F : Euc d → ℝ} (hF : IsCcInfty F)
    (i : Fin d) :
    Tendsto (fun ε : ℝ => ∫ z, fderiv ℝ F z (sa16z_e i) * (rieszKernel d s z * sa16z_chi d ε z))
      (𝓝[>] 0) (𝓝 (∫ z, fderiv ℝ F z (sa16z_e i) * rieszKernel d s z)) := by
  have hgm : Measurable (rieszKernel d s) := HRS.S16Frac.s16frac_g_meas d s
  have hdF := sa16s_cc_fderiv hF (sa16z_e i)
  have hint : Integrable (fun z => rieszKernel d s z * fderiv ℝ F z (sa16z_e i)) :=
    sa16z_g_mul_int hs0 hsd hdF.1.continuous hdF.2
  refine tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure (Euc d)))
    (fun z => ‖rieszKernel d s z * fderiv ℝ F z (sa16z_e i)‖) ?_ ?_ hint.norm ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hdF.1.continuous.measurable.mul (hgm.mul (sa16z_chi_smooth ε).continuous.measurable)).aestronglyMeasurable
  · refine Eventually.of_forall fun ε => Eventually.of_forall fun z => ?_
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sa16z_chi_nonneg ε z)]
    calc |fderiv ℝ F z (sa16z_e i)| * (|rieszKernel d s z| * sa16z_chi d ε z)
        ≤ |fderiv ℝ F z (sa16z_e i)| * (|rieszKernel d s z| * 1) := by
          gcongr; exact sa16z_chi_le_one ε z
      _ = _ := by ring
  · filter_upwards [HRS.Commutator.Whole.ae_ne_zero_euc hd] with z hz
    have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, sa16z_chi d ε z = 1 := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ‖z‖ / 2 by
        have := norm_pos_iff.2 hz; linarith)] with ε hε
      have hlt : ε * ε < (‖z‖ / 2) * (‖z‖ / 2) := mul_self_lt_mul_self hε.1.le hε.2
      exact sa16z_chi_one hε.1 (by nlinarith [norm_nonneg z])
    refine (tendsto_const_nhds (x := fderiv ℝ F z (sa16z_e i) * rieszKernel d s z)).congr'
      (hev.mono fun ε h => ?_)
    simp [h]

end T5

end HRS.Whole.AppendixA.Phase2SA16R
