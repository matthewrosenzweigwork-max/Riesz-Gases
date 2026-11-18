import HRS.MS.R26T8AP07s
import HRS.Equilibrium.Parametrix.PX3bAux
import HRS.Equilibrium.L49Aux2

/-!
# S8.2 local Newton layer, packet T8A.P14: principal relative Laplacian cancellation
`r26t8a_principal_newton_cancel`: for `0 < |z| < 1`, `-2 nu Delta_z midPair (rawNewton nu chi F) X z = midPair F X z`.
The Poisson equation for the Newton potential of the integrable, compactly supported source `chi * midPair F X`, which is `C^2` near `z != 0`,
is `HRS.Parx.newtonKernel_poisson`; here only the identification of the two Newton kernels and the cutoff bookkeeping are new.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_p14_kernel_eq (hd : 2 ≤ d) (nu : ℝ) (u : Euc d) :
    newtonKernel d nu u = HRS.Parx.newtonKernel d nu u := by
  have hball : HRS.sphereArea d = (d : ℝ) * (volume (Metric.ball (0 : Euc d) 1)).toReal := by
    rw [← HRS.L49.l49_ballConst_eq (by omega : 1 ≤ d)]
    rfl
  unfold newtonKernel HRS.Parx.newtonKernel
  by_cases h : d = 2
  · subst h
    have : HRS.sphereArea 2 = 2 * Real.pi := by
      unfold HRS.sphereArea
      norm_num [Real.Gamma_one]
    simp only [if_true, this]
    by_cases hn : nu = 0
    · simp [hn]
    · field_simp
  · simp only [h, if_false, hball]
    have hd2 : ((d : ℝ) - 2) ≠ 0 := by
      intro h0; apply h; exact_mod_cast (by linarith : (d : ℝ) = 2)
    by_cases hn : nu = 0
    · simp [hn]
    · have hv : (d : ℝ) * (volume (Metric.ball (0 : Euc d) 1)).toReal ≠ 0 := by
        exact mul_ne_zero (by exact_mod_cast (by omega : d ≠ 0)) (HRS.Parx.ballVol_pos (by omega)).ne'
      field_simp

theorem r26t8a_principal_newton_cancel (d : ℕ) (hd : 2 ≤ d) (nu : ℝ) (hnu : 0 < nu)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) (F : Euc d → Euc d → ℝ)
    (A M sigma : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A) (hsd : sigma < d)
    (hF : Conormal 4 0 M sigma A F) :
    ∀ X z, z ≠ 0 → ‖z‖ < 1 →
      -2 * nu * Laplacian.laplacian (fun w => midPair (rawNewton nu chi F) X w) z = midPair F X z := by
  intro X z hz hz1
  set H : Euc d → ℝ := fun w => chi w * midPair F X w with hH
  have hm : ContinuousOn (fun w => midPair F X w) {w : Euc d | w ≠ 0} :=
    (r26t8a_midPair_contDiffOn hF.1).continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun w hw => hw)
  have hmc : ContDiffOn ℝ 4 (fun w => midPair F X w) {w : Euc d | w ≠ 0} :=
    (r26t8a_midPair_contDiffOn hF.1).comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun w hw => hw)
  have hopen : IsOpen {w : Euc d | w ≠ 0} := isOpen_ne
  -- compact support
  have hHc : HasCompactSupport H := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) 2) (fun w hw => ?_)
    have : 2 < ‖w‖ := by simpa using hw
    simp [hH, hchi.2.2.2.2 w this.le]
  -- integrability
  have hHi : Integrable H := by
    obtain ⟨s, hs0, hsd', hFb⟩ := r26t8a_p07_midbound hd 4 0 M sigma hM hsd
    obtain ⟨c, hc0, hc⟩ := hFb A hA F hF X
    have hmaj : Integrable ((ball (0 : Euc d) 3).indicator (fun w : Euc d => c * ‖w‖ ^ (-s))) :=
      (integrable_indicator_iff measurableSet_ball).2 ((r26t8a_integrableOn_ball_rpow (by omega) hsd' 3).const_mul c)
    have hmeas : AEStronglyMeasurable H volume :=
      hchi.1.continuous.aestronglyMeasurable.mul (r26t8a_p07_ae_meas hm hd)
    refine Integrable.mono' hmaj hmeas ?_
    filter_upwards [r26t8a_ae_ne_zero hd] with w hw
    have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
    by_cases h2 : ‖w‖ < 2
    · have hb : w ∈ ball (0 : Euc d) 3 := by simp; linarith
      rw [Set.indicator_of_mem hb]
      have := hc w hwn h2.le
      rw [hH]; simp only [norm_mul, Real.norm_eq_abs]
      have hch : |chi w| ≤ 1 := by
        rw [abs_of_nonneg (hchi.2.2.1 w).1]; exact (hchi.2.2.1 w).2
      calc |chi w| * |midPair F X w| ≤ 1 * (c * ‖w‖ ^ (-s)) := mul_le_mul hch this (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    · simp [hH, hchi.2.2.2.2 w (not_lt.1 h2)]
      by_cases hb : w ∈ ball (0 : Euc d) 3
      · rw [Set.indicator_of_mem hb]; positivity
      · rw [Set.indicator_of_notMem hb]
  -- regularity at z
  have hchi2' : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) chi := contDiff_infty.1 hchi.1 2
  have hchi2 : ContDiff ℝ 2 chi := by exact_mod_cast hchi2'
  have hHz : ContDiffAt ℝ 2 H z := by
    have h1 : ContDiffAt ℝ 4 (fun w => midPair F X w) z := hmc.contDiffAt (hopen.mem_nhds hz)
    exact (hchi2.contDiffAt).mul (h1.of_le (by norm_num))
  have hP := HRS.Parx.newtonKernel_poisson hd hnu hHi hHc hHz
  have hloc : (fun w => midPair (rawNewton nu chi F) X w) =ᶠ[𝓝 z]
      fun z' => ∫ w, HRS.Parx.newtonKernel d nu (z' - w) * H w := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds (show ‖z‖ < 1 from hz1)] with y hy
    have hy1 : ‖y‖ ≤ 1 := le_of_lt hy
    rw [r26t8a_p07_raw_mid_int, hchi.2.2.2.1 y hy1, one_mul]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [hH, r26t8a_p14_kernel_eq hd, mul_assoc]
  rw [(InnerProductSpace.laplacian_congr_nhds hloc).eq_of_nhds]
  have : -2 * nu = -(2 * nu) := by ring
  rw [this, hP]
  simp [hH, hchi.2.2.2.1 z hz1.le]

end HRS.MS.R26T8A
