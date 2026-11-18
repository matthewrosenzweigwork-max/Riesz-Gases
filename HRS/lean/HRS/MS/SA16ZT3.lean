import HRS.MS.SA16ZT2

/-!
# S.A.16 (SA16Z) T3: integration by parts against the cutoff kernel `g χ_ε`

`sa16z_ibp_chi`: `∫ F (K χ_ε + g ∂_iχ_ε) = -∫ ∂_iF (g χ_ε)` for `F ∈ C_c^∞`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution RealInnerProductSpace

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section T3
variable {d : ℕ} {s : ℝ}

lemma sa16z_H_smooth {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (fun z : Euc d => rieszKernel d s z * sa16z_chi d ε z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    have hev : (fun z : Euc d => rieszKernel d s z * sa16z_chi d ε z) =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : Euc d) hε] with y hy
      have : ‖y‖ ≤ ε := by have := mem_ball_zero_iff.1 hy; exact this.le
      simp [sa16z_chi_zero hε this]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · exact ((rieszKernel_contDiffOn (d := d) (s := s)).contDiffAt (isOpen_ne.mem_nhds hz)).mul
      (sa16z_chi_smooth ε).contDiffAt

lemma sa16z_H_fderiv {ε : ℝ} (hε : 0 < ε) (i : Fin d) {z : Euc d} (hz : z ≠ 0) :
    fderiv ℝ (fun z : Euc d => rieszKernel d s z * sa16z_chi d ε z) z (sa16z_e i) =
      sa16z_Kx s i z * sa16z_chi d ε z + rieszKernel d s z * sa16z_dchi d ε i z := by
  have hg : DifferentiableAt ℝ (rieszKernel d s) z :=
    ((rieszKernel_contDiffOn (d := d) (s := s)).contDiffAt (isOpen_ne.mem_nhds hz)).differentiableAt (by simp)
  have hc : DifferentiableAt ℝ (sa16z_chi d ε) z := ((sa16z_chi_smooth ε).differentiable (by simp)) z
  rw [fderiv_fun_mul hg hc]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [sa16z_dchi_eq]
  have := sa16z_Kx_eq s i hz
  rw [sa16z_e] at this
  rw [this]
  ring

lemma sa16z_Kx_chi_bdd (hs0 : 0 ≤ s) (i : Fin d) {ε : ℝ} (hε : 0 < ε) (z : Euc d) :
    ‖sa16z_Kx s i z * sa16z_chi d ε z‖ ≤ HRS.CZ.Hls.hlsg_c s * ε ^ (-s - 1) := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sa16z_chi_nonneg ε z)]
  by_cases hz : ‖z‖ ≤ ε
  · rw [sa16z_chi_zero hε hz]; simp
    exact mul_nonneg (HRS.CZ.Hls.hlsg_c_nonneg hs0) (Real.rpow_nonneg hε.le _)
  · calc |sa16z_Kx s i z| * sa16z_chi d ε z ≤ |sa16z_Kx s i z| * 1 :=
          mul_le_mul_of_nonneg_left (sa16z_chi_le_one ε z) (abs_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact sa16z_Kx_bound_far hs0 i hε (not_le.1 hz).le

theorem sa16z_ibp_chi (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {F : Euc d → ℝ} (hF : IsCcInfty F)
    (i : Fin d) {ε : ℝ} (hε : 0 < ε) :
    ∫ z, F z * (sa16z_Kx s i z * sa16z_chi d ε z + rieszKernel d s z * sa16z_dchi d ε i z) =
      -∫ z, fderiv ℝ F z (sa16z_e i) * (rieszKernel d s z * sa16z_chi d ε z) := by
  have hH := sa16z_H_smooth (s := s) (d := d) hε
  have hibp := sa16sp_ibp_C1 (H := fun z : Euc d => rieszKernel d s z * sa16z_chi d ε z) (ψ := F)
    (hH.differentiable (by simp)) (sa16z_e i)
    ((hH.continuous_fderiv (by simp)).clm_apply continuous_const) hF
  rw [← hibp]
  refine integral_congr_ae ?_
  filter_upwards [HRS.Commutator.Whole.ae_ne_zero_euc hd] with z hz
  rw [sa16z_H_fderiv hε i hz]

end T3

end HRS.Whole.AppendixA.Phase2SA16R
