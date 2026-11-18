import HRS.MS.SA16ZT7

/-!
# S.A.16 (SA16Z) T8: `∂_i (g ⋆ f) = -c_s pvOdd_i f` (frozen `pvOdd`)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution RealInnerProductSpace

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section T8
variable {d : ℕ} {s : ℝ}

lemma sa16z_Kx_pv (s : ℝ) (i : Fin d) (z : Euc d) :
    sa16z_Kx s i z = -(HRS.CZ.Hls.hlsg_c s) *
      ((fun u : Euc d => u i) (‖z‖⁻¹ • z) / ‖z‖ ^ ((d : ℝ) + (s + 2 - d) - 1)) := by
  by_cases hz : z = 0
  · subst hz; simp [sa16z_Kx]
  · have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
    have h1 : (d : ℝ) + (s + 2 - d) - 1 = s + 1 := by ring
    rw [h1]
    simp only [sa16z_Kx, PiLp.smul_apply, smul_eq_mul]
    have h2 : ‖z‖ ^ (-s - 2) = ‖z‖⁻¹ / ‖z‖ ^ (s + 1) := by
      rw [← Real.rpow_neg_one ‖z‖, ← Real.rpow_sub hzpos]
      congr 1; ring
    rw [h2]
    field_simp

theorem sa16z_conv_fderiv_pvOdd (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {f : Euc d → ℝ}
    (hf : IsCcInfty f) (i : Fin d) (x : Euc d) :
    fderiv ℝ (convFun (rieszKernel d s) f) x (sa16z_e i) =
      -(HRS.CZ.Hls.hlsg_c s) * pvOdd d (s + 2 - d) (fun u : Euc d => u i) f x := by
  have hc := HRS.CZ.Hls.hlsg_c_pos hs0
  have hT := sa16z_pv_tendsto hd hs0 hsd hf i x
  have hT' : Tendsto (fun ε : ℝ => ∫ z in {z : Euc d | ε < ‖z‖},
      (fun u : Euc d => u i) (‖z‖⁻¹ • z) / ‖z‖ ^ ((d : ℝ) + (s + 2 - d) - 1) * f (x - z)) (𝓝[>] 0)
      (𝓝 (-(HRS.CZ.Hls.hlsg_c s)⁻¹ * fderiv ℝ (convFun (rieszKernel d s) f) x (sa16z_e i))) := by
    have := hT.const_mul (-(HRS.CZ.Hls.hlsg_c s)⁻¹)
    refine this.congr (fun ε => ?_)
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_lt measurable_const measurable_norm) fun z _ => ?_
    simp only
    rw [sa16z_Kx_pv s i z]
    field_simp
  unfold pvOdd
  rw [hT'.limUnder_eq]
  field_simp
