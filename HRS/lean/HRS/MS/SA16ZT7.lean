import HRS.MS.SA16ZT6

/-!
# S.A.16 (SA16Z) T7: `∂_i (g ⋆ f) = -c_s pvOdd_i f`

`sa16z_pv_tendsto` (`∫_{|z|>ε} K_i f(x-·) → ∂_i(g⋆f)(x)`) and `sa16z_conv_fderiv_pvOdd`:
for `f ∈ C_c^∞`, `0 ≤ s < d`, `θ = s + 2 - d`, `0 < θ < 2`:
`∂_i (g ⋆ f)(x) = -c_s · pvOdd d θ (u ↦ u_i) f x` (`c_s = s` for `s > 0`, `1` for `s = 0`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution RealInnerProductSpace

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section T7
variable {d : ℕ} {s : ℝ}

theorem sa16z_pv_tendsto (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {f : Euc d → ℝ} (hf : IsCcInfty f)
    (i : Fin d) (x : Euc d) :
    Tendsto (fun ε : ℝ => ∫ z in {z : Euc d | ε < ‖z‖}, sa16z_Kx s i z * f (x - z)) (𝓝[>] 0)
      (𝓝 (fderiv ℝ (convFun (rieszKernel d s) f) x (sa16z_e i))) := by
  set F : Euc d → ℝ := fun z => f (x - z) with hFdef
  have hF : IsCcInfty F := sa16z_F_cc hf x
  have hFint : Integrable F := hF.1.continuous.integrable_of_hasCompactSupport hF.2
  have hgm : Measurable (rieszKernel d s) := HRS.S16Frac.s16frac_g_meas d s
  -- the limit value
  have hL : fderiv ℝ (convFun (rieszKernel d s) f) x (sa16z_e i) =
      -∫ z, fderiv ℝ F z (sa16z_e i) * rieszKernel d s z := by
    rw [sa16z_conv_fderiv hs0 hsd hf, sa16sp_convFun_eq, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hFdef, sa16z_F_fderiv hf]
    ring
  rw [hL]
  have hR3 := sa16z_R3_tendsto hd hs0 hsd hF i
  have hR2 := sa16z_R2_tendsto hd hs0 hsd hF i
  have hE := sa16z_E_tendsto hd hs0 hsd hF i
  have hcomb := ((hR3.neg).sub hR2).add hE
  have hlim : -(∫ z, fderiv ℝ F z (sa16z_e i) * rieszKernel d s z) =
      -(∫ z, fderiv ℝ F z (sa16z_e i) * rieszKernel d s z) - 0 + 0 := by ring
  rw [hlim]
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : 0 < ε := hε
  -- integrability
  have hI1 : Integrable (fun z => F z * (sa16z_Kx s i z * sa16z_chi d ε z)) := by
    have := hFint.bdd_mul (f := fun z => sa16z_Kx s i z * sa16z_chi d ε z)
      ((sa16z_Kx_meas s i).mul (sa16z_chi_smooth ε).continuous.measurable).aestronglyMeasurable
      (Eventually.of_forall (sa16z_Kx_chi_bdd hs0 i hε0))
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.mul_apply]; ring
  have hI2 : Integrable (fun z => F z * (rieszKernel d s z * sa16z_dchi d ε i z)) := by
    have := sa16z_g_mul_int hs0 hsd (hF.1.continuous.mul (sa16z_dchi_cont ε i))
      ((sa16z_dchi_cs hε0 i).mul_left)
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.mul_apply]; ring
  have hI3 : Integrable (fun z => sa16z_w d ε z * (sa16z_Kx s i z * F z)) := by
    have := hFint.bdd_mul ((sa16z_w_meas ε).mul (sa16z_Kx_meas s i)).aestronglyMeasurable
      (Eventually.of_forall (sa16z_wK_bdd hs0 i hε0))
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.mul_apply]; ring
  have hibp := sa16z_ibp_chi hd hs0 hsd hF i hε0
  have hsplit : ∫ z, F z * (sa16z_Kx s i z * sa16z_chi d ε z + rieszKernel d s z * sa16z_dchi d ε i z) =
      (∫ z, F z * (sa16z_Kx s i z * sa16z_chi d ε z)) +
        ∫ z, F z * (rieszKernel d s z * sa16z_dchi d ε i z) := by
    rw [← integral_add hI1 hI2]
    exact integral_congr_ae (Eventually.of_forall fun z => by simp only; ring)
  rw [hsplit] at hibp
  -- sharp truncation = smooth + w
  have hsharp : ∫ z in {z : Euc d | ε < ‖z‖}, sa16z_Kx s i z * F z =
      (∫ z, F z * (sa16z_Kx s i z * sa16z_chi d ε z)) + ∫ z, sa16z_w d ε z * (sa16z_Kx s i z * F z) := by
    rw [← integral_add hI1 hI3, ← integral_indicator (measurableSet_lt measurable_const measurable_norm)]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [sa16z_w, indicator, mem_setOf_eq]
    split_ifs <;> ring
  rw [hsharp]
  linarith

end T7

end HRS.Whole.AppendixA.Phase2SA16R
