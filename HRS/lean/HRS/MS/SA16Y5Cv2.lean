import HRS.MS.SA16Y5Cv1

/-!
# S.A.16 (SA16Y5) Cv2: the derivative of the Riesz potential splits into near and far kernels (K1)

`sa16y5_D1`: for `0 < s < d`, `u ∈ C_c^∞`, `ε > 0`:
`∂_i (ρ ⋆ u) = rn_ε ⋆ ∂_i u + V_{ε,i} ⋆ u` with `ρ = |z|^{-s}` (`rn_ε` integrable, `V_{ε,i}` the derivative of the far part).
`sa16y5_ddg_cv`: `(∂_i∂_j g_a) ⋆ φ = g_a ⋆ ∂_i∂_j φ` for `φ ∈ C_c^∞`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Cv2
variable {d : ℕ} {s : ℝ}

lemma sa16y5_rho_loc (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) :
    LocallyIntegrable (rieszKernel d s) volume :=
  rieszKernel_locallyIntegrable (d := d) hs.le hsd

theorem sa16y5_D1 (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) {u : Euc d → ℝ} (hu : IsCcInfty u) (i : Fin d)
    {ε : ℝ} (hε : 0 < ε) (x : Euc d) :
    fderiv ℝ (sa16r_cv (rieszKernel d s) u) x (sa16z_e i) =
      sa16r_cv (sa16y5_rn d s ε) (fun y => fderiv ℝ u y (sa16z_e i)) x + sa16r_cv (sa16y5_V d s ε i) u x := by
  rw [sa16y5_cv_fderiv (sa16y5_rho_loc hd hs hsd) hu]
  have hui : IsCcInfty (fun y => fderiv ℝ u y (sa16z_e i)) := sa16s_cc_fderiv hu (sa16z_e i)
  have hrn : Integrable (sa16y5_rn d s ε) := (sa16y5_rn_L1 hd hs hsd hε).1
  have hH := sa16z_H_smooth (s := s) (d := d) hε
  have hint1 := sa16r_cv_integrand hrn hui x
  have hint2 : Integrable (fun z => rieszKernel d s z * sa16z_chi d ε z * fderiv ℝ u (x - z) (sa16z_e i)) := by
    have hc : Continuous (fun z => rieszKernel d s z * sa16z_chi d ε z * fderiv ℝ u (x - z) (sa16z_e i)) :=
      hH.continuous.mul (((hu.1.continuous_fderiv (by simp)).clm_apply continuous_const).comp
        (continuous_const.sub continuous_id))
    refine hc.integrable_of_hasCompactSupport ?_
    exact (sa16z_F_cc hui x).2.mul_left
  have hsplit : sa16r_cv (rieszKernel d s) (fun y => fderiv ℝ u y (sa16z_e i)) x =
      sa16r_cv (sa16y5_rn d s ε) (fun y => fderiv ℝ u y (sa16z_e i)) x +
        ∫ z, rieszKernel d s z * sa16z_chi d ε z * fderiv ℝ u (x - z) (sa16z_e i) := by
    unfold sa16r_cv
    rw [← integral_add hint1 hint2]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [sa16y5_rn]
    ring
  rw [hsplit]
  congr 1
  have hibp := sa16z_ibp_chi hd hs.le hsd (sa16z_F_cc hu x) i hε
  unfold sa16r_cv
  have e1 : ∫ z, sa16y5_V d s ε i z * u (x - z) =
      ∫ z, u (x - z) * (sa16z_Kx s i z * sa16z_chi d ε z + rieszKernel d s z * sa16z_dchi d ε i z) := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [sa16y5_V]
    ring
  rw [e1, hibp, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [sa16z_F_fderiv hu x z]
  ring

lemma sa16y5_ddg_cv {a : ℝ} (ha : 0 < a) {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (i j : Fin d) (x : Euc d) :
    sa16r_cv (sa16y5_ddg d a i j) φ x =
      sa16r_cv (sa16r_g d a) (fun y => fderiv ℝ (fun y' => fderiv ℝ φ y' (sa16z_e i)) y (sa16z_e j)) x := by
  have h1 : sa16r_cv (sa16y5_ddg d a i j) φ x = ∫ z, sa16r_dg d a j z * fderiv ℝ φ (x - z) (sa16z_e i) := by
    unfold sa16r_cv
    have := sa16r_ibp_gen (sa16r_dg_contDiff a j) hφ x (sa16z_e i)
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show _ = fderiv ℝ (sa16r_dg d a j) z (EuclideanSpace.single i 1) * _
    rw [sa16y5_dg_fderiv ha i j z]
  rw [h1]
  exact sa16r_ibp_g ha (sa16s_cc_fderiv hφ (sa16z_e i)) x j

end Cv2

end HRS.Whole.AppendixA.Phase2SA16R
