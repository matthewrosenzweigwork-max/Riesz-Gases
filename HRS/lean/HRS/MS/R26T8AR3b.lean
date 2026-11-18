import HRS.MS.R26T8AR3a

/-!
# S8.2 T8A R3b: the Hessian of the leading inverse `LI ν B` is homogeneous of degree `-s`, with bound `C ‖B‖ |z|^(-s)`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad HRS.MS.S82N

variable {d : ℕ}

theorem r26t8a_R3_L_diffD (nu : ℝ) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) {u : Euc d} (hu : u ≠ 0) :
    DifferentiableAt ℝ (fderiv ℝ (s82n_leadingInverse nu B)) u :=
  ((r26t8a_p22_L_contDiffAt nu B hu).fderiv_right (m := 1) (by simp)).differentiableAt (by simp)

theorem r26t8a_R3_L_hess_scale (nu : ℝ) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) {z : Euc d} (hz : z ≠ 0) {t : ℝ}
    (ht : 0 < t) :
    fderiv ℝ (fderiv ℝ (s82n_leadingInverse nu B)) (t • z) =
      t ^ (-s82n_critS d) • fderiv ℝ (fderiv ℝ (s82n_leadingInverse nu B)) z := by
  set L := s82n_leadingInverse nu B with hL
  have htz : t • z ≠ 0 := smul_ne_zero ht.ne' hz
  have hh : HasFDerivAt (fun w : Euc d => t • w) (t • ContinuousLinearMap.id ℝ (Euc d)) z :=
    (hasFDerivAt_id z).const_smul t
  have hcomp := ((r26t8a_R3_L_diffD nu B htz).hasFDerivAt.comp z hh).fderiv
  have hev : (fun u => fderiv ℝ L (t • u)) =ᶠ[𝓝 z] fun u => t ^ (1 - s82n_critS d) • fderiv ℝ L u := by
    filter_upwards [isOpen_ne.mem_nhds hz] with u hu using r26t8a_p22_fderiv_scale nu B hu ht
  have hrhs : fderiv ℝ (fun u => t ^ (1 - s82n_critS d) • fderiv ℝ L u) z =
      t ^ (1 - s82n_critS d) • fderiv ℝ (fderiv ℝ L) z :=
    ((r26t8a_R3_L_diffD nu B hz).hasFDerivAt.const_smul (t ^ (1 - s82n_critS d))).fderiv
  have hlhs : fderiv ℝ (fun u => fderiv ℝ L (t • u)) z =
      (fderiv ℝ (fderiv ℝ L) (t • z)).comp (t • ContinuousLinearMap.id ℝ (Euc d)) := hcomp
  rw [hev.fderiv_eq, hrhs] at hlhs
  have h2 : t ^ (1 - s82n_critS d) = t * t ^ (-s82n_critS d) := by
    have : (1 : ℝ) - s82n_critS d = 1 + (-s82n_critS d) := by ring
    rw [this, Real.rpow_add ht, Real.rpow_one]
  refine ContinuousLinearMap.ext fun v => ?_
  have hv := congrArg (fun T => T v) hlhs
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, map_smul,
    h2, mul_smul] at hv
  rw [ContinuousLinearMap.smul_apply]
  have hv' := smul_right_injective (Euc d →L[ℝ] ℝ) ht.ne'
  have : t • (fderiv ℝ (fderiv ℝ L) (t • z) v) = t • (t ^ (-s82n_critS d) • fderiv ℝ (fderiv ℝ L) z v) := by
    simpa [smul_smul] using hv.symm
  exact hv' this

set_option maxHeartbeats 1600000 in
theorem r26t8a_R3_sphere_hess (nu : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ), ∀ om ∈ sphere (0 : Euc d) 1,
      ‖fderiv ℝ (fderiv ℝ (s82n_leadingInverse nu B)) om‖ ≤ C * ‖B‖ := by
  refine r26t8a_p22_unif (isCompact_sphere _ _)
    (fun (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) om => fderiv ℝ (fderiv ℝ (s82n_leadingInverse nu B)) om)
    (fun B1 B2 x hx => ?_) (fun c B x hx => ?_) (fun B => fun om hom => ?_)
  · have e : s82n_leadingInverse nu (B1 + B2) = s82n_leadingInverse nu B1 + s82n_leadingInverse nu B2 :=
      funext fun z => r26t8a_p22_L_add nu B1 B2 z
    have hne := r26t8a_p22_sphere_ne x hx
    show fderiv ℝ (fderiv ℝ (s82n_leadingInverse nu (B1 + B2))) x =
      fderiv ℝ (fderiv ℝ (s82n_leadingInverse nu B1)) x + fderiv ℝ (fderiv ℝ (s82n_leadingInverse nu B2)) x
    have hev : fderiv ℝ (s82n_leadingInverse nu (B1 + B2)) =ᶠ[𝓝 x]
        fun u => fderiv ℝ (s82n_leadingInverse nu B1) u + fderiv ℝ (s82n_leadingInverse nu B2) u := by
      filter_upwards [isOpen_ne.mem_nhds hne] with u hu
      rw [e]
      exact fderiv_add ((r26t8a_p22_L_contDiffAt nu B1 hu).differentiableAt (by simp))
        ((r26t8a_p22_L_contDiffAt nu B2 hu).differentiableAt (by simp))
    rw [hev.fderiv_eq]
    exact fderiv_add (r26t8a_R3_L_diffD nu B1 hne) (r26t8a_R3_L_diffD nu B2 hne)
  · have e : s82n_leadingInverse nu (c • B) = fun z => c * s82n_leadingInverse nu B z :=
      funext fun z => r26t8a_p22_L_smul nu c B z
    have hne := r26t8a_p22_sphere_ne x hx
    show fderiv ℝ (fderiv ℝ (s82n_leadingInverse nu (c • B))) x = c • fderiv ℝ (fderiv ℝ (s82n_leadingInverse nu B)) x
    have hev : fderiv ℝ (s82n_leadingInverse nu (c • B)) =ᶠ[𝓝 x] fun u => c • fderiv ℝ (s82n_leadingInverse nu B) u := by
      filter_upwards [isOpen_ne.mem_nhds hne] with u hu
      rw [e]
      exact fderiv_const_mul ((r26t8a_p22_L_contDiffAt nu B hu).differentiableAt (by simp)) c
    rw [hev.fderiv_eq]
    exact fderiv_const_smul (r26t8a_R3_L_diffD nu B hne) c
  · have h1 := (r26t8a_p22_L_contDiffAt nu B (r26t8a_p22_sphere_ne om hom)).fderiv_right (m := 1) (by simp)
    have := h1.fderiv_right (m := 0) (by simp)
    exact this.continuousAt.continuousWithinAt

theorem r26t8a_R3_L_hess (hd : 2 ≤ d) (nu : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (z : Euc d), z ≠ 0 →
      ‖fderiv ℝ (fderiv ℝ (s82n_leadingInverse nu B)) z‖ ≤ C * ‖B‖ * ‖z‖ ^ (-s82n_critS d) := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_R3_sphere_hess (d := d) nu
  refine ⟨C, hC0, fun B z hz => ?_⟩
  have ht : 0 < ‖z‖ := norm_pos_iff.2 hz
  set om : Euc d := ‖z‖⁻¹ • z with homdef
  have hom : om ∈ sphere (0 : Euc d) 1 := by
    simp only [mem_sphere_iff_norm, sub_zero, homdef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ht]
    field_simp
  have hz' : z = ‖z‖ • om := by
    simp only [homdef, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have := hC B om hom
  conv_lhs => rw [hz', r26t8a_R3_L_hess_scale nu B (r26t8a_p22_sphere_ne om hom) ht]
  refine (ContinuousLinearMap.opNorm_smul_le (‖z‖ ^ (-s82n_critS d)) (fderiv ℝ (fderiv ℝ (s82n_leadingInverse nu B)) om)).trans ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht.le _)]
  calc ‖z‖ ^ (-s82n_critS d) * ‖fderiv ℝ (fderiv ℝ (s82n_leadingInverse nu B)) om‖
      ≤ ‖z‖ ^ (-s82n_critS d) * (C * ‖B‖) := mul_le_mul_of_nonneg_left this (Real.rpow_nonneg ht.le _)
    _ = _ := by ring

end HRS.MS.R26T8A
