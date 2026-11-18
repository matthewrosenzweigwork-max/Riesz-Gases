import HRS.MS.R26T8AP22h
import HRS.MS.R26T8AP07i

/-!
# S8.2 local Newton layer, packet T8A.P22 (part i): representation formula for the cut-off leading inverse
`r26t8a_p22_poisson_repr`: `∫ K(z-w) Δg(w) dw = -g(z)/(2 nu)` for `g` of class `C^2` with compact support.
`r26t8a_p22_phi_contDiff`, `r26t8a_p22_phi_cs`: `phi_eps` is `C^2` with compact support.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82N

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_p22_poisson_repr (hd : 2 ≤ d) (nu : ℝ) (hnu : 0 < nu) {g : Euc d → ℝ} (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport g) (z : Euc d) :
    ∫ w, newtonKernel d nu (z - w) * Laplacian.laplacian g w = -g z / (2 * nu) := by
  have h := HRS.Parx.weak_poisson hd hg hc z
  have e1 : ∫ w, newtonKernel d nu (z - w) * Laplacian.laplacian g w =
      ∫ x, newtonKernel d nu x * Laplacian.laplacian g (z - x) := by
    rw [← integral_sub_left_eq_self (fun w => newtonKernel d nu (z - w) * Laplacian.laplacian g w) volume z]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [sub_sub_cancel]
  rw [e1]
  have e2 : ∀ x : Euc d, newtonKernel d nu x * Laplacian.laplacian g (z - x) =
      (1 / (2 * nu)) * (HRS.Parx.Efund d x * Laplacian.laplacian g (z - x)) := by
    intro x
    rw [r26t8a_p14_kernel_eq hd, HRS.Parx.newtonKernel_eq]; ring
  simp_rw [e2]
  rw [integral_const_mul, h]
  field_simp

theorem r26t8a_p22_phi_contDiff (nu : ℝ) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) {chi : Euc d → ℝ}
    (hchi : NewtonCutoff chi) {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 2 (r26t8a_p22_phi nu B chi ε) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : w = 0
  · subst hw
    have hev : r26t8a_p22_phi nu B chi ε =ᶠ[𝓝 (0 : Euc d)] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds (show ‖(0 : Euc d)‖ < ε by simpa using hε)]
        with y hy
      have : r26t8a_p22_theta chi ε y = 0 := by
        unfold r26t8a_p22_theta
        rw [hchi.2.2.2.1 _ (by rw [norm_smul, norm_inv, Real.norm_of_nonneg hε.le]; rw [inv_mul_le_iff₀ hε]; linarith [(show ‖y‖ < ε from hy)])]
        ring
      simp [r26t8a_p22_phi, this]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hL2 : ContDiffAt ℝ 2 (s82n_leadingInverse nu B) w := by
      have h : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (s82n_leadingInverse nu B) w :=
        contDiffAt_infty.1 (r26t8a_p22_L_contDiffAt nu B hw) 2
      exact_mod_cast h
    exact (r26t8a_p22_theta_contDiff hchi ε).contDiffAt.mul ((r26t8a_p22_chi_c2 hchi).contDiffAt.mul hL2)

theorem r26t8a_p22_phi_cs (nu : ℝ) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) {chi : Euc d → ℝ}
    (hchi : NewtonCutoff chi) (ε : ℝ) : HasCompactSupport (r26t8a_p22_phi nu B chi ε) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) 2) (fun w hw => ?_)
  have : 2 < ‖w‖ := by simpa using hw
  simp [r26t8a_p22_phi, hchi.2.2.2.2 w this.le]

end HRS.MS.R26T8A
