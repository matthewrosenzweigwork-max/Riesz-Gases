import HRS.MS.R26T8AP22j

/-!
# S8.2 local Newton layer, packet T8A.P22 (part k): the annular commutator source `c_B`
`c_B = 2 <∇chi, ∇L_B> + L_B Δchi` is `C^∞` with support in `1 <= |w| <= 2`, and linear in `B`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82N

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_p22_lap_contDiff {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (Laplacian.laplacian f) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis f]
  refine ContDiff.sum fun i _ => ?_
  have h1 : ContDiff ℝ ∞ (fun x => iteratedFDeriv ℝ 2 f x) := hf.iteratedFDeriv_right (by simp)
  exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d) ℝ
    ![(stdOrthonormalBasis ℝ (Euc d)) i, (stdOrthonormalBasis ℝ (Euc d)) i]).contDiff).comp h1

theorem r26t8a_p22_grad_contDiffAt {f : Euc d → ℝ} {w : Euc d} (hf : ContDiffAt ℝ ∞ f w) :
    ContDiffAt ℝ ∞ (gradient f) w := by
  have h1 : ContDiffAt ℝ ∞ (fderiv ℝ f) w := hf.fderiv_right (by simp)
  exact ((InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.contDiffAt).comp w h1

theorem r26t8a_p22_cfun_flat {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (nu : ℝ) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)
    {w : Euc d} (hw : ‖w‖ ≤ 1 ∨ 2 ≤ ‖w‖) : r26t8a_p22_cfun nu B chi w = 0 := by
  obtain ⟨h1, h2⟩ := r26t8a_p22_chi_flat hchi hw
  simp [r26t8a_p22_cfun, gradient, h1, h2]

theorem r26t8a_p22_cfun_contDiff (nu : ℝ) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) :
    ContDiff ℝ ∞ (r26t8a_p22_cfun nu B chi) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : ‖w‖ < 1
  · have hev : r26t8a_p22_cfun nu B chi =ᶠ[𝓝 w] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hw] with y hy
      exact r26t8a_p22_cfun_flat hchi nu B (Or.inl (le_of_lt hy))
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hw0 : w ≠ 0 := by
      intro h; rw [h, norm_zero] at hw; exact hw one_pos
    have hc : ContDiffAt ℝ ∞ chi w := hchi.1.contDiffAt
    have hL := r26t8a_p22_L_contDiffAt nu B hw0
    unfold r26t8a_p22_cfun
    exact (contDiffAt_const.mul ((r26t8a_p22_grad_contDiffAt hc).inner ℝ (r26t8a_p22_grad_contDiffAt hL))).add
      (hL.mul (r26t8a_p22_lap_contDiff hchi.1).contDiffAt)

theorem r26t8a_p22_cfun_cs (nu : ℝ) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) :
    HasCompactSupport (r26t8a_p22_cfun nu B chi) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) 2) (fun w hw => ?_)
  have : 2 < ‖w‖ := by simpa using hw
  exact r26t8a_p22_cfun_flat hchi nu B (Or.inr this.le)

theorem r26t8a_p22_cfun_add (nu : ℝ) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (B1 B2 : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)
    (w : Euc d) : r26t8a_p22_cfun nu (B1 + B2) chi w = r26t8a_p22_cfun nu B1 chi w + r26t8a_p22_cfun nu B2 chi w := by
  by_cases hw : w = 0
  · subst hw
    have h0 : ‖(0 : Euc d)‖ ≤ 1 ∨ 2 ≤ ‖(0 : Euc d)‖ := Or.inl (by simp)
    rw [r26t8a_p22_cfun_flat hchi nu _ h0, r26t8a_p22_cfun_flat hchi nu _ h0, r26t8a_p22_cfun_flat hchi nu _ h0]
    simp
  · have e : s82n_leadingInverse nu (B1 + B2) = s82n_leadingInverse nu B1 + s82n_leadingInverse nu B2 :=
      funext fun z => r26t8a_p22_L_add nu B1 B2 z
    have d1 : DifferentiableAt ℝ (s82n_leadingInverse nu B1) w :=
      (r26t8a_p22_L_contDiffAt nu B1 hw).differentiableAt (by simp)
    have d2 : DifferentiableAt ℝ (s82n_leadingInverse nu B2) w :=
      (r26t8a_p22_L_contDiffAt nu B2 hw).differentiableAt (by simp)
    have hg : gradient (s82n_leadingInverse nu (B1 + B2)) w =
        gradient (s82n_leadingInverse nu B1) w + gradient (s82n_leadingInverse nu B2) w := by
      rw [e]
      simp only [gradient]
      rw [show (s82n_leadingInverse nu B1 + s82n_leadingInverse nu B2) = fun x => s82n_leadingInverse nu B1 x + s82n_leadingInverse nu B2 x from rfl,
        fderiv_fun_add d1 d2, map_add]
    unfold r26t8a_p22_cfun
    rw [hg, e]
    simp only [Pi.add_apply, inner_add_right]
    ring

theorem r26t8a_p22_cfun_smul (nu c : ℝ) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)
    (w : Euc d) : r26t8a_p22_cfun nu (c • B) chi w = c * r26t8a_p22_cfun nu B chi w := by
  by_cases hw : w = 0
  · subst hw
    have h0 : ‖(0 : Euc d)‖ ≤ 1 ∨ 2 ≤ ‖(0 : Euc d)‖ := Or.inl (by simp)
    rw [r26t8a_p22_cfun_flat hchi nu _ h0, r26t8a_p22_cfun_flat hchi nu _ h0]
    simp
  · have e : s82n_leadingInverse nu (c • B) = fun z => c * s82n_leadingInverse nu B z :=
      funext fun z => r26t8a_p22_L_smul nu c B z
    have d1 : DifferentiableAt ℝ (s82n_leadingInverse nu B) w :=
      (r26t8a_p22_L_contDiffAt nu B hw).differentiableAt (by simp)
    have hg : gradient (s82n_leadingInverse nu (c • B)) w = c • gradient (s82n_leadingInverse nu B) w := by
      rw [e]
      simp only [gradient]
      rw [fderiv_const_mul d1, map_smul]
    unfold r26t8a_p22_cfun
    rw [hg, e]
    simp only [inner_smul_right, smul_eq_mul]
    ring

end HRS.MS.R26T8A
