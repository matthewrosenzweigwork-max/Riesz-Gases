import HRS.MS.MfeConfAux72

/-!
# S.B.1, packet F8 (part 5): derivatives of `G = k * ρ` for a truncated kernel at one density

For `IsP4Kernel d s r₀ k`, `R : Sb1Rho ρ Cρ M1`:
`dG j = ∂_jG = cv (∂_jk) ρ` (`sb1_lv_dG_eq`), `∂_jG` is differentiable with derivative `∫ρ(y) D(∂_jk)(x-y)`
(`sb1_lv_dG_hasFDerivAt`), `|∂_jG| ≤ Lg`, `‖D∂_jG‖ ≤ L2`, the `(j,j)` Hessian entry `hjj` equals `cv (hjj k j) ρ` and also
`∫ ∂_jρ(y) ∂_jk(x-y) dy` (`sb1_lv_hjj_ibp`), hence is Lipschitz with constant `L2 ∫|∂_jρ|`.
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d : ℕ}

/-- the `(j,j)` entry of the Hessian of `k` -/
def sb1_lv_hjj (k : Euc d → ℝ) (j : Fin d) (z : Euc d) : ℝ := fderiv ℝ (sb1_lv_dk k j) z (sb1e j)

theorem sb1_lv_hjj_bound {k : Euc d → ℝ} (hk : ContDiff ℝ 2 k) {L2 : ℝ}
    (hL : ∀ z, ‖fderiv ℝ (fderiv ℝ k) z‖ ≤ L2) (j : Fin d) (z : Euc d) : |sb1_lv_hjj k j z| ≤ L2 :=
  (sb1_apply_single_le _ j).trans (sb1_lv_dk_fderiv_bound hk hL j z)

theorem sb1_lv_hjj_cont {k : Euc d → ℝ} (hk : ContDiff ℝ 2 k) (j : Fin d) : Continuous (sb1_lv_hjj k j) :=
  (sb1_lv_dk_fderiv_cont hk j).clm_apply continuous_const

theorem sb1_lv_gr_hjj {k : Euc d → ℝ} (hk : ContDiff ℝ 2 k) {L2 : ℝ}
    (hL : ∀ z, ‖fderiv ℝ (fderiv ℝ k) z‖ ≤ L2) (j : Fin d) : Sb1Gr (sb1_lv_hjj k j) L2 := by
  refine ⟨(sb1_lv_hjj_cont hk j).measurable, fun z => ?_⟩
  have h0 : 0 ≤ Real.log (1 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
  linarith [sb1_lv_hjj_bound hk hL j z]

section Dens

variable {ρ : Euc d → ℝ} {Cρ M1 : ℝ}

theorem Sb1Rho.meas' (R : Sb1Rho ρ Cρ M1) : AEStronglyMeasurable ρ volume :=
  R.integrable.aestronglyMeasurable

theorem Sb1Rho.abs_mom (R : Sb1Rho ρ Cρ M1) : Integrable (fun y => |ρ y| * ‖y‖) := by
  refine R.mom.congr (Eventually.of_forall fun y => ?_)
  simp only [abs_of_nonneg (R.dens.nonneg y)]

theorem sb1_lv_dG_eq {s r₀ : ℝ} {k : Euc d → ℝ} (hk4 : IsP4Kernel d s r₀ k) (hd : 1 ≤ d) (hs0 : 0 ≤ s)
    (hsd : s < d) {Lg : ℝ} (hR : Sb1KerR d k Lg) (R : Sb1Rho ρ Cρ M1) (j : Fin d) (x : Euc d) :
    fderiv ℝ (sb1G k ρ) x (sb1e j) = sb1_lv_cv (sb1_lv_dk k j) ρ x :=
  sb1_fderiv_G_apply hd hs0 hsd (sb1KerU_of_p4 hs0 hk4) hR R x (sb1e j)

theorem sb1_lv_dG_hasFDerivAt {s r₀ : ℝ} {k : Euc d → ℝ} (hk4 : IsP4Kernel d s r₀ k) (hd : 1 ≤ d)
    (hs0 : 0 ≤ s) (hsd : s < d) {Lg L2 : ℝ} (hR : Sb1KerR d k Lg) (hL : ∀ z, ‖fderiv ℝ k z‖ ≤ Lg)
    (hL2 : ∀ z, ‖fderiv ℝ (fderiv ℝ k) z‖ ≤ L2) (R : Sb1Rho ρ Cρ M1) (j : Fin d) (x : Euc d) :
    HasFDerivAt (fun x => fderiv ℝ (sb1G k ρ) x (sb1e j)) (∫ y, ρ y • fderiv ℝ (sb1_lv_dk k j) (x - y)) x := by
  have e : (fun x => fderiv ℝ (sb1G k ρ) x (sb1e j)) = sb1_lv_cv (sb1_lv_dk k j) ρ :=
    funext fun x => sb1_lv_dG_eq hk4 hd hs0 hsd hR R j x
  rw [e]
  exact sb1_lv_cv_hasFDerivAt (sb1_lv_gr_dk hk4.smooth hL j) (sb1_lv_dk_diff hk4.smooth j)
    (sb1_lv_dk_fderiv_cont hk4.smooth j) (sb1_lv_dk_fderiv_bound hk4.smooth hL2 j) R.meas' R.integrable R.abs_mom x

theorem sb1_lv_hjj_eq {s r₀ : ℝ} {k : Euc d → ℝ} (hk4 : IsP4Kernel d s r₀ k) (hd : 1 ≤ d)
    (hs0 : 0 ≤ s) (hsd : s < d) {Lg L2 : ℝ} (hR : Sb1KerR d k Lg) (hL : ∀ z, ‖fderiv ℝ k z‖ ≤ Lg)
    (hL2 : ∀ z, ‖fderiv ℝ (fderiv ℝ k) z‖ ≤ L2) (R : Sb1Rho ρ Cρ M1) (j : Fin d) (x : Euc d) :
    fderiv ℝ (fun x => fderiv ℝ (sb1G k ρ) x (sb1e j)) x (sb1e j) = sb1_lv_cv (sb1_lv_hjj k j) ρ x := by
  rw [(sb1_lv_dG_hasFDerivAt hk4 hd hs0 hsd hR hL hL2 R j x).fderiv]
  have hint : Integrable (fun y => ρ y • fderiv ℝ (sb1_lv_dk k j) (x - y)) := by
    refine (R.integrable.norm.mul_const L2).mono' (R.meas'.smul
      ((sb1_lv_dk_fderiv_cont hk4.smooth j).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (sb1_lv_dk_fderiv_bound hk4.smooth hL2 j _) (norm_nonneg _)
  rw [ContinuousLinearMap.integral_apply hint]
  rfl

theorem sb1_lv_hjj_ibp {s r₀ : ℝ} {k : Euc d → ℝ} (hk4 : IsP4Kernel d s r₀ k) {Lg L2 : ℝ}
    (hL : ∀ z, ‖fderiv ℝ k z‖ ≤ Lg) (hL2 : ∀ z, ‖fderiv ℝ (fderiv ℝ k) z‖ ≤ L2)
    (R : Sb1Rho ρ Cρ M1) (hρd : Differentiable ℝ ρ) (hρ' : Continuous (fderiv ℝ ρ)) (j : Fin d)
    (hρ'i : Integrable (fun y => fderiv ℝ ρ y (sb1e j))) (x : Euc d) :
    sb1_lv_cv (sb1_lv_hjj k j) ρ x = sb1_lv_cv (sb1_lv_dk k j) (fun y => fderiv ℝ ρ y (sb1e j)) x := by
  unfold sb1_lv_cv sb1_lv_hjj
  exact sb1_lv_ibp_cv (sb1_lv_dk_diff hk4.smooth j) (sb1_lv_dk_fderiv_cont hk4.smooth j)
    (sb1_lv_dk_fderiv_bound hk4.smooth hL2 j) (sb1_lv_dk_bound hL j) hρd hρd.continuous hρ' R.integrable
    (sb1e j) hρ'i x

theorem sb1_lv_hjj_lip {s r₀ : ℝ} {k : Euc d → ℝ} (hk4 : IsP4Kernel d s r₀ k) {Lg L2 : ℝ}
    (hL : ∀ z, ‖fderiv ℝ k z‖ ≤ Lg) (hL2 : ∀ z, ‖fderiv ℝ (fderiv ℝ k) z‖ ≤ L2)
    (R : Sb1Rho ρ Cρ M1) (hρd : Differentiable ℝ ρ) (hρ' : Continuous (fderiv ℝ ρ)) (j : Fin d)
    (hρ'i : Integrable (fun y => fderiv ℝ ρ y (sb1e j)))
    (hρ'm : Integrable (fun y => |fderiv ℝ ρ y (sb1e j)| * ‖y‖)) (x x' : Euc d) :
    |sb1_lv_cv (sb1_lv_hjj k j) ρ x - sb1_lv_cv (sb1_lv_hjj k j) ρ x'| ≤
      L2 * ‖x - x'‖ * ∫ y, |fderiv ℝ ρ y (sb1e j)| := by
  rw [sb1_lv_hjj_ibp hk4 hL hL2 R hρd hρ' j hρ'i x, sb1_lv_hjj_ibp hk4 hL hL2 R hρd hρ' j hρ'i x']
  exact sb1_lv_cv_lip (sb1_lv_gr_dk hk4.smooth hL j) (sb1_lv_dk_lip hk4.smooth hL2 j)
    (hρ'.clm_apply continuous_const).aestronglyMeasurable hρ'i hρ'm x x'

end Dens

end HRS.MS.MfeConf
