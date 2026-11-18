import Mathlib
import HRS.MS.S82WJ1

/-!
# S8.2 A05 (S82W), part 1: jets of compositions with a linear map and of finite sums (on an open set)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff

namespace HRS.MS.S82W

section lin
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma w_lin_fderiv (F : G → ℝ) {U : Set G} (hU : IsOpen U) (hF : ContDiffOn ℝ 2 F U) (L : E →L[ℝ] G) {z : E}
    (hz : L z ∈ U) : fderiv ℝ (fun y => F (L y)) z = (fderiv ℝ F (L z)).comp L := by
  have hd : DifferentiableAt ℝ F (L z) :=
    (hF.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hz)
  exact (hd.hasFDerivAt.comp z L.hasFDerivAt).fderiv

lemma w_lin_jets (F : G → ℝ) {U : Set G} (hU : IsOpen U) (hF : ContDiffOn ℝ 2 F U) (L : E →L[ℝ] G) {x : E}
    (hx : L x ∈ U) :
    ‖fderiv ℝ (fun y => F (L y)) x‖ ≤ ‖fderiv ℝ F (L x)‖ * ‖L‖ ∧
    ‖fderiv ℝ (fderiv ℝ (fun y => F (L y))) x‖ ≤ ‖fderiv ℝ (fderiv ℝ F) (L x)‖ * ‖L‖ ^ 2 := by
  have hUo : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  set R : (G →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) := (ContinuousLinearMap.compL ℝ E G ℝ).flip L with hR
  have hRapp : ∀ T : G →L[ℝ] ℝ, R T = T.comp L := fun T => rfl
  have hRn : ‖R‖ ≤ ‖L‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun T => ?_
    rw [hRapp]
    calc ‖T.comp L‖ ≤ ‖T‖ * ‖L‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖L‖ * ‖T‖ := mul_comm _ _
  have h1 : ‖fderiv ℝ (fun y => F (L y)) x‖ ≤ ‖fderiv ℝ F (L x)‖ * ‖L‖ := by
    rw [w_lin_fderiv F hU hF L hx]; exact ContinuousLinearMap.opNorm_comp_le _ _
  refine ⟨h1, ?_⟩
  have hev : fderiv ℝ (fun y => F (L y)) =ᶠ[𝓝 x] fun z => R (fderiv ℝ F (L z)) := by
    filter_upwards [hUo.mem_nhds hx] with z hz
    rw [w_lin_fderiv F hU hF L hz]; rfl
  have hg : ContDiffAt ℝ 1 (fderiv ℝ F) (L x) :=
    (hF.contDiffAt (hU.mem_nhds hx)).fderiv_right (by norm_num)
  have hgd : DifferentiableAt ℝ (fderiv ℝ F) (L x) := hg.differentiableAt one_ne_zero
  have h2 : HasFDerivAt (fun z : E => R (fderiv ℝ F (L z))) (R.comp ((fderiv ℝ (fderiv ℝ F) (L x)).comp L)) x :=
    R.hasFDerivAt.comp x (hgd.hasFDerivAt.comp x L.hasFDerivAt)
  rw [hev.fderiv_eq, h2.fderiv]
  calc ‖R.comp ((fderiv ℝ (fderiv ℝ F) (L x)).comp L)‖
      ≤ ‖R‖ * ‖(fderiv ℝ (fderiv ℝ F) (L x)).comp L‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖L‖ * (‖fderiv ℝ (fderiv ℝ F) (L x)‖ * ‖L‖) := by
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖fderiv ℝ (fderiv ℝ F) (L x)‖ * ‖L‖ ^ 2 := by ring

lemma w_sum_jets {ι : Type*} (s : Finset ι) (t : ι → E → ℝ) {U : Set E} (hU : IsOpen U)
    (ht : ∀ k ∈ s, ContDiffOn ℝ 2 (t k) U) {x : E} (hx : x ∈ U) :
    ‖fderiv ℝ (fun y => ∑ k ∈ s, t k y) x‖ ≤ ∑ k ∈ s, ‖fderiv ℝ (t k) x‖ ∧
    ‖fderiv ℝ (fderiv ℝ (fun y => ∑ k ∈ s, t k y)) x‖ ≤ ∑ k ∈ s, ‖fderiv ℝ (fderiv ℝ (t k)) x‖ := by
  have hd : ∀ k ∈ s, ∀ y ∈ U, DifferentiableAt ℝ (t k) y := fun k hk y hy =>
    ((ht k hk).differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hy)
  have hdd : ∀ k ∈ s, DifferentiableAt ℝ (fderiv ℝ (t k)) x := fun k hk =>
    (((ht k hk).contDiffAt (hU.mem_nhds hx)).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hev : fderiv ℝ (fun y => ∑ k ∈ s, t k y) =ᶠ[𝓝 x] fun y => ∑ k ∈ s, fderiv ℝ (t k) y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact fderiv_fun_sum fun k hk => hd k hk y hy
  constructor
  · rw [fderiv_fun_sum fun k hk => hd k hk x hx]
    exact norm_sum_le s (fun k => fderiv ℝ (t k) x)
  · rw [hev.fderiv_eq, fderiv_fun_sum hdd]
    exact norm_sum_le s (fun k => fderiv ℝ (fderiv ℝ (t k)) x)

end lin

end HRS.MS.S82W
