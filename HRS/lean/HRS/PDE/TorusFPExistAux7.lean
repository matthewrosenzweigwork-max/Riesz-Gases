import HRS.PDE.TorusFPExistAux6

/-!
# D1 existence, helper 7: continuity facts and narrow continuity of `t ↦ μ_t`
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS

variable {n : ℕ}

theorem d1_continuous_laplacian_euc {F : Euc n → ℝ} (hF : ContDiff ℝ 2 F) :
    Continuous (Laplacian.laplacian F) := by
  have hF1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (m := 1) (by norm_num)
  have hc2 : Continuous (fderiv ℝ (fderiv ℝ F)) := hF1.continuous_fderiv one_ne_zero
  have h := InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis F
    (EuclideanSpace.basisFun (Fin n) ℝ)
  rw [h]
  refine continuous_finset_sum _ fun i _ => ?_
  have : (fun y => iteratedFDeriv ℝ 2 F y ![EuclideanSpace.basisFun (Fin n) ℝ i,
      EuclideanSpace.basisFun (Fin n) ℝ i]) = fun y =>
      fderiv ℝ (fderiv ℝ F) y (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i) := by
    funext y; rw [iteratedFDeriv_two_apply]; simp
  simp only [this]
  exact (hc2.clm_apply continuous_const).clm_apply continuous_const

theorem d1_continuous_gradient_euc {F : Euc n → ℝ} (hF : ContDiff ℝ 1 F) :
    Continuous (gradient F) := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ (Euc n)).symm.continuous.comp (hF.continuous_fderiv one_ne_zero)


theorem d1_gen_continuous {κ : ℝ} {b : Torus n → Euc n} (hb : Continuous b) {φ : Torus n → ℝ}
    (hφ : Torus.IsCk 2 φ) : Continuous (d1_gen κ b φ) := by
  have hF : ContDiff ℝ 2 (Torus.lift φ) := d1_contDiff_of_isCk2 hφ le_rfl
  apply Torus.continuous_of_continuous_lift
  have e : Torus.lift (d1_gen κ b φ) = fun y =>
      κ * Laplacian.laplacian (Torus.lift φ) y + inner ℝ (b (Torus.mk y)) (gradient (Torus.lift φ) y) := by
    funext y
    simp only [Torus.lift, Function.comp_apply, d1_gen, laplacian_mk, grad_mk]
  rw [e]
  refine (continuous_const.mul (d1_continuous_laplacian_euc hF)).add ?_
  exact (hb.comp Torus.continuous_mk).inner
    (d1_continuous_gradient_euc (hF.of_le (by norm_num)))

theorem d1_gradDrift_continuous {U : Torus n → ℝ} (hU : Torus.IsSmooth U) :
    Continuous (d1_gradDrift U) := by
  have hF : ContDiff ℝ 1 (Torus.lift U) := by
    have : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift U) := hU
    exact this.of_le (by exact_mod_cast le_top)
  apply Torus.continuous_of_continuous_lift
  have e : Torus.lift (d1_gradDrift U) = fun y => -(gradient (Torus.lift U) y) := by
    funext y
    simp only [Torus.lift, Function.comp_apply, d1_gradDrift, grad_mk]
  rw [e]
  exact (d1_continuous_gradient_euc hF).neg

end HRS
