import HRS.MS.R26T8AP15q

/-!
# S8.2 T8A P15r: `Lop` of the centred kernel
`Q = r2CenterKernel mu R` satisfies `Q(x,y) = R(x,y) - r1(x) - r2(y) + c` with `r1(x) = ∫ R(x,.) dmu`, `r2(y) = ∫ R(.,y) dmu`;
for `C²` data `Lop Q(.,y)(x) = Lop R(.,y)(x) - Lop r1 (x)` and `Lop Q(x,.)(y) = Lop R(x,.)(y) - Lop r2 (y)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_Lop_sub_const (C : WholeCoeff d) (f g : Euc d → ℝ) (c : ℝ) (x : Euc d)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    r26t8a_Lop C (fun w => f w - g w + c) x = r26t8a_Lop C f x - r26t8a_Lop C g x := by
  unfold r26t8a_Lop
  have hfd : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hgd : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  have e1 : (fun w => f w - g w + c) = fun w => (f - g) w + c := rfl
  have hfun : fderiv ℝ (fun w => (f - g) w + c) = fderiv ℝ (f - g) := by
    funext w; exact fderiv_add_const c
  have hlap : Laplacian.laplacian (fun w => (f - g) w + c) = Laplacian.laplacian (f - g) := by
    rw [r26t8a_laplacian_basis, r26t8a_laplacian_basis, hfun]
  rw [e1, hlap, r26t8a_p15_inner_gradient, r26t8a_p15_inner_gradient, r26t8a_p15_inner_gradient, hfun,
    hf.laplacian_sub hg, fderiv_sub hfd hgd]
  simp only [sub_apply]
  ring

theorem r26t8a_centre_eq (mu : Measure (Euc d)) (R : Euc d → Euc d → ℝ) (x y : Euc d) :
    r2CenterKernel mu R x y = R x y - (∫ y', R x y' ∂mu) - (∫ x', R x' y ∂mu) +
      ∫ x', ∫ y', R x' y' ∂mu ∂mu := rfl

theorem r26t8a_Lop_centre_x (C : WholeCoeff d) (mu : Measure (Euc d)) (R : Euc d → Euc d → ℝ) (x y : Euc d)
    (hR : ContDiffAt ℝ 2 (fun w => R w y) x) (h1 : ContDiffAt ℝ 2 (fun w => ∫ y', R w y' ∂mu) x) :
    r26t8a_Lop C (fun w => r2CenterKernel mu R w y) x =
      r26t8a_Lop C (fun w => R w y) x - r26t8a_Lop C (fun w => ∫ y', R w y' ∂mu) x := by
  have e : (fun w => r2CenterKernel mu R w y) = fun w => R w y - (∫ y', R w y' ∂mu) +
      (-(∫ x', R x' y ∂mu) + ∫ x', ∫ y', R x' y' ∂mu ∂mu) := by
    funext w; rw [r26t8a_centre_eq]; ring
  rw [e]
  exact r26t8a_Lop_sub_const C _ _ _ x hR h1

theorem r26t8a_Lop_centre_y (C : WholeCoeff d) (mu : Measure (Euc d)) (R : Euc d → Euc d → ℝ) (x y : Euc d)
    (hR : ContDiffAt ℝ 2 (R x) y) (h2 : ContDiffAt ℝ 2 (fun w => ∫ x', R x' w ∂mu) y) :
    r26t8a_Lop C (r2CenterKernel mu R x) y =
      r26t8a_Lop C (R x) y - r26t8a_Lop C (fun w => ∫ x', R x' w ∂mu) y := by
  have e : r2CenterKernel mu R x = fun w => R x w - (∫ x', R x' w ∂mu) +
      (-(∫ y', R x y' ∂mu) + ∫ x', ∫ y', R x' y' ∂mu ∂mu) := by
    funext w; rw [r26t8a_centre_eq]; ring
  rw [e]
  exact r26t8a_Lop_sub_const C _ _ _ y hR h2

end HRS.MS.R26T8A
