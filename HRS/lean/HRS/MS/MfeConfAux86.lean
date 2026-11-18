import HRS.MS.MfeConfAux85

/-!
# S.B.1, packet F8 (part 18): the divergence of `u` and the source field `wψ1`

* `sb1_lv_divu_eq`: `div u = ∑_j [θ (h ∂_j∂_jh - (∂_jh)²)/h² + cv(∂_j∂_jk) h + ∂_j∂_jV]` (all at one density, `x`-derivatives);
* `sb1_lv_w`: `wψ1 = ∂_sψ = -(θ A(ρ_s)/ρ_s + Ġ)`.
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d : ℕ}

theorem sb1_lv_hasFDerivAt_quot {c h : Euc d → ℝ} {c' h' : Euc d →L[ℝ] ℝ} {x : Euc d} (hc : HasFDerivAt c c' x)
    (hh : HasFDerivAt h h' x) (hx : h x ≠ 0) :
    HasFDerivAt (fun y => c y / h y) ((h x)⁻¹ • c' - (c x / (h x) ^ 2) • h') x := by
  have hi : HasFDerivAt (fun y => (h y)⁻¹) (-((h x) ^ 2)⁻¹ • h') x :=
    (hasDerivAt_inv hx).comp_hasFDerivAt x hh
  have := hc.fun_mul hi
  refine (show HasFDerivAt (fun y => c y / h y) _ x from by simpa [div_eq_mul_inv] using this).congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply]
  field_simp
  ring

section Dens

variable {D : Whole.WholeDyn d} {s r₀ : ℝ} {k : Euc d → ℝ} {h : Euc d → ℝ} {Cρ M1 Lg L2 C B : ℝ}

theorem sb1_lv_divu_eq (P : Sb1Pot D.V B) (hk4 : IsP4Kernel d D.s r₀ k) (hd : 1 ≤ d) (hs0 : 0 ≤ D.s)
    (hsd : D.s < d) (hR : Sb1KerR d k Lg) (hL : ∀ z, ‖fderiv ℝ k z‖ ≤ Lg)
    (hL2 : ∀ z, ‖fderiv ℝ (fderiv ℝ k) z‖ ≤ L2) (R : Sb1Rho h Cρ M1) (S : Sb1Slice d C h)
    (hpos : ∀ y, 0 < h y) (x : Euc d) :
    sb1divE (sb1_lv_u D k h) x = ∑ j, (D.invβ * ((h x * fderiv ℝ (fun y => fderiv ℝ h y (sb1e j)) x (sb1e j) -
      fderiv ℝ h x (sb1e j) ^ 2) / h x ^ 2) + sb1_lv_cv (sb1_lv_hjj k j) h x +
      fderiv ℝ (fun y => fderiv ℝ D.V y (sb1e j)) x (sb1e j)) := by
  have hh3 : ContDiff ℝ 3 h := S.decay.1
  have hhd : Differentiable ℝ h := hh3.differentiable (by norm_num)
  have hV : Differentiable ℝ D.V := P.c3.differentiable (by norm_num)
  have hx := (hpos x).ne'
  unfold sb1divE
  refine Finset.sum_congr rfl fun j _ => ?_
  have eu : (fun y => sb1_lv_u D k h y j) = fun y => D.invβ * (fderiv ℝ h y (sb1e j) / h y) +
      sb1_lv_a k h j y + fderiv ℝ D.V y (sb1e j) :=
    funext fun y => sb1_lv_u_apply hk4 hd hs0 hsd hR R hpos hhd hV y j
  have hc : HasFDerivAt (fun y => fderiv ℝ h y (sb1e j)) (fderiv ℝ (fun y => fderiv ℝ h y (sb1e j)) x) x :=
    ((((hh3.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const).differentiable (by norm_num)) x).hasFDerivAt
  have hq := sb1_lv_hasFDerivAt_quot hc (hhd x).hasFDerivAt hx
  have ha : HasFDerivAt (sb1_lv_a k h j) (fderiv ℝ (sb1_lv_a k h j) x) x :=
    (sb1_lv_dG_hasFDerivAt hk4 hd hs0 hsd hR hL hL2 R j x).differentiableAt.hasFDerivAt
  have hdV : HasFDerivAt (fun y => fderiv ℝ D.V y (sb1e j)) (fderiv ℝ (fun y => fderiv ℝ D.V y (sb1e j)) x) x :=
    (((sb1_dV_k_contDiff P j).differentiable (by norm_num)) x).hasFDerivAt
  have hU : HasFDerivAt (fun y => D.invβ * (fderiv ℝ h y (sb1e j) / h y) + sb1_lv_a k h j y +
      fderiv ℝ D.V y (sb1e j)) (D.invβ • ((h x)⁻¹ • fderiv ℝ (fun y => fderiv ℝ h y (sb1e j)) x -
        (fderiv ℝ h x (sb1e j) / (h x) ^ 2) • fderiv ℝ h x) + fderiv ℝ (sb1_lv_a k h j) x +
        fderiv ℝ (fun y => fderiv ℝ D.V y (sb1e j)) x) x :=
    ((hq.const_mul D.invβ).add ha).add hdV
  rw [eu]
  have hfin : fderiv ℝ (fun y => D.invβ * (fderiv ℝ h y (sb1e j) / h y) + sb1_lv_a k h j y +
      fderiv ℝ D.V y (sb1e j)) x (sb1e j) = D.invβ * ((h x)⁻¹ * fderiv ℝ (fun y => fderiv ℝ h y (sb1e j)) x (sb1e j)
        - fderiv ℝ h x (sb1e j) / h x ^ 2 * fderiv ℝ h x (sb1e j)) + fderiv ℝ (sb1_lv_a k h j) x (sb1e j) +
        fderiv ℝ (fun y => fderiv ℝ D.V y (sb1e j)) x (sb1e j) := by
    rw [hU.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.sub_apply]
  rw [hfin]
  have := sb1_lv_hjj_eq hk4 hd hs0 hsd hR hL hL2 R j x
  have e2 : (fun x => fderiv ℝ (sb1G k h) x (sb1e j)) = sb1_lv_a k h j := rfl
  rw [e2] at this
  rw [this]
  field_simp

end Dens

end HRS.MS.MfeConf
