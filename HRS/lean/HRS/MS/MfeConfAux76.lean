import HRS.MS.MfeConfAux75

/-!
# S.B.1, packet F8 (part 8): `u = -∇ψ` is `C¹` and its divergence differs from that of the exact transport by `div(∇G - F)`
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d : ℕ}

section Dens

variable {D : Whole.WholeDyn d} {s r₀ : ℝ} {k : Euc d → ℝ} {h : Euc d → ℝ} {Cρ M1 Lg L2 C : ℝ}

theorem sb1_lv_a_contDiff (hk4 : IsP4Kernel d s r₀ k) (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (hR : Sb1KerR d k Lg) (hL : ∀ z, ‖fderiv ℝ k z‖ ≤ Lg) (hL2 : ∀ z, ‖fderiv ℝ (fderiv ℝ k) z‖ ≤ L2)
    (R : Sb1Rho h Cρ M1) (j : Fin d) : ContDiff ℝ 1 (sb1_lv_a k h j) := by
  refine contDiff_one_iff_fderiv.2 ⟨fun x => (sb1_lv_dG_hasFDerivAt hk4 hd hs0 hsd hR hL hL2 R j x).differentiableAt, ?_⟩
  have e : fderiv ℝ (sb1_lv_a k h j) = fun x => ∫ y, h y • fderiv ℝ (sb1_lv_dk k j) (x - y) :=
    funext fun x => (sb1_lv_dG_hasFDerivAt hk4 hd hs0 hsd hR hL hL2 R j x).fderiv
  rw [e]
  refine continuous_of_dominated (bound := fun y => L2 * |h y|) (fun x => ?_) (fun x => ?_) ?_ ?_
  · exact R.meas'.smul ((sb1_lv_dk_fderiv_cont hk4.smooth j).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Eventually.of_forall fun y => ?_
    rw [norm_smul, Real.norm_eq_abs]
    have := mul_le_mul_of_nonneg_left (sb1_lv_dk_fderiv_bound hk4.smooth hL2 j (x - y)) (abs_nonneg (h y))
    linarith [mul_comm L2 |h y|]
  · exact R.integrable.abs.const_mul L2
  · refine Eventually.of_forall fun y => ?_
    exact (continuous_const : Continuous fun _ : Euc d => h y).smul ((sb1_lv_dk_fderiv_cont hk4.smooth j).comp (continuous_id.sub continuous_const))

theorem sb1_lv_u_contDiff {B : ℝ} (P : Sb1Pot D.V B) (hk4 : IsP4Kernel d s r₀ k) (hd : 1 ≤ d) (hs0 : 0 ≤ s)
    (hsd : s < d) (hR : Sb1KerR d k Lg) (hL : ∀ z, ‖fderiv ℝ k z‖ ≤ Lg)
    (hL2 : ∀ z, ‖fderiv ℝ (fderiv ℝ k) z‖ ≤ L2) (R : Sb1Rho h Cρ M1) (S : Sb1Slice d C h)
    (hpos : ∀ y, 0 < h y) : ContDiff ℝ 1 (sb1_lv_u D k h) := by
  have hh3 : ContDiff ℝ 3 h := S.decay.1
  have hhd : Differentiable ℝ h := hh3.differentiable (by norm_num)
  have hV : Differentiable ℝ D.V := (P.c3.differentiable (by norm_num))
  refine contDiff_euclidean.2 fun j => ?_
  have e : (fun x => sb1_lv_u D k h x j) = fun x => D.invβ * (fderiv ℝ h x (sb1e j) / h x) +
      sb1_lv_a k h j x + fderiv ℝ D.V x (sb1e j) :=
    funext fun x => sb1_lv_u_apply hk4 hd hs0 hsd hR R hpos hhd hV x j
  rw [e]
  have c1 : ContDiff ℝ 1 (fun x => fderiv ℝ h x (sb1e j)) :=
    ((hh3.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const).of_le (by norm_num)
  have c0 : ContDiff ℝ 1 h := hh3.of_le (by norm_num)
  exact (contDiff_const.mul (c1.div c0 (fun x => (hpos x).ne'))).add (sb1_lv_a_contDiff hk4 hd hs0 hsd hR hL hL2 R j)
    |>.add ((sb1_dV_k_contDiff P j).of_le (by norm_num))

theorem sb1_lv_v_contDiff {B : ℝ} (P : Sb1Pot D.V B) (hd : 1 ≤ d) (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    (S : Sb1Slice d C h) (hpos : ∀ y, 0 < h y) : ContDiff ℝ 1 (Whole.mfeTransportW D h) := by
  have hh3 : ContDiff ℝ 3 h := S.decay.1
  refine contDiff_euclidean.2 fun j => ?_
  have e : (fun x => Whole.mfeTransportW D h x j) = fun x => D.invβ * (fderiv ℝ h x (sb1e j) / h x) +
      sb1F d D.s h j x + fderiv ℝ D.V x (sb1e j) :=
    funext fun x => sb1_lv_v_apply hd hs0 hsd S hpos x j
  rw [e]
  have c1 : ContDiff ℝ 1 (fun x => fderiv ℝ h x (sb1e j)) :=
    ((hh3.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const).of_le (by norm_num)
  have c0 : ContDiff ℝ 1 h := hh3.of_le (by norm_num)
  exact (contDiff_const.mul (c1.div c0 (fun x => (hpos x).ne'))).add (sb1F_contDiff hd hs0 hsd S j).1
    |>.add ((sb1_dV_k_contDiff P j).of_le (by norm_num))

end Dens

end HRS.MS.MfeConf
