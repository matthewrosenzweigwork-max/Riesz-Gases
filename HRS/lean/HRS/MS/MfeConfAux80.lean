import HRS.MS.MfeConfAux79

/-!
# S.B.1, packet F8 (part 12): the one-body part `Θ` of the source and its exact decomposition

`sb1_lv_Theta D k h gd x = θ div u - ⟨u,∇V⟩ + |u|² - (θ A(h)/h + gd)`  (`u = sb1_lv_u D k h`, `gd = Ġ(x)`), and
`sb1_lv_Theta_eq`:  `Θ = θ (∑_j ∂_j∂_jG - ∑_j ∂_jF_j) + ∑_j (∂_jG - F_j)(u_j - ∂_jV) + (∑_j ∂_jG v_j - gd)`
(the terms quadratic in the transport field cancel exactly).
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d : ℕ}

/-- the one-body part of the source -/
def sb1_lv_Theta (D : Whole.WholeDyn d) (k h : Euc d → ℝ) (gd : Euc d → ℝ) (x : Euc d) : ℝ :=
  D.invβ * sb1divE (sb1_lv_u D k h) x - inner ℝ (sb1_lv_u D k h x) (gradient D.V x) +
    ‖sb1_lv_u D k h x‖ ^ 2 + (-(D.invβ * (sb1A D h x / h x) + gd x))

section Dens

variable {D : Whole.WholeDyn d} {s r₀ : ℝ} {k : Euc d → ℝ} {h : Euc d → ℝ} {Cρ M1 Lg L2 C B : ℝ}

theorem sb1_lv_Theta_eq (P : Sb1Pot D.V B) (hk4 : IsP4Kernel d D.s r₀ k) (hd : 1 ≤ d) (hs0 : 0 ≤ D.s)
    (hsd : D.s < d) (hR : Sb1KerR d k Lg) (hL : ∀ z, ‖fderiv ℝ k z‖ ≤ Lg)
    (hL2 : ∀ z, ‖fderiv ℝ (fderiv ℝ k) z‖ ≤ L2) (R : Sb1Rho h Cρ M1) (S : Sb1Slice d C h)
    (hpos : ∀ y, 0 < h y) (gd : Euc d → ℝ) (x : Euc d) :
    sb1_lv_Theta D k h gd x =
      D.invβ * (∑ j, sb1_lv_cv (sb1_lv_hjj k j) h x - ∑ j, fderiv ℝ (sb1F d D.s h j) x (sb1e j)) +
        ∑ j, (sb1_lv_a k h j x - sb1F d D.s h j x) *
          (sb1_lv_u D k h x j - fderiv ℝ D.V x (sb1e j)) +
        (∑ j, sb1_lv_a k h j x * Whole.mfeTransportW D h x j - gd x) := by
  have hhd : Differentiable ℝ h := S.decay.1.differentiable (by norm_num)
  have hV : Differentiable ℝ D.V := P.c3.differentiable (by norm_num)
  have hA := sb1_lv_A_over P hd hs0 hsd S hpos x
  have hdiv := sb1_lv_div_sub P hk4 hd hs0 hsd hR hL hL2 R S hpos x
  unfold sb1_lv_Theta
  have hip : inner ℝ (sb1_lv_u D k h x) (gradient D.V x) = ∑ j, sb1_lv_u D k h x j * fderiv ℝ D.V x (sb1e j) := by
    rw [sb1_inner_eq_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [sb1_grad_apply]
  have hn : ‖sb1_lv_u D k h x‖ ^ 2 = ∑ j, sb1_lv_u D k h x j ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, sq_abs]
  rw [hip, hn]
  exact sb1_lv_alg D.invβ (sb1divE (sb1_lv_u D k h) x) (sb1divE (Whole.mfeTransportW D h) x)
    (∑ j, sb1_lv_cv (sb1_lv_hjj k j) h x - ∑ j, fderiv ℝ (sb1F d D.s h j) x (sb1e j))
    (sb1A D h x / h x) (gd x) (fun j => D.invβ * (fderiv ℝ h x (sb1e j) / h x)) (fun j => sb1_lv_a k h j x)
    (fun j => sb1F d D.s h j x) (fun j => sb1_lv_u D k h x j) (fun j => Whole.mfeTransportW D h x j)
    (fun j => fderiv ℝ D.V x (sb1e j))
    (fun j => sb1_lv_u_apply hk4 hd hs0 hsd hR R hpos hhd hV x j)
    (fun j => sb1_lv_v_apply hd hs0 hsd S hpos x j) (by linarith) hA

end Dens

end HRS.MS.MfeConf
