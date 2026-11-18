import HRS.MS.MfeConfAux76

/-!
# S.B.1, packet F8 (part 9): the algebra of the source (MOV-A)

At one density `h`, with `u = -∇ψ`, `v = mfeTransportW D h` (exact transport), `e = ∇G - F`:

* `sb1_lv_alg`: the pure algebra `θ div u - ⟨u,∇V⟩ + |u|² + w = θ div e + ⟨e, u - ∇V⟩ + (⟨∇G, v⟩ - Ġ)` for `w = -(θ A/h + Ġ)`;
* `sb1_lv_div_sub`: `div u - div v = ∑_j ∂_j∂_jG - ∑_j ∂_jF_j`;
* `sb1_lv_A_over`: `θ A(h)/h = ∑_j (θ ∂_jh/h) v_j + θ div v`.
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d : ℕ}

theorem sb1_lv_alg {ι : Type*} [Fintype ι] (θ divu divv dive Aover gd : ℝ) (c a F u v dV : ι → ℝ)
    (hu : ∀ j, u j = c j + a j + dV j) (hv : ∀ j, v j = c j + F j + dV j) (hdiv : divu = divv + dive)
    (hA : θ * Aover = ∑ j, c j * v j + θ * divv) :
    θ * divu - ∑ j, u j * dV j + ∑ j, u j ^ 2 + (-(θ * Aover + gd)) =
      θ * dive + ∑ j, (a j - F j) * (u j - dV j) + (∑ j, a j * v j - gd) := by
  have term : ∀ j, u j ^ 2 - u j * dV j - c j * v j = (a j - F j) * (u j - dV j) + a j * v j := by
    intro j; rw [hu j, hv j]; ring
  have hs : ∑ j, (u j ^ 2 - u j * dV j - c j * v j) = ∑ j, ((a j - F j) * (u j - dV j) + a j * v j) :=
    Finset.sum_congr rfl fun j _ => term j
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hs
  rw [hdiv]
  have : θ * (divv + dive) - ∑ j, u j * dV j + ∑ j, u j ^ 2 + (-(θ * Aover + gd)) =
      θ * dive + (∑ j, u j ^ 2 - ∑ j, u j * dV j - ∑ j, c j * v j) - gd := by
    rw [mul_add]; linarith
  rw [this, hs]; ring

section Dens

variable {D : Whole.WholeDyn d} {s r₀ : ℝ} {k : Euc d → ℝ} {h : Euc d → ℝ} {Cρ M1 Lg L2 C B : ℝ}

theorem sb1_lv_div_sub (P : Sb1Pot D.V B) (hk4 : IsP4Kernel d D.s r₀ k) (hd : 1 ≤ d) (hs0 : 0 ≤ D.s)
    (hsd : D.s < d) (hR : Sb1KerR d k Lg) (hL : ∀ z, ‖fderiv ℝ k z‖ ≤ Lg)
    (hL2 : ∀ z, ‖fderiv ℝ (fderiv ℝ k) z‖ ≤ L2) (R : Sb1Rho h Cρ M1) (S : Sb1Slice d C h)
    (hpos : ∀ y, 0 < h y) (x : Euc d) :
    sb1divE (sb1_lv_u D k h) x - sb1divE (Whole.mfeTransportW D h) x =
      ∑ j, sb1_lv_cv (sb1_lv_hjj k j) h x - ∑ j, fderiv ℝ (sb1F d D.s h j) x (sb1e j) := by
  have hh3 : ContDiff ℝ 3 h := S.decay.1
  have hhd : Differentiable ℝ h := hh3.differentiable (by norm_num)
  have hV : Differentiable ℝ D.V := (P.c3.differentiable (by norm_num))
  have c1 : ∀ j : Fin d, ContDiff ℝ 1 (fun x => fderiv ℝ h x (sb1e j)) := fun j =>
    ((hh3.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const).of_le (by norm_num)
  have c0 : ContDiff ℝ 1 h := hh3.of_le (by norm_num)
  have dc : ∀ j : Fin d, DifferentiableAt ℝ (fun x => D.invβ * (fderiv ℝ h x (sb1e j) / h x)) x := fun j =>
    ((contDiff_const.mul ((c1 j).div c0 (fun x => (hpos x).ne'))).differentiable (by norm_num)) x
  have da : ∀ j : Fin d, DifferentiableAt ℝ (sb1_lv_a k h j) x := fun j =>
    ((sb1_lv_a_contDiff hk4 hd hs0 hsd hR hL hL2 R j).differentiable (by norm_num)) x
  have dF : ∀ j : Fin d, DifferentiableAt ℝ (sb1F d D.s h j) x := fun j =>
    ((sb1F_contDiff hd hs0 hsd S j).1.differentiable (by norm_num)) x
  have dV : ∀ j : Fin d, DifferentiableAt ℝ (fun x => fderiv ℝ D.V x (sb1e j)) x := fun j =>
    (((sb1_dV_k_contDiff P j).differentiable (by norm_num))) x
  have e1 : ∀ j : Fin d, fderiv ℝ (fun y => sb1_lv_u D k h y j) x (sb1e j) -
      fderiv ℝ (fun y => Whole.mfeTransportW D h y j) x (sb1e j) =
      sb1_lv_cv (sb1_lv_hjj k j) h x - fderiv ℝ (sb1F d D.s h j) x (sb1e j) := by
    intro j
    have eu : (fun y => sb1_lv_u D k h y j) = fun y => D.invβ * (fderiv ℝ h y (sb1e j) / h y) +
        sb1_lv_a k h j y + fderiv ℝ D.V y (sb1e j) :=
      funext fun y => sb1_lv_u_apply hk4 hd hs0 hsd hR R hpos hhd hV y j
    have ev : (fun y => Whole.mfeTransportW D h y j) = fun y => D.invβ * (fderiv ℝ h y (sb1e j) / h y) +
        sb1F d D.s h j y + fderiv ℝ D.V y (sb1e j) :=
      funext fun y => sb1_lv_v_apply hd hs0 hsd S hpos y j
    have hU : HasFDerivAt (fun y => D.invβ * (fderiv ℝ h y (sb1e j) / h y) + sb1_lv_a k h j y +
        fderiv ℝ D.V y (sb1e j)) (fderiv ℝ (fun x => D.invβ * (fderiv ℝ h x (sb1e j) / h x)) x +
        fderiv ℝ (sb1_lv_a k h j) x + fderiv ℝ (fun x => fderiv ℝ D.V x (sb1e j)) x) x :=
      ((dc j).hasFDerivAt.add (da j).hasFDerivAt).add (dV j).hasFDerivAt
    have hW : HasFDerivAt (fun y => D.invβ * (fderiv ℝ h y (sb1e j) / h y) + sb1F d D.s h j y +
        fderiv ℝ D.V y (sb1e j)) (fderiv ℝ (fun x => D.invβ * (fderiv ℝ h x (sb1e j) / h x)) x +
        fderiv ℝ (sb1F d D.s h j) x + fderiv ℝ (fun x => fderiv ℝ D.V x (sb1e j)) x) x :=
      ((dc j).hasFDerivAt.add (dF j).hasFDerivAt).add (dV j).hasFDerivAt
    rw [eu, ev, hU.fderiv, hW.fderiv]
    simp only [ContinuousLinearMap.add_apply]
    have := sb1_lv_hjj_eq hk4 hd hs0 hsd hR hL hL2 R j x
    have e2 : (fun x => fderiv ℝ (sb1G k h) x (sb1e j)) = sb1_lv_a k h j := rfl
    rw [e2] at this
    rw [this]; ring
  unfold sb1divE
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => e1 j

theorem sb1_lv_A_over (P : Sb1Pot D.V B) (hd : 1 ≤ d) (hs0 : 0 ≤ D.s) (hsd : D.s < d) (S : Sb1Slice d C h)
    (hpos : ∀ y, 0 < h y) (x : Euc d) :
    D.invβ * (sb1A D h x / h x) = ∑ j, D.invβ * (fderiv ℝ h x (sb1e j) / h x) * Whole.mfeTransportW D h x j +
      D.invβ * sb1divE (Whole.mfeTransportW D h) x := by
  have hh3 : ContDiff ℝ 3 h := S.decay.1
  have hhd : Differentiable ℝ h := hh3.differentiable (by norm_num)
  have hvc := sb1_lv_v_contDiff P hd hs0 hsd S hpos
  have hvj : ∀ j : Fin d, DifferentiableAt ℝ (fun y => Whole.mfeTransportW D h y j) x := fun j =>
    ((contDiff_euclidean.1 hvc j).differentiable (by norm_num)) x
  rw [sb1A_eq_div D P hd hs0 hsd S hpos x]
  have e : ∀ j : Fin d, fderiv ℝ (fun y => h y * Whole.mfeTransportW D h y j) x (sb1e j) =
      fderiv ℝ h x (sb1e j) * Whole.mfeTransportW D h x j +
        h x * fderiv ℝ (fun y => Whole.mfeTransportW D h y j) x (sb1e j) := by
    intro j
    rw [fderiv_fun_mul (hhd x) (hvj j)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  simp only [e, Finset.sum_add_distrib]
  unfold sb1divE
  have hx := (hpos x).ne'
  have h1 : (∑ j : Fin d, fderiv ℝ h x (sb1e j) * Whole.mfeTransportW D h x j) / h x =
      ∑ j : Fin d, (fderiv ℝ h x (sb1e j) / h x) * Whole.mfeTransportW D h x j := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : (∑ j : Fin d, h x * fderiv ℝ (fun y => Whole.mfeTransportW D h y j) x (sb1e j)) / h x =
      ∑ j : Fin d, fderiv ℝ (fun y => Whole.mfeTransportW D h y j) x (sb1e j) := by
    rw [← Finset.mul_sum]; field_simp
  rw [add_div, h1, h2, mul_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

end Dens

end HRS.MS.MfeConf
