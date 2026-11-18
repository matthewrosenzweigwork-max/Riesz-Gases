import HRS.MS.MfeConfAux74

/-!
# S.B.1, packet F8 (part 7): the tilt `ψ` and the field `u = -∇ψ` of the level-`k` reference at one density

For a density `h > 0` (a slice), a truncated kernel `k` and the potential `V`:
`sb1_lv_psi D k h x = -(θ log h(x) + G(x) + V(x))` (`G = k * h`, `θ = D.invβ`), `sb1_lv_u D k h = -∇ψ`, with components
`u_j = θ ∂_jh/h + ∂_jG + ∂_jV` (`sb1_lv_u_apply`) and the exact transport `v = mfeTransportW D h`,
`v_j = θ ∂_jh/h + F_j + ∂_jV` (`sb1_lv_v_apply`), so `u - v = ∇G - F`.
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d : ℕ}

/-- `ψ = -(θ log h + k*h + V)` -/
def sb1_lv_psi (D : Whole.WholeDyn d) (k : Euc d → ℝ) (h : Euc d → ℝ) (x : Euc d) : ℝ :=
  -(D.invβ * Real.log (h x) + sb1G k h x + D.V x)

/-- `u = -∇ψ` -/
def sb1_lv_u (D : Whole.WholeDyn d) (k : Euc d → ℝ) (h : Euc d → ℝ) (x : Euc d) : Euc d :=
  -gradient (sb1_lv_psi D k h) x

/-- `∂_j (k*h)` -/
def sb1_lv_a (k h : Euc d → ℝ) (j : Fin d) (x : Euc d) : ℝ := fderiv ℝ (sb1G k h) x (sb1e j)

section Dens

variable {D : Whole.WholeDyn d} {s r₀ : ℝ} {k : Euc d → ℝ} {h : Euc d → ℝ} {Cρ M1 Lg L2 : ℝ}

theorem sb1_lv_hasFDerivAt_psi (hk4 : IsP4Kernel d s r₀ k) (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    {Lg : ℝ} (hR : Sb1KerR d k Lg) (R : Sb1Rho h Cρ M1) (hpos : ∀ y, 0 < h y)
    (hhd : Differentiable ℝ h) (hV : Differentiable ℝ D.V) (x : Euc d) :
    HasFDerivAt (sb1_lv_psi D k h)
      (-(D.invβ • (h x)⁻¹ • fderiv ℝ h x + fderiv ℝ (sb1G k h) x + fderiv ℝ D.V x)) x := by
  have h1 : HasFDerivAt (fun y => Real.log (h y)) ((h x)⁻¹ • fderiv ℝ h x) x :=
    (hhd x).hasFDerivAt.log (hpos x).ne'
  have h2 := sb1_hasFDerivAt_G hd hs0 hsd (sb1KerU_of_p4 hs0 hk4) hR R x
  have h3 := ((h1.const_mul D.invβ).add h2).add (hV x).hasFDerivAt
  have h4 := h3.neg
  refine (show HasFDerivAt (sb1_lv_psi D k h) _ x from h4).congr_fderiv ?_
  rw [h2.fderiv]

theorem sb1_lv_psi_diff (hk4 : IsP4Kernel d s r₀ k) (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (hR : Sb1KerR d k Lg) (R : Sb1Rho h Cρ M1) (hpos : ∀ y, 0 < h y) (hhd : Differentiable ℝ h)
    (hV : Differentiable ℝ D.V) : Differentiable ℝ (sb1_lv_psi D k h) := fun x =>
  (sb1_lv_hasFDerivAt_psi hk4 hd hs0 hsd hR R hpos hhd hV x).differentiableAt

theorem sb1_lv_u_apply (hk4 : IsP4Kernel d s r₀ k) (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (hR : Sb1KerR d k Lg) (R : Sb1Rho h Cρ M1) (hpos : ∀ y, 0 < h y) (hhd : Differentiable ℝ h)
    (hV : Differentiable ℝ D.V) (x : Euc d) (j : Fin d) :
    sb1_lv_u D k h x j = D.invβ * (fderiv ℝ h x (sb1e j) / h x) + sb1_lv_a k h j x + fderiv ℝ D.V x (sb1e j) := by
  unfold sb1_lv_u
  rw [PiLp.neg_apply, sb1_grad_apply, (sb1_lv_hasFDerivAt_psi hk4 hd hs0 hsd hR R hpos hhd hV x).fderiv]
  unfold sb1_lv_a
  simp [div_eq_inv_mul]

theorem sb1_lv_v_apply (hd : 1 ≤ d) (hs0 : 0 ≤ D.s) (hsd : D.s < d) {C : ℝ}
    (S : Sb1Slice d C h) (hpos : ∀ y, 0 < h y) (x : Euc d) (j : Fin d) :
    Whole.mfeTransportW D h x j = D.invβ * (fderiv ℝ h x (sb1e j) / h x) + sb1F d D.s h j x +
      fderiv ℝ D.V x (sb1e j) := by
  have h1 := sb1_transport_apply D ((sb1_slice_facts S).1.differentiable (by norm_num)) hpos j x
  unfold sb1Flux at h1
  have hx := (hpos x).ne'
  field_simp
  linarith

end Dens

end HRS.MS.MfeConf
