import HRS.MS.S81G_Sing
import HRS.MS.S81R_Euc
import HRS.MS.S81R_Cb

/-!
# S81R, packet R7b: the rescaled interaction potential `G₀`, its derivative bounds and its gradient

For a kernel `k`, `Hint k N x = (2N)⁻¹ ∑ᵢ ∑_{j≠i} k(xᵢ - xⱼ)` and `G₀(y) = -β Hint(Ψ y)` on `Euc (N*d)`, `Ψ = Φ⁻¹`, `Φ = √β enc`.
* `s81r_Bd_G0`: `s81r_Bd G₀` when `s81r_Bd k` (all derivatives of positive order bounded);
* `s81r_beta_Hs`: `β Hs(Ψ y) = (a/2)‖y‖² - G₀(y)` for the dynamics `Whole.quadraticGradientDyn d s a β`;
* `s81r_grad_G0`: `∇G₀(y) = a y + √β enc (b_k(Ψ y))`, so the Pois drift `-a y + ∇G₀(y)` is `√β enc (b_k(Ψ y))`.
-/

noncomputable section

open MeasureTheory
open HRS HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl HRS.MS.MfeConf

namespace HRS.MS.S81R

variable {d N : ℕ}

/-- the interaction part of the Hamiltonian -/
def s81r_Hint (k : Euc d → ℝ) (N : ℕ) (x : Whole.EucConfig d N) : ℝ :=
  (1 / (2 * (N : ℝ))) * p4k_pairSum k N x

/-- the rescaled interaction potential on `Euc (N*d)` -/
def s81r_G0 (β : ℝ) (k : Euc d → ℝ) (N : ℕ) (y : Euc (N * d)) : ℝ :=
  -β * s81r_Hint k N (s81r_Psi β d N y)

theorem s81r_Bd_G0 (β : ℝ) {k : Euc d → ℝ} (hk : s81r_Bd k) : s81r_Bd (s81r_G0 β k N) := by
  have hsum : s81r_Bd (fun y : Euc (N * d) => ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
      k (s81r_Psi β d N y i - s81r_Psi β d N y j)) := by
    refine s81r_Bd_sum _ _ fun i _ => s81r_Bd_sum _ _ fun j _ => ?_
    have := s81r_Bd_comp hk (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i) -
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) j)).comp (s81r_Psi β d N))
    simpa using this
  have h2 := s81r_Bd_smul (-β * (1 / (2 * (N : ℝ)))) hsum
  convert h2 using 1
  funext y
  simp only [s81r_G0, s81r_Hint, p4k_pairSum]
  ring

/-- decomposition of `β Hs ∘ Ψ` -/
theorem s81r_beta_Hs {s a β : ℝ} (hβ : 0 < β) (k : Euc d → ℝ) (y : Euc (N * d)) :
    β * sb1Hs (Whole.quadraticGradientDyn d s a β) k N (s81r_Psi β d N y) =
      a / 2 * ‖y‖ ^ 2 - s81r_G0 β k N y := by
  have h2 : ∑ i, ‖s81r_Psi β d N y i‖ ^ 2 = ‖y‖ ^ 2 / β := by
    rw [← s81r_enc_norm_sq, s81r_enc_Psi, norm_smul, mul_pow, Real.norm_eq_abs, abs_inv,
      abs_of_pos (Real.sqrt_pos.2 hβ), inv_pow, Real.sq_sqrt hβ.le]
    ring
  have h3 : ∑ i, Whole.confinement a (s81r_Psi β d N y i) = a / 2 * (‖y‖ ^ 2 / β) := by
    simp only [Whole.confinement]
    rw [← h2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hβ0 : β ≠ 0 := hβ.ne'
  simp only [sb1Hs, Whole.quadraticGradientDyn, s81r_G0, s81r_Hint]
  rw [h3]
  field_simp
  ring

/-- gradient of `G₀` -/
theorem s81r_grad_G0 {s a β : ℝ} (hβ : 0 < β) {r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k)
    {B0 : ℝ} (P : Sb1Pot (Whole.confinement a : Euc d → ℝ) B0) (y : Euc (N * d)) :
    gradient (s81r_G0 β k N) y =
      a • y + Real.sqrt β • s81r_encFun (sb1DriftM (Whole.quadraticGradientDyn d s a β) k N
        (s81r_Psi β d N y)) := by
  set D := Whole.quadraticGradientDyn d s a β with hD
  have hG : s81r_G0 β k N = fun y => a / 2 * ‖y‖ ^ 2 - β * sb1Hs D k N (s81r_Psi β d N y) := by
    funext y'
    rw [s81r_beta_Hs hβ k y']
    ring
  have hH := sb1_hasFDerivAt_Hs' D hk P (N := N) (s81r_Psi β d N y)
  have hΨ : HasFDerivAt (fun y' => s81r_Psi β d N y') (s81r_Psi β d N) y :=
    (s81r_Psi β d N).hasFDerivAt
  have h2 : HasFDerivAt (fun y' => sb1Hs D k N (s81r_Psi β d N y'))
      ((-(p4InnerL (sb1DriftM D k N (s81r_Psi β d N y)))).comp (s81r_Psi β d N)) y :=
    hH.comp y hΨ
  have h1 : HasFDerivAt (fun y' : Euc (N * d) => a / 2 * ‖y'‖ ^ 2) ((a / 2) • (2 • innerSL ℝ y)) y :=
    ((hasStrictFDerivAt_norm_sq y).hasFDerivAt).const_mul (a / 2)
  have h3 := h1.sub (h2.const_mul β)
  have hG0 : HasFDerivAt (s81r_G0 β k N) ((a / 2) • (2 • innerSL ℝ y) -
      β • ((-(p4InnerL (sb1DriftM D k N (s81r_Psi β d N y)))).comp (s81r_Psi β d N))) y := by
    rw [hG]
    exact h3
  refine ext_inner_right ℝ fun v => ?_
  rw [p4k_inner_grad, hG0.fderiv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, innerSL_apply_apply, smul_eq_mul,
    nsmul_eq_mul]
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, p4k_p4InnerL_apply,
    ← s81r_enc_inner, s81r_enc_Psi, real_inner_smul_right]
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hss : Real.sqrt β * Real.sqrt β = β := Real.mul_self_sqrt hβ.le
  have e : β * (Real.sqrt β)⁻¹ = Real.sqrt β := by
    rw [mul_inv_eq_iff_eq_mul₀ hs.ne', hss]
  push_cast
  linear_combination (inner ℝ (s81r_encFun (sb1DriftM D k N (s81r_Psi β d N y))) v) * e

end HRS.MS.S81R
