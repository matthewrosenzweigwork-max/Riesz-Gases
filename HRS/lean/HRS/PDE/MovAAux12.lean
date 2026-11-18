import HRS.PDE.MovAAux11

/-!
# MOVA Aux12: Lipschitz estimate for `u^M - u`, continuity facts, and the centred identity
`S^M - (-βN(C^M - E_Q C^M)) = ∑ k(x_i) - E_Q ∑ k(x_i)`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem mova_isLipschitzVF_mono {L L' : ℝ} (h : L ≤ L') {v : Torus d → Euc d}
    (hv : IsLipschitzVF L v) : IsLipschitzVF L' v := fun x y =>
  (hv x y).trans (mul_le_mul_of_nonneg_right h (KernelGrad.tdist_nonneg x y))

theorem mova_uReg_sub_apply (D : DynData d) (M : ℝ) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 1 ρ)
    (j : Fin d) (x : Torus d) :
    (movT_uReg D M ρ x - mfeTransport D ρ x).ofLp j =
      convFun (mova_kM D M) (Torus.partialDeriv j ρ) x := by
  have hgi := mova_integrable_periodicRiesz (b15_one_le_d D) D.hs0 D.hsd
  have hgMi := mova_integrable_gReg D M
  have hdρc : Continuous (Torus.partialDeriv j ρ) := mova_continuous_partialDeriv hρ j
  have h3 : convFun (mova_kM D M) (Torus.partialDeriv j ρ) x =
      convFun (b15c_gReg d D.s M) (Torus.partialDeriv j ρ) x -
        convFun (periodicRiesz d D.s) (Torus.partialDeriv j ρ) x :=
    mova_convFun_sub_left hgMi hgi hdρc x
  rw [h3, ← mova_partialDeriv_convFun hgMi hρ j x, ← mova_convGradConv_eq (b15_one_le_d D) D.hs0
    D.hsd hρ j x]
  unfold movT_uReg mfeTransport
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mova_grad_apply]
  ring

theorem mova_lip_uReg (D : DynData d) (M : ℝ) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 2 ρ) {Λ L : ℝ}
    (hΛ : Torus.cbNorm 2 ρ ≤ Λ) (hL : IsLipschitzVF L (mfeTransport D ρ)) :
    IsLipschitzVF (L + d * (Λ * mova_L1 (mova_kM D M))) (movT_uReg D M ρ) := by
  have hρ1 := mova_isCk_one_of_two hρ
  have hki := mova_integrable_kM D M
  intro x y
  have hdρc : ∀ j, Continuous (Torus.partialDeriv j ρ) := fun j => mova_continuous_partialDeriv hρ1 j
  have hj : ∀ j : Fin d, |(movT_uReg D M ρ x - mfeTransport D ρ x - (movT_uReg D M ρ y -
      mfeTransport D ρ y)).ofLp j| ≤ mova_L1 (mova_kM D M) * Λ * KernelGrad.tdist x y := by
    intro j
    rw [PiLp.sub_apply, mova_uReg_sub_apply D M hρ1, mova_uReg_sub_apply D M hρ1]
    have hlip : KernelGrad.IsLipschitz Λ (Torus.partialDeriv j ρ) := fun a b =>
      (mova_isLipschitz_partialDeriv hρ j a b).trans
        (mul_le_mul_of_nonneg_right hΛ (KernelGrad.tdist_nonneg a b))
    exact mova_convFun_lipschitz hki (hdρc j) hlip x y
  have hsum : ‖movT_uReg D M ρ x - mfeTransport D ρ x - (movT_uReg D M ρ y - mfeTransport D ρ y)‖ ≤
      d * (Λ * mova_L1 (mova_kM D M)) * KernelGrad.tdist x y := by
    refine (mova_norm_le_sum _).trans ?_
    refine (Finset.sum_le_sum fun j _ => hj j).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_of_eq (by ring)
  have e : movT_uReg D M ρ x - movT_uReg D M ρ y = (mfeTransport D ρ x - mfeTransport D ρ y) +
      (movT_uReg D M ρ x - mfeTransport D ρ x - (movT_uReg D M ρ y - mfeTransport D ρ y)) := by
    abel
  rw [e]
  calc _ ≤ ‖mfeTransport D ρ x - mfeTransport D ρ y‖ + ‖movT_uReg D M ρ x - mfeTransport D ρ x -
        (movT_uReg D M ρ y - mfeTransport D ρ y)‖ := norm_add_le _ _
    _ ≤ L * KernelGrad.tdist x y + d * (Λ * mova_L1 (mova_kM D M)) * KernelGrad.tdist x y :=
        add_le_add (hL x y) hsum
    _ = _ := by ring

end HRS
