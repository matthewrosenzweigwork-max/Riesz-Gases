/-
# HRS.Equilibrium.Q84dAuxU — packet Q84d: size bounds for `∂_{x_k}ψ`, `∂²_{x_k}ψ`, `∇g`, `∇V`
-/
import HRS.Equilibrium.Q84dAuxT

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem q84d_comp_le_norm (v : Euc d) (k : Fin d) : |v k| ≤ ‖v‖ := by
  have := PiLp.norm_apply_le v k
  simpa [Real.norm_eq_abs] using this

theorem q84d_rpow_one_sub_le {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (s : ℝ) :
    r ^ (1 - s) ≤ r ^ (-s) := by
  exact Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)

/-- `|∂_{x_k}ψ(x,y)| ≤ K w(x,y)`. -/
theorem q84d_gK_bound {ψ : Torus d → Torus d → ℝ} {K : ℝ} (hψ : PsiSize s K ψ) {x y : Torus d}
    (hxy : x ≠ y) (k : Fin d) : |gK ψ k x y| ≤ K * wEnv s x y := by
  have hK : 0 ≤ K := Q84a.q84a_K_nonneg hψ hxy
  have h1 := q84d_grad_comp hψ.smooth hxy k
  have h2 := Q84a.q84a_grad_norm hψ hxy
  have hr := PairCorrAux.rTrunc_pos hxy
  have hr1 := PairCorrAux.rTrunc_le_one x y
  have h3 := q84d_rpow_one_sub_le hr hr1 s
  have h4 : ‖gradFst ψ x y‖ ≤ K * wEnv s x y := by
    refine h2.trans (mul_le_mul_of_nonneg_left ?_ hK)
    unfold wEnv; linarith
  have h5 := q84d_comp_le_norm (gradFst ψ x y) k
  have h6 : gradFst ψ x y = Torus.grad (fun z => ψ z y) x := rfl
  rw [← h1, ← h6] at *
  exact h5.trans h4

/-- `|∂²_{x_k}ψ(x,y)| ≤ K w(x,y)`. -/
theorem q84d_hK_bound {ψ : Torus d → Torus d → ℝ} {K : ℝ} (hψ : PsiSize s K ψ) {x y : Torus d}
    (hxy : x ≠ y) (k : Fin d) : |hK ψ k x y| ≤ K * wEnv s x y := by
  have hp := q84d_mem_offDiag hxy
  have hcd := q84d_contDiffAt_lift2 hψ.smooth hp
  have hdiff : DifferentiableAt ℝ (fderiv ℝ (lift2 ψ)) (Torus.rep x, Torus.rep y) :=
    (hcd.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  set v : Euc d × Euc d := (EuclideanSpace.single k 1, 0) with hv
  have e : hK ψ k x y = fderiv ℝ (fderiv ℝ (lift2 ψ)) (Torus.rep x, Torus.rep y) v v := by
    unfold hK
    rw [fderiv_clm_apply hdiff (differentiableAt_const v)]
    simp
    rfl
  have e2 : fderiv ℝ (fderiv ℝ (lift2 ψ)) (Torus.rep x, Torus.rep y) v v =
      iteratedFDeriv ℝ 2 (lift2 ψ) (Torus.rep x, Torus.rep y) ![v, v] := by
    rw [iteratedFDeriv_two_apply]; rfl
  have hnorm : ‖v‖ ≤ 1 := by
    rw [hv, Prod.norm_def]
    simp
  have h1 := (iteratedFDeriv ℝ 2 (lift2 ψ) (Torus.rep x, Torus.rep y)).le_opNorm ![v, v]
  have h2 : ∏ i, ‖(![v, v] : Fin 2 → Euc d × Euc d) i‖ ≤ 1 := by
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith [norm_nonneg v]
  have h3 := hψ.hess _ hp
  rw [Torus.mk_rep, Torus.mk_rep] at h3
  have hK : 0 ≤ K := Q84a.q84a_K_nonneg hψ hxy
  rw [e, e2, ← Real.norm_eq_abs]
  calc ‖iteratedFDeriv ℝ 2 (lift2 ψ) (Torus.rep x, Torus.rep y) ![v, v]‖
      ≤ ‖iteratedFDeriv ℝ 2 (lift2 ψ) (Torus.rep x, Torus.rep y)‖ *
          ∏ i, ‖(![v, v] : Fin 2 → Euc d × Euc d) i‖ := h1
    _ ≤ ‖iteratedFDeriv ℝ 2 (lift2 ψ) (Torus.rep x, Torus.rep y)‖ * 1 :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ ≤ K * (1 + rTrunc x y ^ (-s)) := by rw [mul_one]; exact h3

end HRS.Q84d

end
