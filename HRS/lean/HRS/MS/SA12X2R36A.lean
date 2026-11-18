import HRS.MS.SA12Z3NearN7A

/-!
# S.A.12 R36 (SA12X2), part A: L1 (derivatives commute with the Riesz convolution) and L3 (product split)

`a ∂_jF = ∂_j(aF) - F ∂_j a` inside the Riesz convolution (used to move the top derivative onto `aF`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12

open HRS HRS.Whole

variable {d : ℕ}

/-- L1: tuple partials commute with the Riesz convolution (from `sa12z3_pd_conv`). -/
theorem sa12x2_conv_pd {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (n : ℕ) (Q : Euc d → ℝ)
    (hQ : ContDiff ℝ n Q) (hQc : HasCompactSupport Q) (idx : Fin n → Fin d) (x : Euc d) :
    partialDeriv idx (HRS.Whole.convFun (rieszKernel d s) Q) x =
      HRS.Whole.convFun (rieszKernel d s) (partialDeriv idx Q) x :=
  HRS.MH.AdjointRd.Phase2SA12Near.sa12z3_pd_conv hs0 hsd n Q hQ hQc idx x

/-- The first partial of a product. -/
theorem sa12x2_pd_mul1 {a F : Euc d → ℝ} (ha : Differentiable ℝ a) (hF : Differentiable ℝ F)
    (j : Fin d) (y : Euc d) :
    partialDeriv (fun _ : Fin 1 => j) (fun z => a z * F z) y =
      a y * partialDeriv (fun _ : Fin 1 => j) F y + F y * partialDeriv (fun _ : Fin 1 => j) a y := by
  unfold partialDeriv
  rw [iteratedFDeriv_one_apply, iteratedFDeriv_one_apply, iteratedFDeriv_one_apply,
    fderiv_fun_mul (ha y) (hF y)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- L3: the Riesz convolution splits `a ∂_jF = ∂_j(aF) - F ∂_j a` (under integrability). -/
theorem sa12x2_conv_split {a F : Euc d → ℝ} (K : Euc d → ℝ) (ha : Differentiable ℝ a)
    (hF : Differentiable ℝ F) (j : Fin d) (x : Euc d)
    (hI1 : Integrable (fun y => K (x - y) * partialDeriv (fun _ : Fin 1 => j) (fun z => a z * F z) y))
    (hI2 : Integrable (fun y => K (x - y) * (F y * partialDeriv (fun _ : Fin 1 => j) a y))) :
    ∫ y, K (x - y) * (a y * partialDeriv (fun _ : Fin 1 => j) F y) =
      (∫ y, K (x - y) * partialDeriv (fun _ : Fin 1 => j) (fun z => a z * F z) y) -
        ∫ y, K (x - y) * (F y * partialDeriv (fun _ : Fin 1 => j) a y) := by
  rw [← integral_sub hI1 hI2]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [sa12x2_pd_mul1 ha hF j y]
  ring

end HRS.MH.AdjointRd.Phase2SA12
