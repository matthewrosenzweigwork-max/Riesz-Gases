import HRS.MS.SA12X3W5

/-!
# S.A.12 N1/N2 (SA12X3), part A: the nonlocal test function through convolutions with the test function derivatives
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12x3n_convFun_contDiff {K : Euc d → ℝ} (hK : LocallyIntegrable K volume) {n : ℕ} {Q : Euc d → ℝ}
    (hQ : ContDiff ℝ n Q) (hQc : HasCompactSupport Q) : ContDiff ℝ n (HRS.Whole.convFun K Q) := by
  have hfun : HRS.Whole.convFun K Q = K ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] Q := by
    funext x'
    have h := integral_sub_left_eq_self (μ := volume) (fun t => K t * Q (x' - t)) x'
    simp only [sub_sub_cancel] at h
    simpa [convolution_def, HRS.Whole.convFun] using h
  rw [hfun]
  exact hQc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hK hQ

theorem sa12x3n_nl_formula {K : Euc d → ℝ} (hK : LocallyIntegrable K volume) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) {μ : Euc d → ℝ} (hμ : ContDiff ℝ 1 μ) (i j : Fin d)
    (x : Euc d) :
    partialDeriv (fun _ : Fin 1 => j) (fun y => μ y * gradient (HRS.Whole.convFun K ψ) y i) x =
      fderiv ℝ μ x (EuclideanSpace.single j (1 : ℝ)) * HRS.Whole.convFun K (D1 i ψ) x +
        μ x * HRS.Whole.convFun K (D1 j (D1 i ψ)) x := by
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by simp)
  have hgi : ∀ y, gradient (HRS.Whole.convFun K ψ) y i = HRS.Whole.convFun K (D1 i ψ) y := by
    intro y
    rw [HRS.Whole.AppendixA.q09_gradient_apply]
    exact convFun_D1 hK (hψ.of_le (by simp)) hψc i y
  have hD1c : HasCompactSupport (D1 i ψ) := D1_supp hψc i
  have hG : ContDiff ℝ 1 (HRS.Whole.convFun K (D1 i ψ)) :=
    sa12x3n_convFun_contDiff hK (D1_contDiff hψ2 i) hD1c
  have hGd : DifferentiableAt ℝ (HRS.Whole.convFun K (D1 i ψ)) x := (hG.differentiable one_ne_zero) x
  have hμd : DifferentiableAt ℝ μ x := (hμ.differentiable one_ne_zero) x
  have h1 : fderiv ℝ (HRS.Whole.convFun K (D1 i ψ)) x (EuclideanSpace.single j (1 : ℝ)) =
      HRS.Whole.convFun K (D1 j (D1 i ψ)) x :=
    convFun_D1 hK (D1_contDiff hψ2 i) hD1c j x
  simp only [hgi]
  rw [HRS.MH.AdjointRd.Phase2SA12Near.sa12x3_pd_one, fderiv_fun_mul hμd hGd]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [h1]
  ring

end HRS.MH.AdjointRd.Phase2SA12Construction
