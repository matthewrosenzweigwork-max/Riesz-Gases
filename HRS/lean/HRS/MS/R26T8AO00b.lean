import HRS.MS.R26T8AO00a

/-!
# S8.2 observed-time layer, packet T8A.O00 (helper b): Lipschitz bound of the gradient

If `‖∂² f‖ ≤ A` everywhere and `f` is smooth, then `‖∇f x - ∇f y‖ ≤ A ‖x - y‖`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole

theorem r26t8a_o00b_grad_lip {d : ℕ} (f : Euc d → ℝ) (hf : ContDiff ℝ ∞ f) (A : ℝ)
    (h2 : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ A) (x y : Euc d) :
    ‖gradient f x - gradient f y‖ ≤ A * ‖x - y‖ := by
  set L : StrongDual ℝ (Euc d) →L[ℝ] Euc d :=
    ((InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearEquiv).toContinuousLinearMap with hL
  have hLn : ‖L‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp [hL]
  have hdiff : ∀ y : Euc d, HasFDerivAt (fun y => fderiv ℝ f y) (fderiv ℝ (fderiv ℝ f) y) y := by
    intro y
    have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
    exact (hfd.differentiable (by simp) y).hasFDerivAt
  have hG : ∀ y : Euc d, HasFDerivAt (fun y => gradient f y) (L.comp (fderiv ℝ (fderiv ℝ f) y)) y := by
    intro y
    have := L.hasFDerivAt.comp y (hdiff y)
    exact this
  have hnorm : ∀ y : Euc d, ‖fderiv ℝ (fun y => gradient f y) y‖ ≤ A := by
    intro y
    rw [(hG y).fderiv]
    have hD : ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ A := by
      have h1 := norm_iteratedFDeriv_one (𝕜 := ℝ) (f := fderiv ℝ f) (x := y)
      have h2' := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := y) (n := 1)
      rw [← h1, h2']
      exact h2 y
    calc ‖L.comp (fderiv ℝ (fderiv ℝ f) y)‖ ≤ ‖L‖ * ‖fderiv ℝ (fderiv ℝ f) y‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * A := mul_le_mul hLn hD (by positivity) zero_le_one
      _ = A := one_mul A
  have hdiffG : ∀ y : Euc d, DifferentiableAt ℝ (fun y => gradient f y) y :=
    fun y => (hG y).differentiableAt
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (f := fun y => gradient f y)
    (fun y _ => hdiffG y) (fun y _ => hnorm y) convex_univ (mem_univ y) (mem_univ x)

end HRS.MS.R26T8A

end
