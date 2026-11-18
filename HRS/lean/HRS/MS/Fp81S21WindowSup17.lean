import HRS.MS.Fp81S21WindowSup16
import HRS.MS.S21L_S08

/-!
# S2.1(iii), packet 9d: Hessian envelope for the commutator kernel

The compiled `IsBoundedPairKernel` bound is a weighted bound off the diagonal.
The gradient of a twice continuously differentiable function with bounded
Hessian is globally Lipschitz, which lets the compiled `s21l_s08_comm_bounded`
adapter produce exactly that kernel class. No bound on the function or its
gradient values is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open HRS HRS.Whole HRS.Whole.AppendixA
open scoped NNReal

namespace HRS.Fp81.S21

/-- A global Hessian bound gives the weighted bounded-kernel envelope for the
Riesz commutator kernel. -/
theorem fp81s21_comm_kernel_of_hessian_bound
    {d : ℕ} {s B : ℝ} {f : Euc d → ℝ}
    (hs0 : 0 ≤ s) (hB : 0 ≤ B) (hf : ContDiff ℝ 2 f)
    (hess : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ B) :
    IsBoundedPairKernel s (max s 1 * Real.toNNReal B)
      (commutatorKernel d s (fun x => gradient f x)) := by
  let Λ : ℝ≥0 := Real.toNNReal B
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have h1 : LipschitzWith Λ (fderiv ℝ f) := by
    refine lipschitzWith_of_nnnorm_fderiv_le hdf fun z => ?_
    have h2 : ‖fderiv ℝ (fderiv ℝ f) z‖ = ‖iteratedFDeriv ℝ 2 f z‖ := by
      rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
    rw [← NNReal.coe_le_coe, coe_nnnorm, h2, Real.coe_toNNReal B hB]
    exact hess z
  have h3 : LipschitzWith 1
      (fun p : Euc d →L[ℝ] ℝ => (InnerProductSpace.toDual ℝ (Euc d)).symm p) :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.isometry.lipschitzWith
  have hgrad : LipschitzWith Λ (fun x => gradient f x) := by
    have h := h3.comp h1
    simp only [one_mul] at h
    change LipschitzWith Λ
      ((fun p : Euc d →L[ℝ] ℝ => (InnerProductSpace.toDual ℝ (Euc d)).symm p) ∘
        fderiv ℝ f)
    exact h
  exact HRS.MS.R26T3.s21l_s08_comm_bounded s hs0 Λ (fun x => gradient f x) hgrad

#print axioms fp81s21_comm_kernel_of_hessian_bound

end HRS.Fp81.S21

end
