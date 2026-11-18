import HRS.MS.SA16Y6CEx2
import HRS.MS.SA16Y4Nl3

/-!
# S.A.16 (SA16Y10) Sm1: `eucNonlocal` is homogeneous in the coefficient (regime-free)
-/

set_option autoImplicit false

noncomputable section

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

theorem sa16y10_euc_smul (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (a F : Euc d → ℝ) (x : Euc d) :
    HRS.MH.AdjointRd.eucNonlocal s M (fun y => c * a y) F x = c * HRS.MH.AdjointRd.eucNonlocal s M a F x := by
  unfold HRS.MH.AdjointRd.eucNonlocal
  by_cases hc : c = 0
  · subst hc; simp
  · letI : Invertible c := invertibleOfNonzero hc
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have key : (fun x' : Euc d => ∫ y, rieszKernel d s (x' - y) * ((fun y => c * a y) y *
        fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))) =
        fun x' => c • ∫ y, rieszKernel d s (x' - y) * (a y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))) := by
      funext x'
      rw [smul_eq_mul, ← MeasureTheory.integral_const_mul]
      congr 1; funext y; ring
    rw [key]
    have hs := fderiv_const_smul_of_invertible (𝕜 := ℝ) (c := c) (x := x)
      (f := fun x' : Euc d => ∫ y, rieszKernel d s (x' - y) * (a y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))))
    rw [show (fun x' : Euc d => c • ∫ y, rieszKernel d s (x' - y) *
        (a y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))) = c • (fun x' : Euc d => ∫ y, rieszKernel d s (x' - y) *
        (a y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))) from rfl, hs]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring

end HRS.Whole.AppendixA.Phase2SA16R

end
