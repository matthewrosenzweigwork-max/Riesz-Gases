import HRS.MS.R26T8AP11f8
import HRS.MS.R26T8AP10a

/-!
# S8.2 T8A P11f (part 9): `divSource ρ Q = ρ ∑_i ∂_{x_i}²Q + ∑_i (∂_iρ) ∂_{x_i}Q` off the diagonal, and its smoothness
`r26t8a_Stil ρ Q` is the right-hand side written with the pair functions `dx_i`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

def r26t8a_Stil (ρ : Euc d → ℝ) (Q : Euc d → Euc d → ℝ) (u y : Euc d) : ℝ :=
  ρ u * ∑ i : Fin d, r26t8a_dx i (r26t8a_dx i Q) u y +
    ∑ i : Fin d, fderiv ℝ ρ u (EuclideanSpace.single i 1) * r26t8a_dx i Q u y

theorem r26t8a_f9_divSource_eq {Q : Euc d → Euc d → ℝ} {y u : Euc d} {ρ : Euc d → ℝ}
    (hf : ContDiffAt ℝ 2 (fun v => Q v y) u) :
    r26t8a_divSource ρ Q u y = r26t8a_Stil ρ Q u y := by
  set f : Euc d → ℝ := fun v => Q v y with hfdef
  have hDD : DifferentiableAt ℝ (fderiv ℝ f) u :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hdx2 : ∀ i : Fin d, r26t8a_dx i (r26t8a_dx i Q) u y =
      fderiv ℝ (fderiv ℝ f) u (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
    intro i
    unfold r26t8a_dx
    have hfun : (fun x' => fderiv ℝ (fun x'' => Q x'' y) x' (EuclideanSpace.single i 1)) =
        (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ) : Euc d)) ∘ fderiv ℝ f := rfl
    rw [hfun, ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ) : Euc d)).hasFDerivAt.comp u
      hDD.hasFDerivAt).fderiv]
    simp
  unfold r26t8a_divSource r26t8a_Stil pairGradX
  congr 1
  · congr 1
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin d) ℝ)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iteratedFDeriv_two_apply, hdx2]
    simp
  · rw [real_inner_comm]
    simp only [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [r26t8a_gradient_coord, r26t8a_dx]
    simp [mul_comm]

end HRS.MS.R26T8A
