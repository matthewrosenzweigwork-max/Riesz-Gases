import HRS.MS.SA12Z3NearN1
import HRS.MS.UniqN3aI
import HRS.MS.UniqN3cB
import HRS.MS.UniqN3cC
import HRS.MS.UniqN3cD
import HRS.MS.UniqT1

/-!
# S.A.12 N5 (SA12Z3), part A: polarization of the matrix Hessian and the Fourier bridge

For `v ∈ C²_c`: `matrixHess M v = ¼ ∑_{ij} M_{ji} (g * D²_{e_i+e_j} v - g * D²_{e_i-e_j} v)`, and for `u ∈ L²`
`-∫ u matrixHess M v = ¼ ∑_{ij} M_{ji} (B_{ij}^+ (u,v) - B_{ij}^- (u,v))`, where `B_p = symbolForm (mq c s p)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3 HRS.MS.UniqN3a HRS.MS.UniqN2b

variable {d : ℕ}

/-- The Hessian entry is `g * ∂_i∂_j v`. -/
theorem sa12z3_hess_convFun {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i j : Fin d) {v : Euc d → ℝ}
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) (y : Euc d) :
    hessRiesz d s i j v y = HRS.Whole.convFun (rieszKernel d s) (D1 i (D1 j v)) y := by
  rw [sa12z3_hess_eq hs0 hsd i j hv hvc y]
  exact HRS.MS.UniqN1c.n1c_D1_kcd hs0 hsd hv hvc j i y

/-- The two polarization directions. -/
def sa12z3_dp (d : ℕ) (i j : Fin d) : Euc d := EuclideanSpace.single i (1 : ℝ) + EuclideanSpace.single j 1
def sa12z3_dm (d : ℕ) (i j : Fin d) : Euc d := EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j 1

theorem sa12z3_matrixHess_polar {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ)
    {v : Euc d → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) (y : Euc d) :
    matrixHess d s M v y = (1 / 4 : ℝ) * ∑ i, ∑ j, M j i *
      (HRS.Whole.convFun (rieszKernel d s) (qq (sa12z3_dp d i j) v) y -
        HRS.Whole.convFun (rieszKernel d s) (qq (sa12z3_dm d i j) v) y) := by
  unfold matrixHess
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sa12z3_hess_convFun hs0 hsd i j hv hvc y]
  have hI : ∀ q : Euc d, Integrable (fun x => rieszKernel d s (y - x) * qq q v x) volume := fun q =>
    n2b_conv_integrable hs0 hsd (qq_contDiff hv) (qq_hasCompactSupport hvc) y
  have e1 : HRS.Whole.convFun (rieszKernel d s) (D1 i (D1 j v)) y =
      HRS.Whole.convFun (rieszKernel d s) (fun x => (1 / 4 : ℝ) * (qq (sa12z3_dp d i j) v x -
        qq (sa12z3_dm d i j) v x)) y := by
    unfold HRS.Whole.convFun
    congr 1; funext x
    rw [HRS.MS.UniqN3c.n3c_hess_symm hv j i x, HRS.MS.UniqN1b.n1b_polar hv i j x]
    rfl
  rw [e1]
  unfold HRS.Whole.convFun
  have e2 : (fun x => rieszKernel d s (y - x) * ((1 / 4 : ℝ) * (qq (sa12z3_dp d i j) v x -
        qq (sa12z3_dm d i j) v x))) = fun x => (1 / 4 : ℝ) *
      (rieszKernel d s (y - x) * qq (sa12z3_dp d i j) v x -
        rieszKernel d s (y - x) * qq (sa12z3_dm d i j) v x) := by
    funext x; ring
  rw [e2, integral_const_mul, integral_sub (hI _) (hI _)]
  ring

end HRS.MH.AdjointRd.Phase2SA12Near
