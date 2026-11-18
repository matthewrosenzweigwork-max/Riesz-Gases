import HRS.MS.R26T8AA01n

/-!
# S8.2 T8A A01 (part o): the ungrouped algebraic form of `tripleG`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_a01_ungrouped {a beta : ℝ} {rho : Euc d → ℝ} {Q : Euc d → Euc d → ℝ}
    (hsymm : ∀ x y, Q x y = Q y x) (x y z : Euc d) :
    3 * tripleG (critCoeff d a beta rho) rho Q x y z =
      -inner ℝ (rieszKernelGrad d (criticalS d) (x - z) - forceMean rho x) (pairGradX Q x y)
      - inner ℝ (rieszKernelGrad d (criticalS d) (y - z) - forceMean rho y) (pairGradX Q y x)
      - inner ℝ (rieszKernelGrad d (criticalS d) (x - y) - forceMean rho x) (pairGradX Q x z)
      + inner ℝ (rieszKernelGrad d (criticalS d) (y - z) + forceMean rho z) (pairGradX Q z x)
      - inner ℝ (rieszKernelGrad d (criticalS d) (y - x) - forceMean rho y) (pairGradX Q y z)
      + inner ℝ (rieszKernelGrad d (criticalS d) (x - z) + forceMean rho z) (pairGradX Q z y)
      - pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q x y
      - pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q x z
      - pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q y z := by
  have gy1 : pairGradY Q x y = pairGradX Q y x := r26t8a_a01_gradY_symm hsymm x y
  have gy2 : pairGradY Q x z = pairGradX Q z x := r26t8a_a01_gradY_symm hsymm x z
  have gy3 : pairGradY Q y z = pairGradX Q z y := r26t8a_a01_gradY_symm hsymm y z
  have hn1 : rieszKernelGrad d (criticalS d) (z - x) = -rieszKernelGrad d (criticalS d) (x - z) := by
    rw [show z - x = -(x - z) from (neg_sub x z).symm]; exact HRS.MS.R2Interp.s102_rieszKernelGrad_neg (criticalS d) _
  have hn3 : rieszKernelGrad d (criticalS d) (z - y) = -rieszKernelGrad d (criticalS d) (y - z) := by
    rw [show z - y = -(y - z) from (neg_sub y z).symm]; exact HRS.MS.R2Interp.s102_rieszKernelGrad_neg (criticalS d) _
  unfold tripleG tripleT HRS.MS.Phase2S82.centeredForce
  simp only [hn1, hn3, gy1, gy2, gy3, inner_sub_left, inner_add_left, inner_neg_left]
  ring

end HRS.MS.R26T8A
