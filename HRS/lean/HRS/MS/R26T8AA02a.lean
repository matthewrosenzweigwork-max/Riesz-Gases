import HRS.MS.R26T8AA01

/-!
# S8.2 T8A A02 (part a): symmetry of `tripleG` and of `pairJ` for a symmetric kernel
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_a02_pairJ_symm (C : WholeCoeff d) (μ : Measure (Euc d)) {Q : Euc d → Euc d → ℝ}
    (hsymm : ∀ x y, Q x y = Q y x) (x y : Euc d) : pairJ C μ Q x y = pairJ C μ Q y x := by
  rw [r26t8a_a01_pairJ_decomp C μ hsymm x y, r26t8a_a01_pairJ_decomp C μ hsymm y x]
  ring

theorem r26t8a_a02_tripleG_symm_xy {a beta : ℝ} {rho : Euc d → ℝ} {Q : Euc d → Euc d → ℝ}
    (hsymm : ∀ x y, Q x y = Q y x) (x y z : Euc d) :
    tripleG (critCoeff d a beta rho) rho Q x y z = tripleG (critCoeff d a beta rho) rho Q y x z := by
  have k1 := r26t8a_a01_key (a := a) (beta := beta) (rho := rho) hsymm x y z
  have k2 := r26t8a_a01_key (a := a) (beta := beta) (rho := rho) hsymm y x z
  have gy : ∀ u v : Euc d, pairGradY Q u v = pairGradX Q v u := fun u v => r26t8a_a01_gradY_symm hsymm u v
  have hn : rieszKernelGrad d (criticalS d) (y - x) = -rieszKernelGrad d (criticalS d) (x - y) := by
    rw [show y - x = -(x - y) from (neg_sub x y).symm]
    exact HRS.MS.R2Interp.s102_rieszKernelGrad_neg (criticalS d) _
  have hJ := r26t8a_a02_pairJ_symm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) hsymm x y
  have hJ2 := r26t8a_a02_pairJ_symm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) hsymm x z
  have hJ3 := r26t8a_a02_pairJ_symm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) hsymm y z
  simp only [gy, hn, inner_sub_right, inner_neg_left] at k1 k2
  rw [hJ] at k1
  linarith

theorem r26t8a_a02_tripleG_symm_yz {a beta : ℝ} {rho : Euc d → ℝ} {Q : Euc d → Euc d → ℝ}
    (hsymm : ∀ x y, Q x y = Q y x) (x y z : Euc d) :
    tripleG (critCoeff d a beta rho) rho Q x y z = tripleG (critCoeff d a beta rho) rho Q x z y := by
  have k1 := r26t8a_a01_key (a := a) (beta := beta) (rho := rho) hsymm x y z
  have k2 := r26t8a_a01_key (a := a) (beta := beta) (rho := rho) hsymm x z y
  have gy : ∀ u v : Euc d, pairGradY Q u v = pairGradX Q v u := fun u v => r26t8a_a01_gradY_symm hsymm u v
  have hn : rieszKernelGrad d (criticalS d) (z - y) = -rieszKernelGrad d (criticalS d) (y - z) := by
    rw [show z - y = -(y - z) from (neg_sub y z).symm]
    exact HRS.MS.R2Interp.s102_rieszKernelGrad_neg (criticalS d) _
  have hJ3 := r26t8a_a02_pairJ_symm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) hsymm y z
  simp only [gy, hn, inner_sub_right, inner_neg_left] at k1 k2
  rw [hJ3] at k1
  linarith

end HRS.MS.R26T8A
