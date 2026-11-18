import HRS.MS.R2WinErrAux16
import HRS.MS.R2WinOrbAux1
import HRS.MS.GoFeatTie

/-!
# S10.4 input `hphi`: the oscillator test functions have `∂_aφ_α ∈ C_b^{4d+42}` with norm `≤ C_φ b_α`

`s104_hphi : S104Phi d` (for `d ≥ 1`): from `S45.s45_cb_oscTest` at order `4d+43` (so that the gradient components are `C_b^{4d+42}`) and
`λ_α^{-(m-J')/2} ≤ λ_α^{(J-m)/2}` for `J' = 4d+43 ≤ J = 18d+180` (`s103_phi_cb` is the same estimate at order `4d+42`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinErr

open HRS HRS.Whole HRS.MS.Go

variable {d : ℕ}

theorem s104_hphi (hd : 1 ≤ d) : S104Phi d := by
  obtain ⟨K, hK0, hK⟩ := S45.s45_cb_oscTest hd (4 * d + 43) ((24 * d + 240 : ℕ) : ℝ)
  refine ⟨K, hK0, fun α a => ?_⟩
  obtain ⟨hmem, hnorm⟩ := hK α
  have hφ : ContDiff ℝ ((4 * d + 42 + 1 : ℕ) : WithTop ℕ∞) (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) :=
    hmem.1
  obtain ⟨hc, hbd⟩ := s55f_gradComp (n := 4 * d + 42) hφ a
  refine ⟨hc, fun j hj x => (hbd j hj x).trans ?_⟩
  have hsup : ‖iteratedFDeriv ℝ (j + 1) (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) x‖ ≤
      cbNorm (4 * d + 43) (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) := by
    unfold cbNorm
    have hbdd := hmem.2 (j + 1) (by omega)
    have h1 := le_ciSup hbdd x
    refine h1.trans ?_
    exact Finset.single_le_sum (f := fun i => ⨆ z, ‖iteratedFDeriv ℝ i
      (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) z‖)
      (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  refine hsup.trans (hnorm.trans (mul_le_mul_of_nonneg_left ?_ hK0))
  show oscEigenvalue d α ^ (-((((24 * d + 240 : ℕ) : ℝ) - ((4 * d + 43 : ℕ) : ℝ)) / 2)) ≤
    oscEigenvalue d α ^ ((((18 * d + 180 : ℕ) : ℝ) - ((24 * d + 240 : ℕ) : ℝ)) / 2)
  refine Real.rpow_le_rpow_of_exponent_le (one_le_oscEigenvalue α) ?_
  push_cast
  nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]

end HRS.MS.R2WinErr
