import HRS.MS.R26T8AW1
import HRS.MS.R26T8AW2

/-!
# S8.2 T8A NL1 (pointwise nonlocal field, part 1): values of a conormal kernel, and a logarithm bound

`r26t8a_nl_value`: `Conormal 0 b M σ A F` gives the pointwise bound at `(x,y)`, `x ≠ y`, with `r = min 1 ‖x-y‖`.
`r26t8a_nl_log_bound`: `(1+|log r|)^b ≤ K (1 + r^{-s})` for `0 < r ≤ 1`, `s > 0`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_nl_value {b : ℕ} {M σ A : ℝ} {F : Euc d → Euc d → ℝ} (hF : Conormal 0 b M σ A F) (x y : Euc d)
    (hxy : x ≠ y) :
    |F x y| ≤ A * Phase2S82.pairWeight M x y *
      (1 + (min 1 ‖x - y‖) ^ (-(σ + (0 : ℕ))) * (1 + |Real.log (min 1 ‖x - y‖)|) ^ b) := by
  have hz : x - y ≠ 0 := sub_ne_zero.2 hxy
  have h := hF.2 0 0 (le_refl _) ((1 / 2 : ℝ) • (x + y)) (x - y) hz
  have e1 : (1 / 2 : ℝ) • (x + y) + (1 / 2 : ℝ) • (x - y) = x := by
    rw [← smul_add]; rw [show x + y + (x - y) = (2 : ℝ) • x by rw [two_smul]; abel]; rw [smul_smul]; norm_num
  have e2 : (1 / 2 : ℝ) • (x + y) - (1 / 2 : ℝ) • (x - y) = y := by
    rw [← smul_sub]; rw [show x + y - (x - y) = (2 : ℝ) • y by rw [two_smul]; abel]; rw [smul_smul]; norm_num
  have hv : ‖mixedJet 0 0 F ((1 / 2 : ℝ) • (x + y)) (x - y)‖ = |F x y| := by
    unfold mixedJet
    rw [norm_iteratedFDeriv_zero, norm_iteratedFDeriv_zero]
    simp only [midPair, e1, e2, Real.norm_eq_abs]
  rw [hv, e1, e2] at h
  exact h

end HRS.MS.R26T8A

end
