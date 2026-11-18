import HRS.MS.R26T8AP03c
import HRS.MS.R26T8AP01
import HRS.MS.WadAux1

/-!
# S8.2 local Newton layer, packet T8A.P03 (part d): the annular Newton integral when the annulus is separated from `z`
`r26t8a_newton_sep`: if every `w` with `R/2 <= |w| <= 2R` satisfies `r0 <= |z-w| <= r1`, then the nested jet of the annular Newton
integral at `(X,z)` is `<= C A <X>^{2M} R^{d-sigma} (1+|log R|)^b r0^{2-d-q} (log factor)`.  The proof truncates the kernel
(part a), differentiates in `z` (part b) and in `Y` (part c) under the integral, and uses `r26t8a_annular_source` (P01) at `q=0` and P02.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_S_contDiff {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {R : ℝ} (hR : 0 < R)
    {F : Euc d → Euc d → ℝ} {k : ℕ} (hF : ContDiffOn ℝ k (Function.uncurry F) {p | p.1 ≠ p.2}) :
    ContDiff ℝ k (fun Yw : Euc d × Euc d => r26t8a_annulus chi R Yw.2 * midPair F Yw.1 Yw.2) := by
  have e : (fun Yw : Euc d × Euc d => r26t8a_annulus chi R Yw.2 * midPair F Yw.1 Yw.2) =
      fun Yw => r26t8a_annulus chi R Yw.2 * (r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2) := by
    funext Yw
    by_cases h : ‖Yw.2‖ ≤ R / 2
    · simp only [r26t8a_annulus_zero_small hchi hR h, zero_mul]
    · push Not at h
      simp only [r26t8a_psiCut_one hchi hR (by linarith : R / 4 ≤ ‖Yw.2‖), one_mul]
  rw [e]
  exact (((r26t8a_annulus_contDiff hchi hR).of_le (by exact_mod_cast le_top)).comp contDiff_snd).mul
    (r26t8a_gtilde_contDiff hchi hR hF)

theorem r26t8a_annulus_ne_zero {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {R : ℝ} (hR : 0 < R) {w : Euc d}
    (h : r26t8a_annulus chi R w ≠ 0) : R / 2 < ‖w‖ ∧ ‖w‖ < 2 * R := by
  constructor
  · by_contra hn; exact h (r26t8a_annulus_zero_small hchi hR (not_lt.1 hn))
  · by_contra hn; exact h (r26t8a_annulus_zero_large hchi hR (not_lt.1 hn))

end HRS.MS.R26T8A
