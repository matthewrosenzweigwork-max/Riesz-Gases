import HRS.MS.R26T8AR10
import HRS.MS.S82RB3

/-!
# S8.2 observed-time layer, packet T8A.R11: generic finite-pin resampling theorem (corrected version)
The merged `S82R.s82r_resampling` proves the resampling inequality for the displayed reference law under the Gaussian
bound of the thermal density.  The Pro packet statement has no `0 < a`, which the Gaussian bound needs; corrected
version `r26t8a_pinned_resampling_pos` has `(ha : 0 < a)`.  Conclusion as in the packet (`2 : ℝ≥0∞`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.R26T8A
open HRS.MS.Phase2S82

theorem r26t8a_pinned_resampling_pos {d p n : ℕ} (hd : 2 ≤ d) {a beta C0 : ℝ} (ha : 0 < a)
    (hbeta : 0 < beta) {rho q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    (hrho : HRS.Whole.IsThermalEquilibrium d (criticalS d) a beta rho)
    (hcal : CalibratedReferenceData d a beta rho q h C0) (N : ℕ) (hN : 2 ≤ N)
    (hnp : n + p ≤ N) (pins : Fin p → Euc d) (F : HRS.Whole.EucConfig d n → ℝ)
    (hF : Measurable F)
    (hF2 : MemLp F 2 (referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins)) :
    evariance F (referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins) ≤
      2 * ∑ i, ∫⁻ X, ∫⁻ y, ENNReal.ofReal ((F (Function.update X i y) - F X) ^ 2)
        ∂resampleLaw q h (HRS.Whole.withDensityReal rho) beta N pins i X
        ∂referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins := by
  obtain ⟨-, C, c, hC, hc, hb⟩ := HRS.MS.Wad.s84_thermal_gaussReg hd ha hbeta hrho
  have hG : HRS.Whole.HasR2GaussianUpper (C + 1) c rho := ⟨hc, fun x => by
    have h1 := (le_abs_self (rho x)).trans (hb x).1
    nlinarith [Real.exp_pos (-c * ‖x‖ ^ 2)]⟩
  have := HRS.MS.S82R.s82r_resampling hd hbeta hcal (G := C + 1) (c := c) (by linarith)
    hrho.2.1 hG hN hnp pins F hF2
  simpa using this

end HRS.MS.R26T8A
