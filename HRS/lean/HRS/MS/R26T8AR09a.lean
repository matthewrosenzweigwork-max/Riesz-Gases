import HRS.MS.S82P2Dis4
import HRS.MS.S82P2Sum3

/-!
# S8.2 observed-time layer, packet T8A.R09a: bounded exponential tilts
A bounded measurable exponent has an integrable exponential with positive integral, and the lower integral of
`ofReal (exp ψ)` is the `ofReal` of the Bochner integral; the calibrated one-body field plus a nonpositive
interaction is at most `1 + 1/1000`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.R26T8A

theorem r26t8a_r09_tilt_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (ψ : α → ℝ) (hm : Measurable ψ) (B : ℝ) (hB : ∀ y, ψ y ≤ B) :
    Integrable (fun y => Real.exp (ψ y)) μ ∧ 0 < ∫ y, Real.exp (ψ y) ∂μ ∧
      ∫⁻ y, ENNReal.ofReal (Real.exp (ψ y)) ∂μ = ENNReal.ofReal (∫ y, Real.exp (ψ y) ∂μ) := by
  have hint : Integrable (fun y => Real.exp (ψ y)) μ := by
    refine Integrable.mono' (integrable_const (Real.exp B))
      (Real.measurable_exp.comp hm).aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (hB y)
  refine ⟨hint, integral_exp_pos hint, ?_⟩
  exact (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => (Real.exp_pos _).le)).symm

theorem r26t8a_r09_psi_le {d : ℕ} {a beta C0 : ℝ} {rho q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    (hbeta : 0 < beta)
    (hcal : HRS.MS.Phase2S82.CalibratedReferenceData d a beta rho q h C0) {N : ℕ} (hN : 2 ≤ N)
    (y : Euc d) {S : ℝ} (hS : 0 ≤ S) :
    beta * HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) y + h N y - (beta / N) * S
      ≤ 1 + 1 / 1000 := by
  have h1 := hcal.small_row y
  have h2 := (abs_le.1 (hcal.hsmall N hN y)).2
  have h3 : 0 ≤ (beta / N) * S := by positivity
  linarith

end HRS.MS.R26T8A
