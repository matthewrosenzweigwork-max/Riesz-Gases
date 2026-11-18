import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.Mov63DAux1

/-!
# S6.7nl.67: one common positive radius and strict output rate gap
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

/-- S6.7nl.67: a common positive radius and a strict rate gap, chosen before any data. -/
theorem s67bd_common_radius (Rbar C c1 lam : ℝ)
    (hR : 0 < Rbar) (hC : 1 ≤ C) (hc1 : 0 < c1) (hlam : c1 ≤ lam) :
    ∃ R c : ℝ, 0 < R ∧ R ≤ Rbar ∧ R ≤ 1 ∧ 0 < c ∧ c < c1 ∧ c < lam ∧
      C * R * mndBeta (1 / 2) (c1 - c) ≤ 1 / 2 := by
  have hC0 : 0 < C := by linarith
  obtain ⟨B, hBdef⟩ : ∃ B, mndBeta (1 / 2) (c1 - c1 / 2) = B := ⟨_, rfl⟩
  have hB : 0 ≤ B := by
    rw [← hBdef]
    exact HRS.MS.Mov63.mnd_beta_nonneg _ _
  have hK : 0 < 2 * C * (B + 1) := by positivity
  obtain ⟨R, hRdef⟩ : ∃ R, R = min Rbar (min 1 (1 / (2 * C * (B + 1)))) := ⟨_, rfl⟩
  have hR0 : 0 < R := by
    rw [hRdef]
    exact lt_min hR (lt_min one_pos (by positivity))
  have hRR : R ≤ Rbar := by
    rw [hRdef]
    exact min_le_left _ _
  have hR1 : R ≤ 1 := by
    rw [hRdef]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hRK : R ≤ 1 / (2 * C * (B + 1)) := by
    rw [hRdef]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hprod : R * (2 * C * (B + 1)) ≤ 1 := (le_div_iff₀ hK).1 hRK
  refine ⟨R, c1 / 2, hR0, hRR, hR1, by positivity, by linarith, by linarith, ?_⟩
  rw [hBdef]
  nlinarith [mul_nonneg (mul_nonneg hC0.le hR0.le) hB]

end HRS.MS.BreakdownS67
