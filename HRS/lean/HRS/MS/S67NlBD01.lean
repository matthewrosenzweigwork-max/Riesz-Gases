import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie

/-!
# S6.7nl.01: frozen index arithmetic and positive bootstrap increment
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

/-- Positive increment for the finite a priori bootstrap. -/
def s67bd_delta (d : ℕ) (s : ℝ) : ℝ := (2 - movA d s) / 2

/-- S6.7nl.01: frozen index arithmetic and the positive bootstrap increment. -/
theorem s67bd_indices (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (j M j' m : ℕ) (hM : (d : ℝ) / 2 + j + 5 < M) (hj' : 1 ≤ j')
    (hm : (d : ℝ) / 2 + j' + 6 < m) (hmM : (M : ℝ) + 4 < m) :
    1 ≤ movA d s ∧ movA d s < 2 ∧
    0 ≤ movA d s - 1 ∧ movA d s - 1 < 1 ∧ 2 ≤ M ∧
    (d : ℝ) / 2 + 7 < m ∧ 0 < s67bd_delta d s ∧
    movA d s + s67bd_delta d s < 2 ∧
    ∀ σ : ℝ, 2 ≤ σ → σ ≤ M →
      0 ≤ σ - movA d s ∧ (d : ℝ) / 2 < (m : ℝ) - movA d s ∧
      σ - movA d s ≤ ((m : ℝ) - movA d s) - 1 := by
  have hA1 : 1 ≤ movA d s := by
    unfold movA
    exact le_max_left _ _
  have hA2 : movA d s < 2 := by
    unfold movA
    refine max_lt (by norm_num) ?_
    linarith
  have hA0 : 0 ≤ movA d s - 1 := by linarith
  have hA1' : movA d s - 1 < 1 := by linarith
  have hdR : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hjR : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hj'R : (1 : ℝ) ≤ (j' : ℝ) := by exact_mod_cast hj'
  have hM5 : (5 : ℝ) < (M : ℝ) := by linarith
  have hM5' : 5 < M := by exact_mod_cast hM5
  have h2M : 2 ≤ M := by omega
  have h7 : (d : ℝ) / 2 + 7 < (m : ℝ) := by linarith
  have hδpos : 0 < s67bd_delta d s := by
    unfold s67bd_delta
    linarith
  have hδsum : movA d s + s67bd_delta d s < 2 := by
    unfold s67bd_delta
    linarith
  refine ⟨hA1, hA2, hA0, hA1', h2M, h7, hδpos, hδsum, fun σ hσ2 hσM => ⟨?_, ?_, ?_⟩⟩
  · linarith
  · linarith
  · linarith

end HRS.MS.BreakdownS67
