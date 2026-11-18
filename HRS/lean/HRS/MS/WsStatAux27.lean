import HRS.MS.WsStatAux26

/-!
# S21 packet I-5: the stationary master comparison, statement and proof

See `WsStatAux25` for the description.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath HRS.MP.RdRem HRS.GF HRS.Uniform HRS.Whole.AppendixA
open HRS (Euc)

variable {d : ℕ}

/-- The coordinates of the centred remainder: `-(σ/2) ∫_0^t (c_α - E c_α) dr`. -/
def s21Gfun (b : WholeBounds d) (S : WholeSetup b) {N : ℕ} (ρ : Euc d → ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N) (t : ℝ) (α : MultiIndex d)
    (ζ : Ω) : ℝ :=
  -(S.σ N / 2) * ∫ r in Set.Icc (0 : ℝ) t,
    (commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ -
      ∫ ζ', commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ' ∂P)

end HRS.MS.S21
