import HRS.MS.R26T8AP00

/-!
# S8.2 local Newton layer, packet T8A.D04: one fixed diagonal-safe finite parametrix and canonical smooth extension
Definitions verbatim from the Pro packet (`r26t8a_parametrixZero`, `r26t8a_remainder`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

def r26t8a_parametrixZero {d : ℕ} (C : WholeCoeff d) (mu : Measure (Euc d))
    (chi : Euc d → ℝ) (f : Euc d → ℝ) (x y : Euc d) : ℝ :=
  if x = y then 0 else r26t8a_parametrix C mu chi f x y

def r26t8a_remainder {d : ℕ} (C : WholeCoeff d) (mu : Measure (Euc d))
    (chi : Euc d → ℝ) (f : Euc d → ℝ) : Euc d → Euc d → ℝ := by
  classical
  exact if h : ∃ G : Euc d → Euc d → ℝ, ContDiff ℝ 8 (Function.uncurry G) ∧
    ∀ x y, x ≠ y → G x y = r26t8a_parametrixTerm C mu chi f (iterationCount d) x y
  then h.choose else 0

end HRS.MS.R26T8A
