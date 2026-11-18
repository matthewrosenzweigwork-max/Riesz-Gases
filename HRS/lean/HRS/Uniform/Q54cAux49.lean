import HRS.Uniform.Q54cAux48

/-!
# Q54c, part 49: the core comparison theorem (abstract data)
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q54c

open HRS HRS.PDE HRS.Uniform

variable {d : ℕ}

namespace PdeSetup

/-- the constant of the core theorem -/
def Ccore (P : PdeSetup d) (cc : P.CmpConst) : ℝ :=
  (1 + |P.T|) * P.Kc * Real.sqrt (HilbertBDG.bdgConst 2 * (4 * d * HRS.Uniform.Q14.q14S d ((P.n : ℝ) - 1) * |P.T|)) +
  (1 + |P.T|) * (cc.Cst + (cc.Kd * (P.c.Cop (P.n + 2) + 1) + P.c.Cg P.n * cc.Cst)) *
    Real.sqrt (HilbertBDG.bdgConst 2 * (4 * d * HRS.Uniform.Q14.q14S d ((P.n : ℝ) - 1) * |P.T|)) +
  P.Kc + cc.Cst + 1

theorem Ccore_pos (P : PdeSetup d) (cc : P.CmpConst) : 0 < P.Ccore cc := by
  have h1 := P.Kc_nonneg
  have h2 := cc.Cst_nonneg
  have h3 := cc.Kd_nonneg
  have h4 := P.c.Cop_nonneg (P.n + 2)
  have h5 := P.c.Cg_nonneg P.n
  unfold Ccore
  positivity

end PdeSetup

end HRS.Uniform.Q54c
