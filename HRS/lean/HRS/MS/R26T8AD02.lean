import HRS.MS.R26T8AD00

/-!
# S8.2 observed-time layer, packet T8A.D02: actual age-parametrized normal-form terms
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

def r26t8a_ageTest {d : ℕ} (a beta m : ℝ) (rho : Euc d → ℝ) (alpha : MultiIndex d) (j : ℕ) (v : ℝ) :
    Euc d → ℝ :=
  r26t8a_genPower (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) j
    (r26t8a_projectedOrbit (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) v (oscTestFun m alpha))

def r26t8a_QAge {d N : ℕ} (a beta m : ℝ) (rho : Euc d → ℝ)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (alpha : MultiIndex d) (j : ℕ) (v : ℝ) : EucConfig d N → ℝ :=
  r26t8a_correctedQ a beta Psi (r26t8a_ageTest a beta m rho alpha j v)

def r26t8a_DAge {d N : ℕ} (a beta m : ℝ) (rho : Euc d → ℝ)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (alpha : MultiIndex d) (j : ℕ) (v : ℝ) : EucConfig d N → ℝ :=
  r26t8a_correctedD a beta rho Psi (r26t8a_ageTest a beta m rho alpha j v)

def r26t8a_VAge {d N : ℕ} (a beta m : ℝ) (rho : Euc d → ℝ)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (alpha : MultiIndex d) (j : ℕ) (v : ℝ) : EucConfig d N → ℝ :=
  r26t8a_DAge a beta m rho Psi alpha j v - r26t8a_QAge a beta m rho Psi alpha (j + 1) v

open Classical in
def r26t8a_noiseAge {d N : ℕ} {Omega : Type*} (a beta m : ℝ) (rho : Euc d → ℝ)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (alpha : MultiIndex d)
    (X : ℝ≥0 → Omega → EucConfig d N) (j : ℕ) (b r : ℝ) (w : Omega) (i : Fin N × Fin d) : ℝ :=
  if 0 ≤ r ∧ r ≤ b ∧ X r.toNNReal w ∉ eucCollisionSet d N then
    Real.sqrt (2 / beta) *
      Phase2S82.configGrad (r26t8a_QAge a beta m rho Psi alpha j (b - r)) (X r.toNNReal w) i.1 i.2
  else 0

end HRS.MS.R26T8A

end
