import HRS.MS.S82P2Local
import HRS.MS.S82P2Mom

/-!
# S8.2 local Newton layer, packet T8A.P00: dyadic Newton and finite-parametrix objects
Definitions only (Pro T8A P00, verbatim contract); names `r26t8a_*`, namespace `HRS.MS.R26T8A`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

def r26t8a_annulus {d : ℕ} (chi : Euc d → ℝ) (R : ℝ) (z : Euc d) : ℝ :=
  chi (R⁻¹ • z) - chi ((2/R) • z)

def r26t8a_annularNewton {d : ℕ} (nu : ℝ) (chi : Euc d → ℝ) (R : ℝ)
    (F : Euc d → Euc d → ℝ) (X z : Euc d) : ℝ :=
  ∫ w, newtonKernel d nu (z-w) * r26t8a_annulus chi R w * midPair F X w

def r26t8a_jetEnvelope (b : ℕ) (sigma : ℝ) (r : ℝ) : ℝ :=
  1 + (min 1 r)^(-sigma) * (1+|Real.log (min 1 r)|)^b

def r26t8a_parametrixTerm {d : ℕ} (C : WholeCoeff d) (mu : Measure (Euc d))
    (chi : Euc d → ℝ) (f : Euc d → ℝ) (j : ℕ) : Euc d → Euc d → ℝ :=
  (newtonDefect C mu chi)^[j] (HSource mu f)

def r26t8a_parametrix {d : ℕ} (C : WholeCoeff d) (mu : Measure (Euc d))
    (chi : Euc d → ℝ) (f : Euc d → ℝ) : Euc d → Euc d → ℝ :=
  ∑ j ∈ Finset.range (iterationCount d), localNewton mu C.ν chi
    (r26t8a_parametrixTerm C mu chi f j)

def r26t8a_truncForce {d : ℕ} (eps : ℝ) (z : Euc d) : Euc d :=
  if eps < ‖z‖ then rieszKernelGrad d (criticalS d) z else 0

end HRS.MS.R26T8A
