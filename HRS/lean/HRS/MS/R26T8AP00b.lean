import HRS.MS.R26T8AP00

/-!
# S8.2 local Newton layer, packet T8A.P00b: literal localized Riesz potential and divergence source
Definitions only (Pro T8A P00b, verbatim contract).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

def r26t8a_annularRiesz {d : ℕ} (alpha : ℝ) (chi : Euc d → ℝ) (R : ℝ)
    (F : Euc d → Euc d → ℝ) (X z : Euc d) : ℝ :=
  ∫ v, ‖z-v‖^(alpha-(d:ℝ))*r26t8a_annulus chi R v*midPair F X v

def r26t8a_localRiesz {d : ℕ} (alpha : ℝ) (chi : Euc d → ℝ)
    (F : Euc d → Euc d → ℝ) (x y : Euc d) : ℝ :=
  chi (x-y)*∫ v, ‖x-y-v‖^(alpha-(d:ℝ))*chi v*F (y+v) y

def r26t8a_divSource {d : ℕ} (rho : Euc d → ℝ) (Q : Euc d → Euc d → ℝ)
    (x y : Euc d) : ℝ :=
  rho x*Laplacian.laplacian (fun u => Q u y) x+inner ℝ (gradient rho x) (pairGradX Q x y)

end HRS.MS.R26T8A
