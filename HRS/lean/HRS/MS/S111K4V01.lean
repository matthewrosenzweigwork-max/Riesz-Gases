import HRS.MS.S111K4R1

/-!
# S11.1 / V01 (S11K4): Pro `R26-T6C.V01`, stationary covariance under a common shift.

`r26t6_thermalCoeff d s a β ρ` of the Pro packet is, by its definition on the Pro branch, the coefficient
`(quadraticGradientDyn d s a β).coeff (fun _ => ρ)`; the statement below uses that coefficient directly.
The proof is the stationarity lemma `k4_lgc_shift` (R1).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4

open HRS HRS.Whole

variable {d : ℕ}

/-- **V01** (Pro `R26-T6C.V01`): the two-time covariance of the thermal stationary preparation is invariant
under a common shift of both times. -/
theorem k4_v01 (hd : 2 ≤ d) (s a beta u r t : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hu : 0 ≤ u) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d s a beta rho)
    (f h : Euc d → ℝ) (hf : IsOscTest (wholeSpaceIndex d) f)
    (hh : IsOscTest (wholeSpaceIndex d) h) :
    linearGaussianCov ((quadraticGradientDyn d s a beta).coeff (fun _ => rho)) beta⁻¹
        (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal rho) beta) (u + r) (u + t) f h =
      linearGaussianCov ((quadraticGradientDyn d s a beta).coeff (fun _ => rho)) beta⁻¹
        (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal rho) beta) r t f h :=
  k4_lgc_shift hd s a beta hs0 hs ha hbeta rho hrho hu hr ht hf hh

end HRS.MS.S111K4
