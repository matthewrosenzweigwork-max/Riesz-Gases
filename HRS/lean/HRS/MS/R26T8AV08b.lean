import HRS.MS.R26T8AD01

/-!
# S8.2 observed-time layer, packet T8A.V08b: reversible windows of arbitrary singular canonical realizations

Adapter to the native result: the finite-dimensional marginals of a canonical realization are reversible on every
window (`s81r_canonical_reversible_windows`, packaged as `r26t8a_reversible_of_canonical` in D01).  The cutoff chain
V00-V07 of the Pro packet (cutoff Picard flow, GapRef for the cutoff Gibbs data, detailed balance, density-ratio
convergence) is not needed: the native S81G/S81R argument already treats the singular canonical realization.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_canonical_reversible_windows (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N)
    (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d)
    (X : ℝ≥0 → Omega → EucConfig d N)
    (hX : IsCanonicalRealization d (criticalS d) a beta N P X0 W X) :
    r26t8a_ReversibleWindows P X :=
  r26t8a_reversible_of_canonical d N hd a beta ha hbeta P X0 W X hX

end HRS.MS.R26T8A

end
