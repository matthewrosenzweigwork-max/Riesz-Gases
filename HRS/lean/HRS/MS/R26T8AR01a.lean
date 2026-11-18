import HRS.MS.S82RQ1
import HRS.MS.S82P2Mom

/-!
# S8.2 local Newton layer, packet T8A.R01a: smoothness of the heat cutoff off the origin
The merged `HRS.MS.S82R.s82r_qTau_shortRange` already proves that `qTau d (criticalS d) tau` is a `ShortRangePole`; its `smooth` field is the claim.
-/

set_option autoImplicit false
noncomputable section
open HRS HRS.Whole HRS.MS.Phase2S82
open scoped ContDiff

namespace HRS.MS.R26T8A

theorem r26t8a_heat_cutoff_smooth (d : ℕ) (hd : 2 ≤ d) (tau : ℝ) (htau : 0 < tau) :
    ContDiffOn ℝ ∞ (HRS.MS.Psd.qTau d (criticalS d) tau) {z | z ≠ 0} :=
  (HRS.MS.S82R.s82r_qTau_shortRange (by omega) htau).smooth

end HRS.MS.R26T8A
