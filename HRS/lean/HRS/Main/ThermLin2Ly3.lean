import HRS.Main.ThermLinPlan2
import HRS.Main.T25PAux19

/-!
# THERMLIN2 packet Ly, part 3: `tl2_CbDens_det` (Z1)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P

variable {d : ℕ}

/-- Z1: the covariation density `tl2CbDens` of the stationary field is a deterministic covariance density on
`[0,T']` and vanishes after `T'` (`t25p_detCov` for `thermlin_stationary_traj`, and `t25p_covDensT_zero`). -/
theorem tl2_CbDens_det_proof (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m) {T' : ℝ} (hT' : 0 < T') :
    IsDetCovDensity T' (tl2CbDens S ρβ m T') ∧ ∀ r : ℝ, T' < r → tl2CbDens S ρβ m T' r = 0 := by
  refine ⟨?_, fun r hr => t25p_covDensT_zero hr _⟩
  have hm1 : (d : ℝ) / 2 + 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  exact t25p_detCov S.hd (HRS.ThermLin.thermlin_stationary_traj S h) hm1 hT'

example := (@tl2_CbDens_det_proof : type_of% @tl2_CbDens_det)

end HRS.ThermLin.Plan2
