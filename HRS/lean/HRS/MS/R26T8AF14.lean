import HRS.MS.R26T8AF13

/-!
# S8.2 observed-time layer, packet T8A.F14: assemble every field of `r26t8a_FeatureOrbits`

The constants come from F13 (chosen before `rho`); the existence, shift, continuity and derivative fields come from F12,
and the decay bound field from F13 at the same `rho`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.Phase2S82

theorem r26t8a_high_order_feature_orbits (d : ℕ) (hd : 2 ≤ d)
    (a beta m : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho → r26t8a_FeatureOrbits d a beta m C c rho := by
  obtain ⟨C, c, hC, hc, hdec⟩ := r26t8a_feature_decay_exact d hd a beta m ha hbeta
  refine ⟨C, c, hC, hc, fun rho hrho => ?_⟩
  obtain ⟨h1, h2, h3, h4, -⟩ := r26t8a_projected_orbit_regularity d hd a beta m ha hbeta rho hrho
  exact ⟨h1, h2, fun alpha v hv j hj => hdec rho hrho alpha v hv j hj, h3, h4⟩

end HRS.MS.R26T8A
