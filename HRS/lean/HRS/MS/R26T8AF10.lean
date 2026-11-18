import HRS.MS.R26T8AF00
import HRS.MS.OrbFeatAux1

/-!
# S8.2 observed-time layer, packet T8A.F10: the Hermite datum norm equals the frozen S8.2 weight

Immediate from the merged `s52b_phi` (normalised Hermite Schwartz map with `oscNorm N = λ_α^{(N-m)/2}` for natural `N`)
at `N = M_* + 4`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

theorem r26t8a_feature_weight (d : ℕ) (m : ℝ) (alpha : MultiIndex d) :
    ∃ f : SchwartzMap (Euc d) ℝ, ⇑f = oscTestFun m alpha ∧
      oscNorm ((HRS.MS.S82BD.s82FeatureOrder d + 4 : ℕ) : ℝ) f = HRS.MS.S82BD.s82Weight d m alpha := by
  obtain ⟨f, hf, hn⟩ := HRS.MS.S52B.s52b_phi (d := d) m alpha
  refine ⟨f, hf, ?_⟩
  rw [hn, HRS.MS.S82BD.s82Weight]
  push_cast
  rfl

end HRS.MS.R26T8A

end
