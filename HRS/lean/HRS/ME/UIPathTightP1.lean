import HRS.ME.UIPath
import HRS.ME.RetPathLaw
import HRS.ME.RetGlueB
import HRS.MD.EQFrozen29Rest
import HRS.MD.EQLawPath
import HRS.Sections.AdjKGlue

/-!
# Packet P1 of `HRS.ui_path_tight`: measurability of the Gibbs-centred window

Proof of `windowGibbs_aemeasurable` (statement frozen in `HRS/ME/UIPathTightSpec.lean`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.ME.UIPathTight

open HRS HRS.LZ HRS.Uniform HRS.Main

variable {d : ℕ}

/-- **P1** (measurability of the Gibbs-centred window; scope note 1.4, "JUNK/MEASURABILITY").
`windowGibbs` (junk value `0` for discontinuous windows) is `P`-a.e. measurable for any strong solution
`X` of any particle system (`IsStrongSolution` supplies the measurability of each `X t` and the a.s.
continuity of every coordinate), centred at any probability measure `μ`; `d < 2m` makes `η ↦ etaE m η μ`
continuous.  Route: `eqlaw_pathOf`, `eqlaw_aemeasurable_pathOf`, `eqlaw_continuous_ofMeasureDiff_empirical`. -/
theorem windowGibbs_aemeasurable {N : ℕ} (hN : 1 ≤ N) {m : ℝ} (hm : (d : ℝ) < 2 * m) (T u : ℝ)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : DynData d) (H : ℝ)
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (h : IsStrongSolution P D H X₀ W X) :
    AEMeasurable (windowGibbs m T u μ X) P := by
  have hη : Continuous fun Y : Config d N => etaE m Y μ :=
    (HRS.MD.EQLawPath.eqlaw_continuous_ofMeasureDiff_empirical hm μ hN).const_smul (Real.sqrt N)
  have heq : windowGibbs m T u μ X = fun ω => HRS.MD.EQLawPath.eqlaw_pathOf d m T (fun τ =>
      etaE m (X (Real.toNNReal (u + τ)) ω) μ) := by
    funext ω; rfl
  rw [heq]
  refine HRS.MD.EQLawPath.eqlaw_aemeasurable_pathOf P T _ (fun τ => ?_) ?_
  · exact hη.measurable.comp (h.adapted (Real.toNNReal (u + τ)))
  · filter_upwards [h.cont] with ω hω
    refine hη.comp ?_
    refine continuous_pi fun i => ?_
    exact (hω i).comp (continuous_real_toNNReal.comp (continuous_const.add continuous_subtype_val))

end HRS.ME.UIPathTight
