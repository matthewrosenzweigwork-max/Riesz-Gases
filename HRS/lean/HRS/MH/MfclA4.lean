import HRS.MH.MfclSpec
import HRS.MD.EQInterpWin
import HRS.Sections.AdjKGlueAux7

/-!
# Mfcl packet A4: proof of `HRS.MH.Mfcl.windowFluc_at'_ae` (a.s. pointwise value of the window)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.MfclP

theorem windowFluc_at'_ae_proof : type_of% @HRS.MH.Mfcl.windowFluc_at'_ae := by
  intro d hd s hs0 hsd V hV β hβ N hN u T hu hT Ω _ P _ X₀ W X hX m hm ρβ hρβ σ
  have hNpos : 1 ≤ N := by omega
  obtain ⟨-, -, hcont⟩ := HRS.MD.EQInterp.flow_facts hd hs0 hsd V hV hβ hN P hX
  haveI := HRS.isProb_withDensityReal hρβ
  filter_upwards [hcont] with ω hω
  intro τ
  have hc : Continuous fun τ' : Set.Icc (0 : ℝ) T =>
      σ • NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal u + Real.toNNReal (τ' : ℝ)) ω))
        (withDensityReal ρβ) := by
    refine Continuous.const_smul ?_ σ
    refine (HRS.MD.EQLawPath.eqlaw_continuous_ofMeasureDiff_empirical hm (withDensityReal ρβ) hNpos).comp ?_
    refine continuous_pi fun i => ?_
    exact (hω i).comp (continuous_const.add (continuous_real_toNNReal.comp continuous_subtype_val))
  exact HRS.AdjK.adjkg_flucPath_at m T σ (fun t => X (Real.toNNReal u + t)) (fun _ => ρβ) ω hc τ

end HRS.MH.MfclP
