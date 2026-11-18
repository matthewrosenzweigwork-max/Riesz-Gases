import HRS.MH.MfclSpec
import HRS.MH.MfclA5A6

/-!
# Mfcl packet A7: proof of `HRS.MH.Mfcl.law_pathEval_windowFluc`
(law of the time-zero pairing of the window is the image of the Gibbs law by `linCoord`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.MfclP

open HRS HRS.Main HRS.LZ HRS.MD.EQ29

theorem law_pathEval_windowFluc_proof : type_of% @HRS.MH.Mfcl.law_pathEval_windowFluc := by
  intro d hd s hs0 hsd V hV β hβ N hN u T hu hT Ω _ P _ X₀ W X hX m hm ρβ hρβ hρs ℓ hℓ
  obtain ⟨hstat, hmeas, -⟩ := HRS.MD.EQInterp.flow_facts hd hs0 hsd V hV hβ hN P hX
  have hW : AEMeasurable (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ)) P :=
    windowFluc_aemeasurable_proof hd hs0 hsd V hV hβ hN hu hT P hX hm ρβ hρβ (Real.sqrt N)
  have hA6 := pathEval_windowFluc_ae_proof hd hs0 hsd V hV hβ hN hu hT P hX hm ρβ hρβ hρs ℓ hℓ
  have hℓm : Measurable ℓ := ℓ.continuous.measurable
  have hXu : Measurable (X (Real.toNNReal u)) := hmeas _
  have hψ : Measurable ρβ := hρβ.measurable
  have hlin : Measurable (linCoord (withDensityReal ρβ) ρβ : Config d N → ℝ) := by
    unfold linCoord
    fun_prop
  have hu' : ((Real.toNNReal u : ℝ≥0) : ℝ) ≤ u + T := by
    rw [Real.coe_toNNReal _ hu]
    linarith
  have hstat' := hstat (Real.toNNReal u) hu'
  have hae : (ℓ ∘ windowFluc m T u (Real.sqrt N) X (fun _ => ρβ)) =ᵐ[P]
      (linCoord (withDensityReal ρβ) ρβ ∘ X (Real.toNNReal u)) := by
    filter_upwards [hA6] with ω hω
    exact hω
  show (Measure.map (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ)) P).map ℓ = _
  rw [AEMeasurable.map_map_of_aemeasurable hℓm.aemeasurable hW, Measure.map_congr hae,
    ← hstat', Measure.map_map hlin hXu]

end HRS.MH.MfclP
