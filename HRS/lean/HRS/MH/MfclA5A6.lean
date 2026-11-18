import HRS.MH.MfclSpec
import HRS.MH.MfclA4
import HRS.MD.EQInterpWin
import HRS.MD.EQLawZeta

/-!
# Mfcl packets A5 and A6: measurability of the window and its time-zero pairing
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.MfclP

open HRS HRS.Main HRS.LZ HRS.MD.EQ29

theorem windowFluc_aemeasurable_proof : type_of% @HRS.MH.Mfcl.windowFluc_aemeasurable := by
  intro d hd s hs0 hsd V hV β hβ N hN u T hu hT Ω _ P _ X₀ W X hX m hm ρβ hρβ σ
  have hNpos : 1 ≤ N := by omega
  obtain ⟨-, hmeas, hcont⟩ := HRS.MD.EQInterp.flow_facts hd hs0 hsd V hV hβ hN P hX
  haveI := HRS.isProb_withDensityReal hρβ
  have heq : HRS.Main.windowFluc m T u σ X (fun _ => ρβ) = fun ω =>
      HRS.MD.EQLawPath.eqlaw_pathOf d m T (fun τ =>
        σ • NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal u + Real.toNNReal (τ : ℝ)) ω))
          (withDensityReal ρβ)) := by
    funext ω
    rfl
  rw [heq]
  refine HRS.MD.EQLawPath.eqlaw_aemeasurable_pathOf P T _ (fun τ => ?_) ?_
  · have hc : Continuous fun x : Config d N =>
        σ • NegSobolev.ofMeasureDiff m (empirical x) (withDensityReal ρβ) :=
      Continuous.const_smul (HRS.MD.EQLawPath.eqlaw_continuous_ofMeasureDiff_empirical hm
        (withDensityReal ρβ) hNpos) σ
    exact hc.measurable.comp (hmeas _)
  · filter_upwards [hcont] with ω hω
    refine Continuous.const_smul ?_ σ
    refine (HRS.MD.EQLawPath.eqlaw_continuous_ofMeasureDiff_empirical hm (withDensityReal ρβ) hNpos).comp ?_
    refine continuous_pi fun i => ?_
    exact (hω i).comp (continuous_const.add (continuous_real_toNNReal.comp continuous_subtype_val))

theorem pathEval_windowFluc_ae_proof : type_of% @HRS.MH.Mfcl.pathEval_windowFluc_ae := by
  intro d hd s hs0 hsd V hV β hβ N hN u T hu hT Ω _ P _ X₀ W X hX m hm ρβ hρβ hρs ℓ hℓ
  have hNpos : 0 < N := by omega
  haveI := HRS.isProb_withDensityReal hρβ
  have hsmul : ∀ (c : ℝ) (F : NegSobolev d m) (φ : Torus d → ℝ),
      NegSobolev.eval (c • F) φ = c * NegSobolev.eval F φ := by
    intro c F φ
    have hc : ∀ k : NonzeroLattice d,
        NegSobolev.fourierCoeff (c • F) k = c * NegSobolev.fourierCoeff F k := by
      intro k
      simp only [NegSobolev.fourierCoeff]
      have : NegSobolev.coord (c • F) k = c * NegSobolev.coord F k := rfl
      rw [this]
      ring
    unfold NegSobolev.eval
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by rw [hc k]; ring
  have hA4 := HRS.MH.MfclP.windowFluc_at'_ae_proof hd hs0 hsd V hV hβ hN hu hT P hX hm ρβ hρβ
    (Real.sqrt N)
  filter_upwards [hA4] with ω hω
  have h0 := hω ⟨0, Set.left_mem_Icc.2 hT⟩
  have hx : Real.toNNReal u + Real.toNNReal ((⟨0, Set.left_mem_Icc.2 hT⟩ : Set.Icc (0 : ℝ) T) : ℝ) =
      Real.toNNReal u := by
    simp
  rw [hx] at h0
  haveI := empirical_isProbabilityMeasure hNpos (X (Real.toNNReal u) ω)
  rw [hℓ, h0, hsmul, NegSobolev.eval_ofMeasureDiff hm _ _ ρβ hρs, pair_empirical hNpos]
  unfold linCoord
  rw [one_div]

end HRS.MH.MfclP
