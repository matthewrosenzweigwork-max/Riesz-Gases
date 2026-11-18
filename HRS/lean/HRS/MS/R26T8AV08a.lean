import HRS.MS.CritForceAssemblyMaj
import HRS.MS.S82P2Mom

/-!
# S8.2 observed-time layer, packet T8A.V08a: initial-density change preserves the independent noise product law

If the initial variable `Y` and the noise `W` are independent under `P`, and `nu ≪ P.map Y` is a probability measure,
then the reweighted measure `P.withDensity (nu.rnDeriv (P.map Y) ∘ Y)` is a probability measure whose image under
`w ↦ (Y w, W w)` is the product `nu ⊗ P.map W`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A

theorem r26t8a_initial_reweight {Omega E B : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    [MeasurableSpace B] (P : Measure Omega) [IsProbabilityMeasure P] (Y : Omega → E) (W : Omega → B)
    (hY : Measurable Y) (hW : Measurable W) (hind : IndepFun Y W P)
    (nu : Measure E) [IsProbabilityMeasure nu] (hnu : nu ≪ P.map Y) :
    let r := fun w => nu.rnDeriv (P.map Y) (Y w)
    IsProbabilityMeasure (P.withDensity r) ∧
      (P.withDensity r).map (fun w => (Y w, W w)) = nu.prod (P.map W) := by
  intro r
  have hρm : Measurable (fun e => nu.rnDeriv (P.map Y) e) := Measure.measurable_rnDeriv nu (P.map Y)
  -- the initial marginal: `∫ 1_s(Y) ρ(Y) dP = nu s`
  have hkey : ∀ s : Set E, MeasurableSet s →
      ∫⁻ w, s.indicator (fun e => nu.rnDeriv (P.map Y) e) (Y w) ∂P = nu s := by
    intro s hs
    rw [← lintegral_map (hρm.indicator hs) hY, lintegral_indicator hs]
    exact Measure.setLIntegral_rnDeriv hnu s
  have htot : ∫⁻ w, r w ∂P = 1 := by
    show ∫⁻ w, nu.rnDeriv (P.map Y) (Y w) ∂P = 1
    rw [← lintegral_map hρm hY, Measure.lintegral_rnDeriv hnu]
    simp
  refine ⟨⟨?_⟩, ?_⟩
  · rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact htot
  · symm
    apply Measure.prod_eq
    intro s t hs ht
    have hpre : MeasurableSet ((fun w => (Y w, W w)) ⁻¹' (s ×ˢ t)) :=
      (hY.prodMk hW) (hs.prod ht)
    rw [Measure.map_apply (hY.prodMk hW) (hs.prod ht), withDensity_apply _ hpre,
      ← lintegral_indicator hpre]
    have hfac : (((fun w => (Y w, W w)) ⁻¹' (s ×ˢ t)).indicator r) =
        fun w => s.indicator (fun e => nu.rnDeriv (P.map Y) e) (Y w) *
          t.indicator (fun _ => (1 : ℝ≥0∞)) (W w) := by
      funext w
      by_cases h1 : Y w ∈ s <;> by_cases h2 : W w ∈ t <;> simp [Set.indicator, h1, h2, r]
    rw [hfac]
    have hind' : IndepFun (fun w => s.indicator (fun e => nu.rnDeriv (P.map Y) e) (Y w))
        (fun w => t.indicator (fun _ => (1 : ℝ≥0∞)) (W w)) P :=
      hind.comp (hρm.indicator hs) (measurable_const.indicator ht)
    have hmul : ∫⁻ w, s.indicator (fun e => nu.rnDeriv (P.map Y) e) (Y w) *
        t.indicator (fun _ => (1 : ℝ≥0∞)) (W w) ∂P =
        (∫⁻ w, s.indicator (fun e => nu.rnDeriv (P.map Y) e) (Y w) ∂P) *
          ∫⁻ w, t.indicator (fun _ => (1 : ℝ≥0∞)) (W w) ∂P :=
      lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
        ((hρm.indicator hs).comp hY) ((measurable_const.indicator ht).comp hW) hind'
    dsimp only
    rw [hmul]
    rw [hkey s hs, ← lintegral_map (measurable_const.indicator ht) hW, lintegral_indicator_const ht, one_mul]

end HRS.MS.R26T8A

end
