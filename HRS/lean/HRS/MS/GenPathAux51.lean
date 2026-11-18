import HRS.MS.GenPathAux50

/-!
# S5.6 packet P9b: the abstract comparison with a prescribed initial path `Yc`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.Uniform

variable {d : ℕ}

theorem s56_compare (m T : ℝ) (hT : 0 ≤ T) :
    ∃ Cs Cw1 Cw2 : ℝ, 0 ≤ Cs ∧ 0 ≤ Cw1 ∧ 0 ≤ Cw2 ∧
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ mΩ) (k0 : Ω → KSpace d m T), Measurable[ℱ 0] k0 →
      ∀ (M : ℝ → Ω → KSpace d m T) (Sg : ℝ → Ω → (KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ)),
      IsHilbertMartingaleWithCovariation P ℱ T M Sg → (∀ t, Measurable (M t)) →
      ∀ (G : ℝ → Ω → KSpace d m T) (Cb : ℝ → (KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ)),
      IsDetCovDensity T Cb → IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => Cb r) →
      (∀ t, Measurable (G t)) →
      ∀ (Sd : ℝ → Ω → (KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ)) (cost : ℝ → Ω → ℝ),
      IsHilbertMartingaleWithCovariation P ℱ T (fun τ ζ => M (min τ T) ζ - G (min τ T) ζ)
        (fun r ζ => if r ≤ T then Sd r ζ else 0) →
      (∀ᵐ ζ ∂P, ∀ r : ℝ, 0 ≤ r → r ≤ T → traceNormForm (Sd r ζ) ≤ cost r ζ) →
      (∀ᵐ ζ ∂P, ContinuousOn (fun t => M t ζ) (Set.Icc 0 T)) → (∀ᵐ ζ ∂P, M 0 ζ = 0) →
      (∀ᵐ ζ ∂P, ContinuousOn (fun t => G t ζ) (Set.Icc 0 T)) → (∀ᵐ ζ ∂P, G 0 ζ = 0) →
      ∀ (R : ℝ → Ω → OscDual d m), (∀ᵐ ζ ∂P, ContinuousOn (fun t => R t ζ) (Set.Icc 0 T)) →
      (∀ t, Measurable (R t)) → ∀ (Ξ Yc : Ω → OscPath d m T),
      AEMeasurable Ξ P → AEMeasurable Yc P →
      AEMeasurable (fun ζ => windowPathOf m T 0 (fun t => (k0 ζ).evalA t + reconstructPath m T G ζ t)) P →
      (∀ᵐ ζ ∂P, Ξ ζ = windowPathOf m T 0
        (fun t => (k0 ζ).evalA t + reconstructPath m T M ζ t + R t ζ)) →
      (ENNReal.ofReal (smoothDist 2 (law P Ξ) (law P Yc)) ≤
        ENNReal.ofReal Cs * ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T,
          ENNReal.ofReal (traceNormForm (Sg r ζ - Cb r))) ∂P +
        ∫⁻ ζ, ‖windowPathOf m T 0 (fun t => R t ζ)‖ₑ ∂P +
        ∫⁻ ζ, ‖windowPathOf m T 0 (fun t => (k0 ζ).evalA t + reconstructPath m T G ζ t) - Yc ζ‖ₑ ∂P) ∧
      (wassersteinE 1 (law P Ξ) (law P Yc) ≤
        ENNReal.ofReal Cw1 * (∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ζ)) ∂P) ^ (1 / 2 : ℝ) +
        (∫⁻ ζ, ‖windowPathOf m T 0 (fun t => R t ζ)‖ₑ ^ (1 : ℝ) ∂P) ^ (1 / (1 : ℝ)) +
        (∫⁻ ζ, ENNReal.ofReal (‖windowPathOf m T 0 (fun t => (k0 ζ).evalA t + reconstructPath m T G ζ t) -
          Yc ζ‖ ^ (1 : ℝ)) ∂P) ^ (1 / (1 : ℝ))) ∧
      (wassersteinE 2 (law P Ξ) (law P Yc) ≤
        ENNReal.ofReal Cw2 * (∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ζ)) ∂P) ^ (1 / 2 : ℝ) +
        (∫⁻ ζ, ‖windowPathOf m T 0 (fun t => R t ζ)‖ₑ ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) +
        (∫⁻ ζ, ENNReal.ofReal (‖windowPathOf m T 0 (fun t => (k0 ζ).evalA t + reconstructPath m T G ζ t) -
          Yc ζ‖ ^ (2 : ℝ)) ∂P) ^ (1 / (2 : ℝ))) := by
  obtain ⟨Cs, hCs0, hCs⟩ := s56_smooth_abstract (d := d) m T hT
  obtain ⟨Cw1, hCw10, hCw1⟩ := s56_wasserstein_abstract (d := d) m T hT 1 (Or.inl rfl)
  obtain ⟨Cw2, hCw20, hCw2⟩ := s56_wasserstein_abstract (d := d) m T hT 2 (Or.inr rfl)
  refine ⟨Cs, Cw1, Cw2, hCs0, hCw10, hCw20, ?_⟩
  intro Ω mΩ P hP ℱ k0 hk0 M Sg hM hMm G Cb hCb hG hGm Sd cost hdiff hcost hMc hM0 hGc hG0 R hRc hRm Ξ Yc
    hΞm hYcm hYhm hΞ
  set Yh : Ω → OscPath d m T := fun ζ => windowPathOf m T 0
    (fun t => (k0 ζ).evalA t + reconstructPath m T G ζ t) with hYh
  have : IsProbabilityMeasure (law P Ξ) := (Measure.isProbabilityMeasure_map_iff hΞm).2 inferInstance
  have : IsProbabilityMeasure (law P Yc) := (Measure.isProbabilityMeasure_map_iff hYcm).2 inferInstance
  have : IsProbabilityMeasure (law P Yh) := (Measure.isProbabilityMeasure_map_iff hYhm).2 inferInstance
  refine ⟨?_, ?_, ?_⟩
  · have h1 := hCs Ω P ℱ k0 hk0 M Sg hM hMm G Cb hCb hG hGm R hRc hRm Ξ Yh hΞ
      (Filter.Eventually.of_forall fun ζ => rfl)
    have h2 := s56_smoothDist_coupling_ae P Yh Yc hYhm hYcm
    have h3 := smoothDist_triangle 2 (law P Ξ) (law P Yh) (law P Yc)
    calc ENNReal.ofReal (smoothDist 2 (law P Ξ) (law P Yc))
        ≤ ENNReal.ofReal (smoothDist 2 (law P Ξ) (law P Yh) + smoothDist 2 (law P Yh) (law P Yc)) :=
          ENNReal.ofReal_le_ofReal h3
      _ = ENNReal.ofReal (smoothDist 2 (law P Ξ) (law P Yh)) +
          ENNReal.ofReal (smoothDist 2 (law P Yh) (law P Yc)) :=
          ENNReal.ofReal_add (smoothDist_nonneg _ _ _) (smoothDist_nonneg _ _ _)
      _ ≤ _ := add_le_add h1 h2
  · have h1 := hCw1 Ω P ℱ k0 (hk0.mono (ℱ.le 0) le_rfl) M G hMm hGm Sd cost hdiff hcost hMc hM0 hGc hG0 R hRc hRm Ξ Yh hΞ
      (Filter.Eventually.of_forall fun ζ => rfl)
    have h2 := wassersteinE_le_of_coupling P 1 le_rfl Yh Yc hYhm hYcm
    have h3 := wassersteinE_triangle 1 le_rfl (law P Ξ) (law P Yh) (law P Yc)
    exact h3.trans (add_le_add h1 h2)
  · have h1 := hCw2 Ω P ℱ k0 (hk0.mono (ℱ.le 0) le_rfl) M G hMm hGm Sd cost hdiff hcost hMc hM0 hGc hG0 R hRc hRm Ξ Yh hΞ
      (Filter.Eventually.of_forall fun ζ => rfl)
    have h2 := wassersteinE_le_of_coupling P 2 (by norm_num) Yh Yc hYhm hYcm
    have h3 := wassersteinE_triangle 2 (by norm_num) (law P Ξ) (law P Yh) (law P Yc)
    exact h3.trans (add_le_add h1 h2)

end HRS.MS.GenPath
