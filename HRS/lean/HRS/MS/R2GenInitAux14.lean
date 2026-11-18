import HRS.MS.R2GenInitAux13

/-!
# S10.5 window comparison, packet A3: the abstract window comparison with a prescribed initial path `Yc`

`S105WinCompareHyp m T Cs Cw` and `s105_win_compare`: the conclusion of the master comparison (smooth and `W_1`), with constants independent of
the window start `b ≥ 0` (analogue of `S56CompareHyp`, `s56_compare'`): the particle window is `A(k₀) + 𝒯M_b + R` and the target `Yc` is any path,
the price being `E‖A(k₀) + 𝒯G_b - Yc‖`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.GenPath HRS.MS.U9

variable {d : ℕ}

/-- The conclusion of `s105_win_compare` for fixed constants. -/
def S105WinCompareHyp (m T Cs Cw : ℝ) : Prop :=
  ∀ (b : ℝ), 0 ≤ b → ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (k0 : Ω → KSpace d m T), Measurable[ℱ 0] k0 →
    ∀ (M : ℝ → Ω → KSpace d m T) (Sg : ℝ → Ω → (KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ)),
    IsHilbertMartingaleWithCovariation P ℱ (b + T) M Sg → (∀ t, Measurable (M t)) →
    ∀ (G : ℝ → Ω → KSpace d m T) (Cb : ℝ → (KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ)),
    IsDetCovDensity (b + T) Cb → IsHilbertMartingaleWithCovariation P ℱ (b + T) G (fun r _ => Cb r) →
    (∀ t, Measurable (G t)) →
    ∀ (Sd : ℝ → Ω → (KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ)) (cost : ℝ → Ω → ℝ),
    IsHilbertMartingaleWithCovariation P ℱ (b + T) (fun τ ζ => M (min τ (b + T)) ζ - G (min τ (b + T)) ζ)
      (fun r ζ => if r ≤ b + T then Sd r ζ else 0) →
    (∀ᵐ ζ ∂P, ∀ r : ℝ, 0 ≤ r → r ≤ b + T → traceNormForm (Sd r ζ) ≤ cost r ζ) →
    (∀ᵐ ζ ∂P, ContinuousOn (fun t => M t ζ) (Set.Icc 0 (b + T))) → (∀ᵐ ζ ∂P, M 0 ζ = 0) →
    (∀ᵐ ζ ∂P, ContinuousOn (fun t => G t ζ) (Set.Icc 0 (b + T))) → (∀ᵐ ζ ∂P, G 0 ζ = 0) →
    ∀ (R : ℝ → Ω → OscDual d m), (∀ᵐ ζ ∂P, ContinuousOn (fun t => R t ζ) (Set.Icc 0 T)) →
    (∀ t, Measurable (R t)) → ∀ (Ξ Yc : Ω → OscPath d m T),
    AEMeasurable Ξ P → AEMeasurable Yc P →
    AEMeasurable (fun ζ => windowPathOf m T 0
      (fun t => (k0 ζ).evalA t + reconstructPath m T (fun τ ζ => G (b + τ) ζ) ζ t)) P →
    (∀ᵐ ζ ∂P, Ξ ζ = windowPathOf m T 0
      (fun t => (k0 ζ).evalA t + reconstructPath m T (fun τ ζ => M (b + τ) ζ) ζ t + R t ζ)) →
    (ENNReal.ofReal (smoothDist 2 (law P Ξ) (law P Yc)) ≤
      ENNReal.ofReal Cs * ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) (b + T),
        ENNReal.ofReal (traceNormForm (Sg r ζ - Cb r))) ∂P +
      ∫⁻ ζ, ‖windowPathOf m T 0 (fun t => R t ζ)‖ₑ ∂P +
      ∫⁻ ζ, ‖windowPathOf m T 0 (fun t => (k0 ζ).evalA t +
        reconstructPath m T (fun τ ζ => G (b + τ) ζ) ζ t) - Yc ζ‖ₑ ∂P) ∧
    (wassersteinE 1 (law P Ξ) (law P Yc) ≤
      ENNReal.ofReal Cw * (∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) (b + T), ENNReal.ofReal (cost r ζ)) ∂P) ^ (1 / 2 : ℝ) +
      ∫⁻ ζ, ‖windowPathOf m T 0 (fun t => R t ζ)‖ₑ ∂P +
      ∫⁻ ζ, ‖windowPathOf m T 0 (fun t => (k0 ζ).evalA t +
        reconstructPath m T (fun τ ζ => G (b + τ) ζ) ζ t) - Yc ζ‖ₑ ∂P)

theorem s105_win_compare (m T : ℝ) (hT : 0 < T) :
    ∃ Cs Cw : ℝ, 0 ≤ Cs ∧ 0 ≤ Cw ∧ S105WinCompareHyp (d := d) m T Cs Cw := by
  obtain ⟨Cs, hCs0, hCs⟩ := s105_smooth_abstract (d := d) m T hT
  obtain ⟨Cw, hCw0, hCw⟩ := s105_w1_abstract (d := d) m T hT
  refine ⟨Cs, Cw, hCs0, hCw0, ?_⟩
  intro b hb Ω mΩ P hP ℱ k0 hk0 M Sg hM hMm G Cb hCb hG hGm Sd cost hdiff hcost hMc hM0 hGc hG0 R hRc hRm Ξ Yc
    hΞm hYcm hYhm hΞ
  set Yh : Ω → OscPath d m T := fun ζ => windowPathOf m T 0
    (fun t => (k0 ζ).evalA t + reconstructPath m T (fun τ ζ => G (b + τ) ζ) ζ t) with hYh
  have : IsProbabilityMeasure (law P Ξ) := (Measure.isProbabilityMeasure_map_iff hΞm).2 inferInstance
  have : IsProbabilityMeasure (law P Yc) := (Measure.isProbabilityMeasure_map_iff hYcm).2 inferInstance
  have : IsProbabilityMeasure (law P Yh) := (Measure.isProbabilityMeasure_map_iff hYhm).2 inferInstance
  refine ⟨?_, ?_⟩
  · have h1 := hCs b hb Ω P ℱ k0 hk0 M Sg hM hMm G Cb hCb hG hGm R hRc hRm Ξ Yh hΞ
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
  · have h1 := hCw b hb Ω P ℱ k0 M G hMm hGm Sd cost hdiff hcost hMc hM0 hGc hG0 R hRc hRm Ξ Yh hΞ
      (Filter.Eventually.of_forall fun ζ => rfl) (hk0.mono (ℱ.le 0) le_rfl)
    have h2 := wassersteinE_le_of_coupling P 1 le_rfl Yh Yc hYhm hYcm
    have h3 := wassersteinE_triangle 1 le_rfl (law P Ξ) (law P Yh) (law P Yc)
    have h2' : wassersteinE 1 (law P Yh) (law P Yc) ≤ ∫⁻ ζ, ‖Yh ζ - Yc ζ‖ₑ ∂P := by
      refine h2.trans (le_of_eq ?_)
      simp only [div_one, ENNReal.rpow_one, Real.rpow_one]
      exact lintegral_congr fun ζ => ofReal_norm _
    exact h3.trans (by rw [add_assoc]; exact add_le_add h1 h2' |>.trans_eq (by rw [add_assoc]))

end HRS.MS.R2GenInit
