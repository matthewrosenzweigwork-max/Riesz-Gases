import HRS.MS.R2GenInitAux4

/-!
# S10.5 packet G0''': the covariance clause with realization-dependent energy and second-moment bounds

`s105_partA`: `s104_partA` without the conversion to `localizationRate`: for any realization-dependent bounds `E ≥ 0`, `M₂ ≥ 0`
(energy moment `E`, second moments `M₂`) the covariance error satisfies
`E ∫_0^{b+T} ‖Bt_r‖₁ dr ≤ C_a · generalLocalizationRate d E M₂ N` with `C_a` independent of the realization (S L8478-8481).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2GenInit

open HRS.Whole HRS.Whole.AppendixA HRS.MS.R2WinErr

variable {d : ℕ}

theorem s105_partA (hd1 : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Λ : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∀ (T c q K : ℝ), 0 < c → 0 ≤ T → 0 ≤ q → 0 ≤ K →
      ∃ CTa : ℝ, 0 ≤ CTa ∧ ∀ (m b : ℝ), 0 ≤ b → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : ℝ≥0 → Ω → EucConfig d N) (ρ : ℝ → Euc d → ℝ) (Ev M₂ : ℝ), 0 ≤ Ev → 0 ≤ M₂ →
      (∀ r ∈ Set.Icc (0 : ℝ) (b + T), HRS.Whole.IsProbDensity (ρ r) ∧ (∀ x, ρ r x ≤ Λ) ∧
        Integrable (fun x => ‖x‖ ^ 2 * ρ r x) ∧ secondMomentOf (HRS.Whole.withDensityReal (ρ r)) ≤ M₂) →
      (∀ᵐ ζ ∂P, ∀ r ∈ Set.Icc (0 : ℝ) (b + T), Function.Injective (X r.toNNReal ζ)) →
      AEMeasurable (fun p : Ω × ℝ => rieszModulatedEnergy d s (X p.2.toNNReal p.1)
        (HRS.Whole.withDensityReal (ρ p.2)) + HRS.oN d s C₀ N)
        (P.prod (volume.restrict (Set.Icc 0 (b + T)))) →
      AEMeasurable (fun p : Ω × ℝ => secondMomentOf (HRS.Whole.empirical (X p.2.toNNReal p.1)))
        (P.prod (volume.restrict (Set.Icc 0 (b + T)))) →
      (∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∫⁻ ζ, ENNReal.ofReal (rieszModulatedEnergy d s (X r.toNNReal ζ)
        (HRS.Whole.withDensityReal (ρ r)) + HRS.oN d s C₀ N) ∂P ≤ ENNReal.ofReal Ev) →
      (∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∫⁻ ζ, ENNReal.ofReal
        (secondMomentOf (HRS.Whole.empirical (X r.toNNReal ζ))) ∂P ≤ ENNReal.ofReal M₂) →
      ∀ (Γ : ℝ → Fin d → Euc d → KSpace d m T) (Br : ℝ → ℝ),
      (∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∀ a, ContDiff ℝ ((mStar d - 1 : ℕ) : WithTop ℕ∞) (Γ r a)) →
      (∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∀ a, ∀ j ≤ mStar d - 1, ∀ x,
        ‖iteratedFDeriv ℝ j (Γ r a) x‖ ≤ Br r) →
      (∀ r ∈ Set.Icc (0 : ℝ) (b + T), Br r ^ 2 ≤ K * s104_theta2 c b r) →
      ∃ Bt : ℝ → Ω → KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ,
        (∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∀ ζ u v, Bt r ζ u v = featureForm m T q (Γ r)
            (HRS.Whole.empirical (X r.toNNReal ζ)) u v -
          featureForm m T q (Γ r) (HRS.Whole.withDensityReal (ρ r)) u v) ∧
        ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) (b + T), ENNReal.ofReal (HRS.traceNormForm (Bt r ζ))) ∂P ≤
          ENNReal.ofReal (CTa * generalLocalizationRate d Ev M₂ N) := by
  obtain ⟨C₀min, Cp, hCp0, hcore⟩ := s104_part_a_core hd1 s hs0 hsd Λ
  refine ⟨C₀min, fun C₀ hC₀m T c q K hc hT hq hK => ?_⟩
  refine ⟨2 * (Cp * q * K) * (1 / (2 * c) + T), by positivity, ?_⟩
  intro m b hb N hN Ω _ P _ X ρ Ev M₂ hEv hM₂ hρ hinj hen hmm hE hM Γ Br hΓ hB hBK
  have hone : ∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∀ a, ∀ x, ‖Γ r a x‖ ≤ Br r := by
    intro r hr a x
    have := hB r hr a 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero] at this
  have hBr0 : ∀ r ∈ Set.Icc (0 : ℝ) (b + T), 0 ≤ Br r := fun r hr =>
    (norm_nonneg _).trans (hone r hr ⟨0, by omega⟩ 0)
  have hmeasΓ : ∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∀ a, Measurable (Γ r a) := fun r hr a =>
    (hΓ r hr a).continuous.measurable
  have hex₁ : ∀ (r : ℝ) (ζ : Ω), ∃ F : KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ,
      r ∈ Set.Icc (0 : ℝ) (b + T) → ∀ u v, F u v = featureForm m T q (Γ r)
        (HRS.Whole.empirical (X r.toNNReal ζ)) u v := by
    intro r ζ
    by_cases hr : r ∈ Set.Icc (0 : ℝ) (b + T)
    · have : IsProbabilityMeasure (HRS.Whole.empirical (X r.toNNReal ζ)) :=
        HRS.Whole.empirical_isProbabilityMeasure (by omega) _
      obtain ⟨F, hF⟩ := s104_featureForm_clm q (Γ r) (HRS.Whole.empirical (X r.toNNReal ζ))
        (hBr0 r hr) (hmeasΓ r hr) (hone r hr)
      exact ⟨F, fun _ => hF⟩
    · exact ⟨0, fun h => absurd h hr⟩
  have hex₂ : ∀ r : ℝ, ∃ F : KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ,
      r ∈ Set.Icc (0 : ℝ) (b + T) → ∀ u v, F u v = featureForm m T q (Γ r)
        (HRS.Whole.withDensityReal (ρ r)) u v := by
    intro r
    by_cases hr : r ∈ Set.Icc (0 : ℝ) (b + T)
    · have : IsProbabilityMeasure (HRS.Whole.withDensityReal (ρ r)) :=
        Q09A.measure_isProb (hρ r hr).1
      obtain ⟨F, hF⟩ := s104_featureForm_clm q (Γ r) (HRS.Whole.withDensityReal (ρ r))
        (hBr0 r hr) (hmeasΓ r hr) (hone r hr)
      exact ⟨F, fun _ => hF⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose B₁ hB₁ using hex₁
  choose B₂ hB₂ using hex₂
  have hmain := hcore C₀ hC₀m m T b q c K M₂ hc hT hb hq hK hM₂ N hN P X ρ hρ hinj hen hmm
    (E₁ := ENNReal.ofReal Ev) ENNReal.ofReal_ne_top hE hM Γ Br hΓ hB hBK B₁ B₂
    (fun r hr ζ u v => hB₁ r ζ hr u v) (fun r hr u v => hB₂ r hr u v)
  refine ⟨fun r ζ => B₁ r ζ - B₂ r, fun r hr ζ u v => ?_, ?_⟩
  · simp only [ContinuousLinearMap.sub_apply, hB₁ r ζ hr, hB₂ r hr]
  · refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [ENNReal.toReal_ofReal hEv]

end HRS.MS.R2GenInit
