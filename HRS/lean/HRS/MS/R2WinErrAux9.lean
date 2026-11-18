import HRS.MS.R2WinErrAux8

/-!
# S10.4 packet E2d: part (a) of `r2_window_errors` as a conditional statement on a feature family

`s104_partA`: the existence of the forms `Bt` (as continuous bilinear forms, for `r ∈ [0,b+T]`) together with the integrated trace bound
`E ∫_0^{b+T} ‖Bt_r‖₁ dr ≤ C_T w_N` with the explicit `w_N = localizationRate d s C₀ N`, for any feature family `Γ_r` with derivative bounds
`≤ B_r`, `B_r² ≤ K θ_b(r)²` and the particle / mean-field inputs of `MovParticleBounds` (energy moment, second moments, injectivity, measurability).
The window features `r2WindowFeature` enter only through the hypotheses `hΓ, hB, hBK` (packet E1).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinErr

open HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

lemma s104_oN_nonneg (d : ℕ) (s C₀ : ℝ) (hC₀ : 0 ≤ C₀) (N : ℕ) : 0 ≤ HRS.oN d s C₀ N := by
  unfold HRS.oN
  have h1 : 0 ≤ C₀ * (N : ℝ) ^ (s / d - 1) := mul_nonneg hC₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have h2 : 0 ≤ (if s = 0 then Real.log N / (2 * d * N) else 0) := by
    split_ifs
    · rcases Nat.eq_zero_or_pos N with h | h
      · subst h; simp
      · have : (1 : ℝ) ≤ N := by exact_mod_cast h
        have := Real.log_nonneg this
        positivity
    · exact le_rfl
  linarith

theorem s104_partA (hd1 : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Λ : ℝ) :
    ∃ C₀min : ℝ, 0 ≤ C₀min ∧ ∀ C₀ : ℝ, C₀min ≤ C₀ → ∀ (T c q K Cen M₂ : ℝ), 0 < c → 0 ≤ T →
      0 ≤ q → 0 ≤ K → 0 ≤ Cen → 0 ≤ M₂ → ∃ CT : ℝ, ∀ (m b : ℝ), 0 ≤ b → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : ℝ≥0 → Ω → EucConfig d N) (ρ : ℝ → Euc d → ℝ),
      (∀ r ∈ Set.Icc (0 : ℝ) (b + T), HRS.Whole.IsProbDensity (ρ r) ∧ (∀ x, ρ r x ≤ Λ) ∧
        Integrable (fun x => ‖x‖ ^ 2 * ρ r x) ∧ secondMomentOf (HRS.Whole.withDensityReal (ρ r)) ≤ M₂) →
      (∀ᵐ ζ ∂P, ∀ r ∈ Set.Icc (0 : ℝ) (b + T), Function.Injective (X r.toNNReal ζ)) →
      AEMeasurable (fun p : Ω × ℝ => rieszModulatedEnergy d s (X p.2.toNNReal p.1)
        (HRS.Whole.withDensityReal (ρ p.2)) + HRS.oN d s C₀ N)
        (P.prod (volume.restrict (Set.Icc 0 (b + T)))) →
      AEMeasurable (fun p : Ω × ℝ => secondMomentOf (HRS.Whole.empirical (X p.2.toNNReal p.1)))
        (P.prod (volume.restrict (Set.Icc 0 (b + T)))) →
      (∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∫⁻ ζ, ENNReal.ofReal (rieszModulatedEnergy d s (X r.toNNReal ζ)
        (HRS.Whole.withDensityReal (ρ r)) + HRS.oN d s C₀ N) ∂P ≤
          ENNReal.ofReal (Cen * HRS.oN d s C₀ N)) →
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
          ENNReal.ofReal (CT * localizationRate d s C₀ N) := by
  obtain ⟨C₀min, Cp, hCp0, hcore⟩ := s104_part_a_core hd1 s hs0 hsd Λ
  refine ⟨max C₀min 0, le_max_right _ _, fun C₀ hC₀ T c q K Cen M₂ hc hT hq hK hCen hM₂ => ?_⟩
  have hC₀0 : 0 ≤ C₀ := (le_max_right _ _).trans hC₀
  have hC₀m : C₀min ≤ C₀ := (le_max_left _ _).trans hC₀
  obtain ⟨Cg, hCg0, hCg⟩ := s104_glr_le d hd1 s hs0 hsd C₀ Cen M₂ hC₀0 hCen hM₂
  refine ⟨2 * (Cp * q * K) * (1 / (2 * c) + T) * Cg, ?_⟩
  intro m b hb N hN Ω _ P _ X ρ hρ hinj hen hmm hE hM Γ Br hΓ hB hBK
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
    · haveI : IsProbabilityMeasure (HRS.Whole.empirical (X r.toNNReal ζ)) :=
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
    · haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal (ρ r)) :=
        Q09A.measure_isProb (hρ r hr).1
      obtain ⟨F, hF⟩ := s104_featureForm_clm q (Γ r) (HRS.Whole.withDensityReal (ρ r))
        (hBr0 r hr) (hmeasΓ r hr) (hone r hr)
      exact ⟨F, fun _ => hF⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose B₁ hB₁ using hex₁
  choose B₂ hB₂ using hex₂
  have hEne : ENNReal.ofReal (Cen * HRS.oN d s C₀ N) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmain := hcore C₀ hC₀m m T b q c K M₂ hc hT hb hq hK hM₂ N hN P X ρ hρ hinj hen hmm hEne hE hM
    Γ Br hΓ hB hBK B₁ B₂ (fun r hr ζ u v => hB₁ r ζ hr u v) (fun r hr u v => hB₂ r hr u v)
  refine ⟨fun r ζ => B₁ r ζ - B₂ r, fun r hr ζ u v => ?_, ?_⟩
  · simp only [ContinuousLinearMap.sub_apply, hB₁ r ζ hr, hB₂ r hr]
  · refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
    have hoN0 := s104_oN_nonneg d s C₀ hC₀0 N
    rw [ENNReal.toReal_ofReal (mul_nonneg hCen hoN0)]
    have hc0 : 0 ≤ 2 * (Cp * q * K) * (1 / (2 * c) + T) := by positivity
    calc 2 * (Cp * q * K) * (1 / (2 * c) + T) * generalLocalizationRate d (Cen * HRS.oN d s C₀ N) M₂ N
        ≤ 2 * (Cp * q * K) * (1 / (2 * c) + T) * (Cg * localizationRate d s C₀ N) :=
          mul_le_mul_of_nonneg_left (hCg N hN) hc0
      _ = _ := by ring

end HRS.MS.R2WinErr
