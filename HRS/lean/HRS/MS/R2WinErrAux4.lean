import HRS.MS.R2WinErrAux3

/-!
# S10.4 packet E2b: the window trace error, abstract core (part (a) of `r2_window_errors`)

`s104_part_a_core`: pathwise bound (`s104_trace_pathwise`) with the feature scale `B_r² ≤ K θ_b(r)²`, integrated over `r ∈ [0,b+T]`
and the probability space with the weighted moment core (`s104_trace_moment_w`, `∫_0^{b+T}θ_b² ≤ T + 1/(2c)`):
`E ∫_0^{b+T} ‖C_r - C̄_r‖₁ dr ≤ 2 C_p q K (T + 1/(2c)) w_N`, `w_N = generalLocalizationRate d E₁ M₂ N`.
All particle/mean-field inputs are hypotheses of the form produced by `MovParticleBounds` (energy moment `E₁`, second moment `M₂`,
no collisions a.s.) and the class (`ρ^r ≤ Λ`, probability densities, second moments); the shared core for S10.4 and S10.5.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinErr

open HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

theorem s104_part_a_core (hd1 : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Λ : ℝ) :
    ∃ C₀min Cp : ℝ, 0 ≤ Cp ∧ ∀ C₀ : ℝ, C₀min ≤ C₀ → ∀ (m T b q c K M₂ : ℝ), 0 < c → 0 ≤ T → 0 ≤ b →
      0 ≤ q → 0 ≤ K → 0 ≤ M₂ → ∀ N : ℕ, 2 ≤ N →
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
      ∀ {E₁ : ℝ≥0∞}, E₁ ≠ ⊤ →
      (∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∫⁻ ζ, ENNReal.ofReal (rieszModulatedEnergy d s (X r.toNNReal ζ)
        (HRS.Whole.withDensityReal (ρ r)) + HRS.oN d s C₀ N) ∂P ≤ E₁) →
      (∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∫⁻ ζ, ENNReal.ofReal
        (secondMomentOf (HRS.Whole.empirical (X r.toNNReal ζ))) ∂P ≤ ENNReal.ofReal M₂) →
      ∀ (Γ : ℝ → Fin d → Euc d → KSpace d m T) (Br : ℝ → ℝ),
      (∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∀ a, ContDiff ℝ ((mStar d - 1 : ℕ) : WithTop ℕ∞) (Γ r a)) →
      (∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∀ a, ∀ j ≤ mStar d - 1, ∀ x,
        ‖iteratedFDeriv ℝ j (Γ r a) x‖ ≤ Br r) →
      (∀ r ∈ Set.Icc (0 : ℝ) (b + T), Br r ^ 2 ≤ K * s104_theta2 c b r) →
      ∀ (B₁ : ℝ → Ω → KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ)
        (B₂ : ℝ → KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ),
      (∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∀ ζ u v, B₁ r ζ u v = featureForm m T q (Γ r)
        (HRS.Whole.empirical (X r.toNNReal ζ)) u v) →
      (∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∀ u v, B₂ r u v = featureForm m T q (Γ r)
        (HRS.Whole.withDensityReal (ρ r)) u v) →
      ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) (b + T), ENNReal.ofReal (HRS.traceNormForm (B₁ r ζ - B₂ r))) ∂P ≤
        ENNReal.ofReal (2 * (Cp * q * K) * (1 / (2 * c) + T) *
          generalLocalizationRate d E₁.toReal M₂ N) := by
  obtain ⟨C₀min, Cp, hCp0, hpw⟩ := s104_trace_pathwise hd1 s hs0 hsd Λ
  refine ⟨C₀min, Cp, hCp0, fun C₀ hC0 m T b q c K M₂ hc hT hb hq hK hM₂ N hN Ω _ P _ X ρ hρ hinj
    hen hmm E₁ hE₁ hE hM Γ Br hΓ hB hBK B₁ B₂ h1 h2 => ?_⟩
  have hL : (0 : ℝ) ≤ b + T := by linarith
  have hW0 : 0 ≤ 1 / (2 * c) + T := by positivity
  have hfin := s104_trace_moment_w P d N (L := b + T) (s104_theta2 c b) (s104_theta2_measurable c b)
    hW0 (s104_theta2_lintegral hc hb hT) _ _ hen hmm hE₁ hE hM₂ hM
    (fun ζ r => HRS.MS.GenPath.s56_secondMoment_nonneg _)
    (c := Cp * q * K) (by positivity)
    (fun ζ r => ENNReal.ofReal (HRS.traceNormForm (B₁ r ζ - B₂ r))) ?_
  · refine hfin.trans (le_of_eq ?_)
    ring_nf
  · filter_upwards [hinj] with ζ hζ r hr R hR
    obtain ⟨hprob, hΛ, hmom, hm2⟩ := hρ r hr
    have hpwr := hpw C₀ hC0 m T q hq N hN (ρ r) hprob hΛ hmom (X r.toNNReal ζ) (hζ r hr) R hR
      (Γ r) (Br r) (hΓ r hr) (hB r hr) (B₁ r ζ) (B₂ r) (h1 r hr ζ) (h2 r hr)
    have hRpos : 0 < R := by linarith
    rw [← ENNReal.ofReal_mul (s104_theta2_pos c b r).le]
    refine ENNReal.ofReal_le_ofReal (hpwr.trans ?_)
    have e : -(1 : ℝ) / d = -(1 / (d : ℝ)) := by ring
    rw [e]
    have hmm0 := HRS.MS.GenPath.s56_secondMoment_nonneg (HRS.Whole.empirical (X r.toNNReal ζ))
    have hbr : Br r ^ 2 ≤ K * s104_theta2 c b r := hBK r hr
    have hErr : R ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 / (d : ℝ))) + Real.sqrt (rieszModulatedEnergy d s
          (X r.toNNReal ζ) (HRS.Whole.withDensityReal (ρ r)) + HRS.oN d s C₀ N)) +
        (secondMomentOf (HRS.Whole.empirical (X r.toNNReal ζ)) +
          secondMomentOf (HRS.Whole.withDensityReal (ρ r))) / R ^ 2 ≤
        R ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 / (d : ℝ))) + Real.sqrt (rieszModulatedEnergy d s
          (X r.toNNReal ζ) (HRS.Whole.withDensityReal (ρ r)) + HRS.oN d s C₀ N)) +
        (secondMomentOf (HRS.Whole.empirical (X r.toNNReal ζ)) + M₂) * (1 / R ^ 2) := by
      rw [← div_eq_mul_one_div]
      gcongr
    have hErr0 : 0 ≤ R ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 / (d : ℝ))) + Real.sqrt (rieszModulatedEnergy d s
          (X r.toNNReal ζ) (HRS.Whole.withDensityReal (ρ r)) + HRS.oN d s C₀ N)) +
        (secondMomentOf (HRS.Whole.empirical (X r.toNNReal ζ)) +
          secondMomentOf (HRS.Whole.withDensityReal (ρ r))) / R ^ 2 := by
      have := HRS.MS.GenPath.s56_secondMoment_nonneg (HRS.Whole.withDensityReal (ρ r))
      positivity
    have hq0 : 0 ≤ Cp * q := mul_nonneg hCp0 hq
    have hθ0 := (s104_theta2_pos c b r).le
    have key := mul_le_mul (mul_le_mul_of_nonneg_left hbr hq0) hErr hErr0
      (mul_nonneg hq0 (mul_nonneg hK hθ0))
    exact key.trans (le_of_eq (by ring))

end HRS.MS.R2WinErr
