import HRS.MS.TiltAux11

/-!
# S4.7 packet P7: the feature-form conclusion for the tilted preparation

`s47_conclusion`: for `a, β, γ` in compact positive intervals, every `ε` with `IsTiltData d s a β ψ ε` and every summable feature
family, `StaticFieldConclusion` holds for `Q⁰ = s47_P = canonicalGibbs g V₀ N γ` (`= modulatedGibbs g N γ μ₀`), the centering
`ν = firstMarginal Q⁰` and every Gaussian `Zg` with the covariance of the statement; together with the bias bound
`|ν(f) - μ₀(f)| ≤ ‖f‖_∞ C_s δ_N` used by the mean-field clause.  (Copy of the feature form of S4.6 with the corrector of P2.)
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S47

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d : ℕ}

/-- **Feature form for the tilted preparation, uniform over the tilt class** (ED15R): `C, C_s` depend on `ε_*` only. -/
theorem s47_conclusion_unif (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (J : ℕ)
    (hJ : (d : ℝ) / 2 + 2 < J) (am ap βm βp γm γp : ℝ) (ham : 0 < am) (hβm : 0 < βm)
    (hγm : 0 < γm) (εstar : ℝ) :
    ∃ C Cs : ℝ, 0 ≤ Cs ∧ ∀ a ∈ Set.Icc am ap, ∀ β ∈ Set.Icc βm βp, ∀ γ ∈ Set.Icc γm γp, ∀ ε : ℝ,
      ∀ ψ : Euc d → ℝ, IsTiltData d s a β ψ ε → cbNorm (100 * d + 1001) (fun x => ε * ψ x) ≤ εstar → ∀ φ : ℕ → Euc d → ℝ, IsSummableFeatureFamily J φ → ∀ N, 2 ≤ N →
      ∀ Zg : Measure SeqL2, IsCenteredGaussianSeq Zg
        (fun i j => susceptibilityCov (rieszKernel d s) (tiltedMeasure d s a β ε ψ) γ (φ i) (φ j)) →
      StaticFieldConclusion d s N (s47_P d s (perturbedDensity (thermalDensity d s a β) ε ψ) γ N)
        (s47_nu d s (perturbedDensity (thermalDensity d s a β) ε ψ) γ N) J φ Zg C ∧
      (∀ f : Euc d → ℝ, Measurable f → ∀ Bf : ℝ, (∀ x, |f x| ≤ Bf) →
        |pair (s47_nu d s (perturbedDensity (thermalDensity d s a β) ε ψ) γ N) f -
          pair (tiltedMeasure d s a β ε ψ) f| ≤ Bf * (Cs * HRS.deltaN d s N)) ∧
      s47_P d s (perturbedDensity (thermalDensity d s a β) ε ψ) γ N =
        modulatedGibbs (rieszKernel d s) N γ (tiltedMeasure d s a β ε ψ) ∧
      IsProbDensity (perturbedDensity (thermalDensity d s a β) ε ψ) ∧
      IsProbabilityMeasure (s47_P d s (perturbedDensity (thermalDensity d s a β) ε ψ) γ N) := by
  by_cases hr : am ≤ ap ∧ βm ≤ βp ∧ γm ≤ γp
  swap
  · exact ⟨0, 0, le_rfl, fun a ha β hβ γ hγ => absurd ⟨ha.1.trans ha.2, hβ.1.trans hβ.2, hγ.1.trans hγ.2⟩ hr⟩
  obtain ⟨hap, hβp, hγp⟩ := hr
  obtain ⟨Cs, Ct, ct, BU, BB, KR, KT, hCs0, hKR, hKT, hsuAll⟩ :=
    s47_setup_unif hd hs0 hsd ham hβm hγm hap hβp hγp εstar
  obtain ⟨Cc, hCc0, hCc⟩ := s47_corrector_unif hd hs0 hsd J hJ am ap βm βp γm γp ham hβm hγm εstar
  have hJ1 : 1 ≤ J := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    have h2 : (2 : ℝ) < J := by linarith
    have h1 : (1 : ℝ) ≤ J := by linarith
    exact_mod_cast h1
  refine ⟨KR * Cc + γm⁻¹ * KT * Cc, Cs, hCs0, ?_⟩
  intro a ha β hβ γ hγ ε ψ hε hcb φ hφ N hN Zg hZg
  have ha0 : 0 < a := ham.trans_le ha.1
  have hβ0 : 0 < β := hβm.trans_le hβ.1
  have hγ0 : 0 < γ := hγm.trans_le hγ.1
  have hq : 0 < a * β := mul_pos ha0 hβ0
  obtain ⟨Bd, hsu⟩ := hsuAll a ha β hβ γ hγ ε ψ hε hcb
  set ρ : Euc d → ℝ := perturbedDensity (thermalDensity d s a β) ε ψ with hρdef
  have hex : ∀ i, ∃ χ, S47Feat d s ρ γ (φ i) χ (Cc * cbNorm J (φ i)) := fun i =>
    hCc a ha β hβ γ hγ ρ (Or.inr ⟨ε, ψ, hε, hcb, rfl⟩) (φ i) (hφ.1 i)
  choose χ hfeat using hex
  refine ⟨?_, fun f hf Bf hBf => s47_bias hsu.hT.prob (hsu.hS N hN) hf hBf,
    s47_P_eq (by omega) hs0 hsd hsu.hT.hc hsu.hT.C0 hsu.hT.prob hsu.hT.smooth.continuous hsu.hT.pos
      hsu.hT.h0 hγ0 N, hsu.hT.prob, (hsu.hS N hN).prob⟩
  haveI hZG : IsGaussian Zg := hZg.1.1
  have hN1 : 1 ≤ N := by omega
  haveI hP : IsProbabilityMeasure (s47_P d s ρ γ N) := (hsu.hS N hN).prob
  haveI hν : IsProbabilityMeasure (s47_nu d s ρ γ N) := s47_nu_prob hN hP
  set P := s47_P d s ρ γ N with hPdef
  set ν := s47_nu d s ρ γ N with hνdef
  set S := featureSum J φ with hSdef
  set δ' := Real.sqrt (HRS.deltaN d s N) with hδ'
  have hS0 : 0 ≤ S := tsum_nonneg fun i => HRS.MS.Tc5.tc5_cb_nonneg J (φ i)
  have hδ0 : 0 ≤ δ' := Real.sqrt_nonneg _
  set K0 : ℝ := KR * Cc + γ⁻¹ * KT * Cc with hK0
  have hKRC : 0 ≤ KR * Cc := mul_nonneg hKR hCc0
  have hKTC : 0 ≤ γ⁻¹ * KT * Cc := mul_nonneg (mul_nonneg (inv_nonneg.2 hγ0.le) hKT) hCc0
  have hKK : K0 ≤ KR * Cc + γm⁻¹ * KT * Cc := by
    have h1 : γ⁻¹ ≤ γm⁻¹ := inv_anti₀ hγm hγ.1
    have : γ⁻¹ * KT * Cc ≤ γm⁻¹ * KT * Cc :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hKT) hCc0
    linarith
  have hfm : Measurable (featureVec φ ν : EucConfig d N → SeqL2) :=
    s45_feature_measurable hN1 hφ
  have hXi : Integrable (fun w : EucConfig d N × SeqL2 => featureVec φ ν w.1) (P.prod Zg) :=
    Integrable.of_bound (C := 2 * Real.sqrt N * S) (hfm.comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => s45_featureVec_norm_le hN1 hφ w.1)
  have hγn : Integrable (fun z : SeqL2 => ‖z‖) Zg := (IsGaussian.integrable_id (μ := Zg)).norm
  have hGn : Integrable (fun w : EucConfig d N × SeqL2 => ‖w.2‖) (P.prod Zg) :=
    (measurePreserving_snd (μ := P) (ν := Zg)).integrable_comp_of_integrable hγn
  have hGauss : HRS.IsCenteredGaussian (HRS.law (P.prod Zg) (fun w : EucConfig d N × SeqL2 => w.2)) := by
    have : HRS.law (P.prod Zg) (fun w : EucConfig d N × SeqL2 => w.2) = Zg := s45_map_snd
    rw [this]; exact hZg.1
  have h4 : ∀ F : SeqL2 → ℝ, ContDiff ℝ 2 F → ∀ D₁ D₂ : ℝ, (∀ z, ‖fderiv ℝ F z‖ ≤ D₁) →
      (∀ z, ‖iteratedFDeriv ℝ 2 F z‖ ≤ D₂) →
      Integrable (fun X => F (featureVec φ ν X)) P ∧ Integrable F Zg ∧
      |∫ X, F (featureVec φ ν X) ∂P - ∫ z, F z ∂Zg| ≤ K0 * δ' * (S * D₁ + S ^ 2 * D₂) := by
    intro F hF D₁ D₂ hD₁ hD₂
    have hD₁0 : 0 ≤ D₁ := (norm_nonneg _).trans (hD₁ 0)
    have hD₂0 : 0 ≤ D₂ := (norm_nonneg _).trans (hD₂ 0)
    obtain ⟨k1, k2, k3⟩ := static_stein_hilbert (P.prod Zg) s45_seqBasis
      (fun w : EucConfig d N × SeqL2 => featureVec φ ν w.1) (fun w => w.2) hXi measurable_snd.aemeasurable
      hGauss (KR * Cc * S * δ') (γ⁻¹ * KT * Cc * S ^ 2 * δ')
      (fun n => s47_hfin hd hs0 hsd hq hγ0 hsu hN hJ1 hCc0 hφ hfeat hZg n)
      (s45_tail_tendsto (hfm.comp measurable_fst) hXi.norm)
      (s45_tail_tendsto measurable_snd hGn) F hF D₁ D₂ hD₁ hD₂
    have hgm : AEStronglyMeasurable (fun X => F (featureVec φ ν X)) P :=
      (hF.continuous.measurable.comp hfm).aestronglyMeasurable
    have hgm2 : AEStronglyMeasurable F Zg := hF.continuous.aestronglyMeasurable
    refine ⟨?_, ?_, ?_⟩
    · exact ((measurePreserving_fst (μ := P) (ν := Zg)).integrable_comp hgm).1 k1
    · exact ((measurePreserving_snd (μ := P) (ν := Zg)).integrable_comp hgm2).1 k2
    · rw [s45_integral_fst (γ := Zg) (g := fun X => F (featureVec φ ν X)) hgm,
        s45_integral_snd (P := P) (g := F) hgm2] at k3
      refine k3.trans ?_
      have t1 : 0 ≤ KR * Cc * δ' * S ^ 2 * D₂ := by positivity
      have t2 : 0 ≤ γ⁻¹ * KT * Cc * δ' * S * D₁ := by positivity
      have t3 : 0 ≤ γ⁻¹ * KT * Cc * δ' * S ^ 2 * D₂ := by positivity
      nlinarith
  have h4' : ∀ F : SeqL2 → ℝ, ContDiff ℝ 2 F → ∀ D₁ D₂ : ℝ, (∀ z, ‖fderiv ℝ F z‖ ≤ D₁) →
      (∀ z, ‖iteratedFDeriv ℝ 2 F z‖ ≤ D₂) →
      Integrable (fun X => F (featureVec φ ν X)) P ∧ Integrable F Zg ∧
      |∫ X, F (featureVec φ ν X) ∂P - ∫ z, F z ∂Zg| ≤
        (KR * Cc + γm⁻¹ * KT * Cc) * δ' * (S * D₁ + S ^ 2 * D₂) := by
    intro F hF D₁ D₂ hD₁ hD₂
    obtain ⟨k1, k2, k3⟩ := h4 F hF D₁ D₂ hD₁ hD₂
    refine ⟨k1, k2, k3.trans ?_⟩
    have hD₁0 : 0 ≤ D₁ := (norm_nonneg _).trans (hD₁ 0)
    have hD₂0 : 0 ≤ D₂ := (norm_nonneg _).trans (hD₂ 0)
    have h0 : 0 ≤ δ' * (S * D₁ + S ^ 2 * D₂) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hKK h0]
  refine ⟨s45_feature_memℓp hN1 hφ, hfm, ?_, fun F hF D₁ D₂ hD₁ hD₂ => h4' F hF D₁ D₂ hD₁ hD₂⟩
  have := s45_smoothDist_le (P := P) (γ := Zg) hfm (K := (KR * Cc + γm⁻¹ * KT * Cc) * δ') (A := S)
    (B := S ^ 2) (by
      have : 0 ≤ γm⁻¹ * KT * Cc := mul_nonneg (mul_nonneg (inv_nonneg.2 hγm.le) hKT) hCc0
      positivity) hS0 (by positivity)
    (fun F hF D₁ D₂ hD₁ hD₂ => (h4' F hF D₁ D₂ hD₁ hD₂).2.2)
  refine this.trans (le_of_eq ?_)
  ring

/-- **Feature form for the tilted preparation** (fixed `ψ`; a corollary of `s47_conclusion_unif`). -/
theorem s47_conclusion (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (J : ℕ)
    (hJ : (d : ℝ) / 2 + 2 < J) (am ap βm βp γm γp : ℝ) (ham : 0 < am) (hβm : 0 < βm)
    (hγm : 0 < γm) (ψ : Euc d → ℝ) :
    ∃ C Cs : ℝ, 0 ≤ Cs ∧ ∀ a ∈ Set.Icc am ap, ∀ β ∈ Set.Icc βm βp, ∀ γ ∈ Set.Icc γm γp, ∀ ε : ℝ,
      IsTiltData d s a β ψ ε → ∀ φ : ℕ → Euc d → ℝ, IsSummableFeatureFamily J φ → ∀ N, 2 ≤ N →
      ∀ Zg : Measure SeqL2, IsCenteredGaussianSeq Zg
        (fun i j => susceptibilityCov (rieszKernel d s) (tiltedMeasure d s a β ε ψ) γ (φ i) (φ j)) →
      StaticFieldConclusion d s N (s47_P d s (perturbedDensity (thermalDensity d s a β) ε ψ) γ N)
        (s47_nu d s (perturbedDensity (thermalDensity d s a β) ε ψ) γ N) J φ Zg C ∧
      (∀ f : Euc d → ℝ, Measurable f → ∀ Bf : ℝ, (∀ x, |f x| ≤ Bf) →
        |pair (s47_nu d s (perturbedDensity (thermalDensity d s a β) ε ψ) γ N) f -
          pair (tiltedMeasure d s a β ε ψ) f| ≤ Bf * (Cs * HRS.deltaN d s N)) ∧
      s47_P d s (perturbedDensity (thermalDensity d s a β) ε ψ) γ N =
        modulatedGibbs (rieszKernel d s) N γ (tiltedMeasure d s a β ε ψ) ∧
      IsProbDensity (perturbedDensity (thermalDensity d s a β) ε ψ) ∧
      IsProbabilityMeasure (s47_P d s (perturbedDensity (thermalDensity d s a β) ε ψ) γ N) := by
  obtain ⟨εstar, hε⟩ := HRS.MS.S48.s48_tilt_cb_star (d := d) ψ
  obtain ⟨C, Cs, hCs, h⟩ := s47_conclusion_unif hd hs0 hsd J hJ am ap βm βp γm γp ham hβm hγm εstar
  exact ⟨C, Cs, hCs, fun a ha β hβ γ hγ ε hε' => h a ha β hβ γ hγ ε ψ hε' (hε s a β ε hε')⟩

end S47

end
