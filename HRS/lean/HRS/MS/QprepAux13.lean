import HRS.MS.QprepAux12

/-!
# S4.6 packet A13: proof of `quadratic_preparation_static` (feature form)
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S46

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

/-- **S4.6, feature form.** -/
theorem quadratic_preparation_static_proof : type_of% @HRS.Whole.quadratic_preparation_static := by
  intro d s hd hs0 hsd J hJ am ap βm βp γm γp ham hβm hγm
  by_cases hr : am ≤ ap ∧ βm ≤ βp ∧ γm ≤ γp
  swap
  · exact ⟨0, fun a ha β hβ γ hγ => absurd ⟨ha.1.trans ha.2, hβ.1.trans hβ.2, hγ.1.trans hγ.2⟩ hr⟩
  obtain ⟨hap, hβp, hγp⟩ := hr
  obtain ⟨Cs, Ct, ct, BU, KR, KT, hCs0, hKR, hKT, hsuAll⟩ :=
    s46_setup hd hs0 hsd ham hβm hγm hap hβp hγp
  have hJ' : ((1 : ℕ) : ℝ) + 1 + (d : ℝ) / 2 < J := by push_cast; linarith
  obtain ⟨Cc₀, hCc⟩ := HRS.MS.Tc6.thermal_corrector_proof hd hs0 hsd 1 le_rfl J hJ' am ap βm βp γm γp
    ham hβm hγm
  set Cc : ℝ := max Cc₀ 0 with hCcdef
  have hCc0 : 0 ≤ Cc := le_max_right _ _
  have hJ1 : 1 ≤ J := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    have h2 : (2 : ℝ) < J := by linarith
    have h1 : (1 : ℝ) ≤ J := by linarith
    exact_mod_cast h1
  refine ⟨KR * Cc + γm⁻¹ * KT * Cc, ?_⟩
  intro a ha β hβ γ hγ φ hφ N hN Zg hZg
  have ha0 : 0 < a := ham.trans_le ha.1
  have hβ0 : 0 < β := hβm.trans_le hβ.1
  have hγ0 : 0 < γ := hγm.trans_le hγ.1
  have hsu := hsuAll a ha β hβ γ hγ
  have hex : ∀ i, ∃ χ, IsThermalCorrector d s a β γ 1 (φ i) (cbNorm J (φ i)) Cc₀ χ := fun i =>
    hCc a ha β hβ γ hγ (φ i) (hφ.1 i)
  choose χ hχ using hex
  have hfeat : ∀ i, S46Feat d s a β γ (φ i) (χ i) (Cc * cbNorm J (φ i)) := fun i =>
    (s46_feat_of_corrector (hχ i)).mono
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (HRS.MS.Tc5.tc5_cb_nonneg J (φ i)))
  haveI hZG : IsGaussian Zg := hZg.1.1
  have hN1 : 1 ≤ N := by omega
  haveI hP : IsProbabilityMeasure (s46_P d s a β γ N) := (hsu.hS N hN).prob
  haveI hν : IsProbabilityMeasure (s46_nu d s a β γ N) := s46_nu_prob hN hP
  rw [← s46_P_eq hd hs0 hsd ha0 hβ0 hγ0 N]
  set P := s46_P d s a β γ N with hPdef
  set ν := s46_nu d s a β γ N with hνdef
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
      (fun n => s46_hfin hd hs0 hsd ha0 hβ0 hγ0 hsu hN hJ1 hCc0 hφ hfeat hZg n)
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

end S46

end
