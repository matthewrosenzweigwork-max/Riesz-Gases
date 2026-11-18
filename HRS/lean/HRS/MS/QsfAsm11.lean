import HRS.MS.QsfAsm10
import HRS.MS.ThCorr

/-!
# S4.5: proof of `quadratic_static_field`
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc cbNorm MemCb)

/-- **S4.5, feature form.** -/
theorem quadratic_static_field_proof : type_of% @HRS.Whole.quadratic_static_field := by
  intro d s hd hs0 hsd a β ha hβ J hJ
  obtain ⟨Cs, C₁, c, BU, KR, KT, hsu⟩ := s45_setup hd hs0 hsd ha hβ
  have hJ' : ((1 : ℕ) : ℝ) + 1 + (d : ℝ) / 2 < J := by push_cast; linarith
  obtain ⟨Cc₀, hCc⟩ := HRS.MS.Tc6.thermal_corrector_proof hd hs0 hsd 1 le_rfl J hJ' a a β β β β ha hβ hβ
  set Cc : ℝ := max Cc₀ 0 with hCcdef
  have hCc0 : 0 ≤ Cc := le_max_right _ _
  have hJ1 : 1 ≤ J := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    have h2 : (2 : ℝ) < J := by linarith
    have h1 : (1 : ℝ) ≤ J := by linarith
    exact_mod_cast h1
  refine ⟨KR * Cc + β⁻¹ * KT * Cc, ?_⟩
  intro φ hφ N hN γ hγ
  have hex : ∀ i, ∃ χ, IsThermalCorrector d s a β β 1 (φ i) (cbNorm J (φ i)) Cc₀ χ := fun i =>
    hCc a ⟨le_rfl, le_rfl⟩ β ⟨le_rfl, le_rfl⟩ β ⟨le_rfl, le_rfl⟩ (φ i) (hφ.1 i)
  choose χ hχ using hex
  have hfeat : ∀ i, S45Feat d s a β (φ i) (χ i) (Cc * cbNorm J (φ i)) := fun i =>
    (s45_feat_of_corrector (hχ i)).mono
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (HRS.MS.Tc5.tc5_cb_nonneg J (φ i)))
  haveI hγG : IsGaussian γ := hγ.1.1
  have hN1 : 1 ≤ N := by omega
  haveI hP : IsProbabilityMeasure (s45_P d s a β N) := (hsu.hS N hN).prob
  haveI hν : IsProbabilityMeasure (s45_nu d s a β N) := s45_nu_prob hN hP
  set P := s45_P d s a β N with hPdef
  set ν := s45_nu d s a β N with hνdef
  set S := featureSum J φ with hSdef
  set δ' := Real.sqrt (HRS.deltaN d s N) with hδ'
  have hS0 : 0 ≤ S := tsum_nonneg fun i => HRS.MS.Tc5.tc5_cb_nonneg J (φ i)
  have hδ0 : 0 ≤ δ' := Real.sqrt_nonneg _
  have hKRC : 0 ≤ KR * Cc := mul_nonneg hsu.hKR hCc0
  have hKTC : 0 ≤ β⁻¹ * KT * Cc := mul_nonneg (mul_nonneg (inv_nonneg.2 hβ.le) hsu.hKT) hCc0
  have hfm : Measurable (featureVec φ ν : EucConfig d N → SeqL2) :=
    s45_feature_measurable hN1 hφ
  have hXi : Integrable (fun w : EucConfig d N × SeqL2 => featureVec φ ν w.1) (P.prod γ) :=
    Integrable.of_bound (C := 2 * Real.sqrt N * S) (hfm.comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => s45_featureVec_norm_le hN1 hφ w.1)
  have hγn : Integrable (fun z : SeqL2 => ‖z‖) γ := (IsGaussian.integrable_id (μ := γ)).norm
  have hGn : Integrable (fun w : EucConfig d N × SeqL2 => ‖w.2‖) (P.prod γ) :=
    (measurePreserving_snd (μ := P) (ν := γ)).integrable_comp_of_integrable hγn
  have hGauss : HRS.IsCenteredGaussian (HRS.law (P.prod γ) (fun w : EucConfig d N × SeqL2 => w.2)) := by
    have : HRS.law (P.prod γ) (fun w : EucConfig d N × SeqL2 => w.2) = γ := s45_map_snd
    rw [this]; exact hγ.1
  have h4 : ∀ F : SeqL2 → ℝ, ContDiff ℝ 2 F → ∀ D₁ D₂ : ℝ, (∀ z, ‖fderiv ℝ F z‖ ≤ D₁) →
      (∀ z, ‖iteratedFDeriv ℝ 2 F z‖ ≤ D₂) →
      Integrable (fun X => F (featureVec φ ν X)) P ∧ Integrable F γ ∧
      |∫ X, F (featureVec φ ν X) ∂P - ∫ z, F z ∂γ| ≤
        (KR * Cc + β⁻¹ * KT * Cc) * δ' * (S * D₁ + S ^ 2 * D₂) := by
    intro F hF D₁ D₂ hD₁ hD₂
    have hD₁0 : 0 ≤ D₁ := (norm_nonneg _).trans (hD₁ 0)
    have hD₂0 : 0 ≤ D₂ := (norm_nonneg _).trans (hD₂ 0)
    obtain ⟨k1, k2, k3⟩ := static_stein_hilbert (P.prod γ) s45_seqBasis
      (fun w : EucConfig d N × SeqL2 => featureVec φ ν w.1) (fun w => w.2) hXi measurable_snd.aemeasurable
      hGauss (KR * Cc * S * δ') (β⁻¹ * KT * Cc * S ^ 2 * δ')
      (fun n => s45_hfin hd hs0 hsd ha hβ hsu hN hJ1 hCc0 hφ hfeat hγ n)
      (s45_tail_tendsto (hfm.comp measurable_fst) hXi.norm)
      (s45_tail_tendsto measurable_snd hGn) F hF D₁ D₂ hD₁ hD₂
    have hgm : AEStronglyMeasurable (fun X => F (featureVec φ ν X)) P :=
      (hF.continuous.measurable.comp hfm).aestronglyMeasurable
    have hgm2 : AEStronglyMeasurable F γ := hF.continuous.aestronglyMeasurable
    refine ⟨?_, ?_, ?_⟩
    · exact ((measurePreserving_fst (μ := P) (ν := γ)).integrable_comp hgm).1 k1
    · exact ((measurePreserving_snd (μ := P) (ν := γ)).integrable_comp hgm2).1 k2
    · rw [s45_integral_fst (γ := γ) (g := fun X => F (featureVec φ ν X)) hgm,
        s45_integral_snd (P := P) (g := F) hgm2] at k3
      refine k3.trans ?_
      have t1 : 0 ≤ KR * Cc * δ' * S ^ 2 * D₂ := by positivity
      have t2 : 0 ≤ β⁻¹ * KT * Cc * δ' * S * D₁ := by positivity
      have t3 : 0 ≤ β⁻¹ * KT * Cc * δ' * S ^ 2 * D₂ := by positivity
      nlinarith
  refine ⟨s45_feature_memℓp hN1 hφ, hfm, ?_, fun F hF D₁ D₂ hD₁ hD₂ => h4 F hF D₁ D₂ hD₁ hD₂⟩
  have := s45_smoothDist_le (P := P) (γ := γ) hfm (K := (KR * Cc + β⁻¹ * KT * Cc) * δ') (A := S)
    (B := S ^ 2) (by positivity) hS0 (by positivity)
    (fun F hF D₁ D₂ hD₁ hD₂ => (h4 F hF D₁ D₂ hD₁ hD₂).2.2)
  refine this.trans (le_of_eq ?_)
  ring

end S45

end
