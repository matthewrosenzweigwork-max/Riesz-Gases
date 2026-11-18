import HRS.Main.A34Aux28

/-!
# Packet A34, helper 29: Proposition A.34 (ii), qualitative clause 1 (convergence in `H^{-γ'}`)
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A34

open HRS HRS.PDE HRS.PDE.ET HRS.A33 HRS.Main

variable {d : ℕ}

theorem a34_qual_one (s : ℝ) (Rg : Regime) (ν₀ MB Λ T VB : ℝ) (S : MainData d) (hs : S.s = s)
    (hT : S.T = T) (L : LimitCoeffs d)
    (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d + 2) (gammaIdx d))
    (νin : Measure (NegSobolev d (gammaIdx d : ℝ))) (hν : IsProbabilityMeasure νin)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    (νG : ℕ → Measure (NegSobolev d (gammaIdx d : ℝ)))
    (hνG : ∀ N : ℕ, 1 ≤ N →
      IsLinearFieldNoise (S.dyn N) (S.ρ N) (S.qN N) t (gammaIdx d : ℝ) (νG N))
    (νGlim : Measure (NegSobolev d (gammaIdx d : ℝ)))
    (hνGlim : IsLinearFieldNoise (L.dyn S) L.ρ L.invβstar t (gammaIdx d : ℝ) νGlim)
    {γ' : ℝ} (hγ : (gammaIdx d : ℝ) < γ') :
    ConvergesInLaw
      (fun N => (linearFieldLaw νin (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) id (νG N)).map
        (NegSobolev.embed γ'))
      ((limitFieldLaw S L (gammaIdx d : ℝ) νin t νGlim).map (NegSobolev.embed γ')) := by
  have hs0 : 0 ≤ s := hs ▸ S.hs0
  have hsd : s < d := hs ▸ S.hsd
  obtain ⟨Cg, hCg, hg'⟩ := a34_gauss_couple S.hd s hs0 hsd Rg ν₀ MB Λ VB T
  haveI := hν
  haveI := hνGlim.1
  haveI := InitialDataAux.negSobolev_secondCountable d (gammaIdx d : ℝ)
  haveI := InitialDataAux.negSobolev_secondCountable d γ'
  have hγle : (gammaIdx d : ℝ) ≤ γ' := hγ.le
  have he : Measurable (NegSobolev.embed γ' : NegSobolev d (gammaIdx d : ℝ) → NegSobolev d γ') :=
    a34_embed_meas hγle
  set u : ℕ → NegSobolev d (gammaIdx d : ℝ) → NegSobolev d (gammaIdx d : ℝ) :=
    fun N F => S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F with hu_def
  set u₀ : NegSobolev d (gammaIdx d : ℝ) → NegSobolev d (gammaIdx d : ℝ) :=
    fun F => L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F with hu₀_def
  have hu : ∀ N, 1 ≤ N → Measurable (u N) := fun N hN => by
    subst hT
    exact (a34_transport_meas S L Rg ν₀ MB Λ VB hcoef N hN ht).1.const_smul (S.AN N)
  have hu₀ : Measurable u₀ := by
    subst hT
    exact (a34_transport_meas S L Rg ν₀ MB Λ VB hcoef 1 le_rfl ht).2.const_smul L.A
  have hνp : ∀ N, 1 ≤ N → IsProbabilityMeasure (νG N) := fun N hN => (hνG N hN).1
  have hμp : ∀ N, 1 ≤ N → IsProbabilityMeasure (νin.map (u N)) := fun N hN =>
    (Measure.isProbabilityMeasure_map_iff (hu N hN).aemeasurable).2 hν
  haveI : IsProbabilityMeasure (νin.map u₀) :=
    (Measure.isProbabilityMeasure_map_iff hu₀.aemeasurable).2 hν
  -- convergence of the first factor
  have hμc : ConvergesInLaw (fun N => (νin.map (u N)).map (NegSobolev.embed γ'))
      ((νin.map u₀).map (NegSobolev.embed γ')) := by
    have h := a34_conv_of_pointwise (ν := νin)
      (fun N F => NegSobolev.embed γ' (u N F)) (fun F => NegSobolev.embed γ' (u₀ F))
      ((eventually_ge_atTop 1).mono fun N hN => he.comp (hu N hN)) (he.comp hu₀)
      (fun F => tendsto_iff_norm_sub_tendsto_zero.2
        (a34_field_pointwise s Rg ν₀ MB Λ T VB S hs hT L hcoef t ht F hγ))
    rw [Measure.map_map he hu₀]
    refine a34_converges_congr ?_ h
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (Measure.map_map he (hu N hN)).symm
  have hμ : ∀ N, 1 ≤ N → IsProbabilityMeasure ((νin.map (u N)).map (NegSobolev.embed γ')) :=
    fun N hN => by
      haveI := hμp N hN
      infer_instance
  haveI : IsProbabilityMeasure (νGlim.map (NegSobolev.embed γ')) :=
    inferInstance
  have hν' : ∀ N, 1 ≤ N → IsProbabilityMeasure ((νG N).map (NegSobolev.embed γ')) :=
    fun N hN => by
      haveI := hνp N hN
      infer_instance
  set Δ : ℕ → ℝ := fun N => S.coeffDiscrepancy L (gammaIdx d) N with hΔ
  have hε : Tendsto (fun N => Real.sqrt (Cg * (Δ N + Δ N ^ 2))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N => Cg * (Δ N + Δ N ^ 2)) atTop (𝓝 0) := by
      have := (hcoef.tendsto.add (hcoef.tendsto.pow 2)).const_mul Cg
      simpa using this
    have := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at this
    exact this
  have key := a34_converges_conv _ _ (fun N => (νG N).map (NegSobolev.embed γ'))
    (νGlim.map (NegSobolev.embed γ')) hμ hν' hμc
    (fun N => Real.sqrt (Cg * (Δ N + Δ N ^ 2))) hε ?_
  · have hlim : (limitFieldLaw S L (gammaIdx d : ℝ) νin t νGlim).map (NegSobolev.embed γ') =
        (νin.map u₀).map (NegSobolev.embed γ') ∗ νGlim.map (NegSobolev.embed γ') :=
      a34_map_conv_embed hγle (νin.map u₀) νGlim
    rw [hlim]
    refine a34_converges_congr ?_ key
    filter_upwards [eventually_ge_atTop 1] with N hN
    haveI := hμp N hN
    haveI := hνp N hN
    exact (a34_map_conv_embed hγle (νin.map (u N)) (νG N)).symm
  · intro N hN
    obtain ⟨Ω, mΩ, P, hP, G₁, G₂, hm₁, hm₂, hl₁, hl₂, hint, hbd⟩ :=
      hg' S L hs hT hcoef N hN t ht (νG N) νGlim (hνG N hN) hνGlim
    haveI := hP
    obtain ⟨hi1, hi2⟩ := a34_E_norm_le (hm₁.sub hm₂).aestronglyMeasurable hint
    have hdom : ∀ ω, ‖NegSobolev.embed γ' (G₁ ω) - NegSobolev.embed γ' (G₂ ω)‖ ≤
        ‖G₁ ω - G₂ ω‖ := fun ω => by
      rw [← a34_embed_sub hγle]
      exact NegSobolev.norm_embed_le γ' hγle _
    have hI : Integrable (fun ω => ‖NegSobolev.embed γ' (G₁ ω) - NegSobolev.embed γ' (G₂ ω)‖) P :=
      Integrable.mono' hi1 ((he.comp hm₁).sub (he.comp hm₂)).norm.aestronglyMeasurable
        (ae_of_all _ fun ω => by rw [norm_norm]; exact hdom ω)
    refine ⟨Ω, mΩ, P, hP, fun ω => NegSobolev.embed γ' (G₁ ω), fun ω => NegSobolev.embed γ' (G₂ ω),
      he.comp hm₁, he.comp hm₂, ?_, ?_, hI, ?_⟩
    · rw [← hl₁]; exact (Measure.map_map he hm₁).symm
    · rw [← hl₂]; exact (Measure.map_map he hm₂).symm
    · refine (integral_mono hI hi1 hdom).trans (hi2.trans (Real.sqrt_le_sqrt hbd))

end HRS.A34
