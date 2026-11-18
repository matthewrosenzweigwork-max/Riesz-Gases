import HRS.Main.A34Aux23

/-!
# Packet A34, helper 24: Proposition A.34 (ii), qualitative clause (transported initial laws converge)
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A34

open HRS HRS.PDE HRS.PDE.ET HRS.A33 HRS.Main

variable {d : ℕ}

theorem a34_qual_two (s : ℝ) (Rg : Regime) (ν₀ MB Λ T VB : ℝ) (S : MainData d) (hs : S.s = s)
    (hT : S.T = T) (L : LimitCoeffs d)
    (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d + 2) (gammaIdx d))
    (νin : Measure (NegSobolev d (gammaIdx d : ℝ))) (hν : IsProbabilityMeasure νin)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    (νG : ℕ → Measure (NegSobolev d (gammaIdx d : ℝ)))
    (hνG : ∀ N : ℕ, 1 ≤ N →
      IsLinearFieldNoise (S.dyn N) (S.ρ N) (S.qN N) t (gammaIdx d : ℝ) (νG N))
    (νGlim : Measure (NegSobolev d (gammaIdx d : ℝ)))
    (hνGlim : IsLinearFieldNoise (L.dyn S) L.ρ L.invβstar t (gammaIdx d : ℝ) νGlim) :
    ConvergesInLaw
        (fun N => law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
          S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F))
        (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
          L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F)) →
      ConvergesInLaw
        (fun N => linearFieldLaw νin (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) id (νG N))
        (limitFieldLaw S L (gammaIdx d : ℝ) νin t νGlim) := by
  intro hμc
  have hs0 : 0 ≤ s := hs ▸ S.hs0
  have hsd : s < d := hs ▸ S.hsd
  obtain ⟨Cg, hCg, hg'⟩ := a34_gauss_couple S.hd s hs0 hsd Rg ν₀ MB Λ VB T
  haveI := hν
  haveI := hνGlim.1
  haveI := InitialDataAux.negSobolev_secondCountable d (gammaIdx d : ℝ)
  have hmeas : ∀ N, 1 ≤ N → (Measurable fun F : NegSobolev d (gammaIdx d : ℝ) =>
      S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F) := fun N hN => by
    subst hT
    exact (a34_transport_meas S L Rg ν₀ MB Λ VB hcoef N hN ht).1.const_smul (S.AN N)
  have hmeas₂ : Measurable (fun F : NegSobolev d (gammaIdx d : ℝ) =>
      L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F) := by
    subst hT
    exact (a34_transport_meas S L Rg ν₀ MB Λ VB hcoef 1 le_rfl ht).2.const_smul L.A
  haveI : IsProbabilityMeasure (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
      L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F)) :=
    (Measure.isProbabilityMeasure_map_iff hmeas₂.aemeasurable).2 hν
  have hμ : ∀ N, 1 ≤ N → IsProbabilityMeasure (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
      S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F)) := fun N hN =>
    (Measure.isProbabilityMeasure_map_iff (hmeas N hN).aemeasurable).2 hν
  have hνp : ∀ N, 1 ≤ N → IsProbabilityMeasure (νG N) := fun N hN => (hνG N hN).1
  set Δ : ℕ → ℝ := fun N => S.coeffDiscrepancy L (gammaIdx d) N with hΔ
  have hΔ0 : ∀ N, 1 ≤ N → 0 ≤ Δ N := fun N hN =>
    (a34_delta_facts S L (gammaIdx d) N Rg ν₀ MB Λ VB
      (HRS.PDE.StabAux.adjointData_mono (by omega) (hcoef.seq_adjoint N hN))
      (HRS.PDE.StabAux.adjointData_mono (by omega) hcoef.limit_adjoint)).1
  have hε : Tendsto (fun N => Real.sqrt (Cg * (Δ N + Δ N ^ 2))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N => Cg * (Δ N + Δ N ^ 2)) atTop (𝓝 0) := by
      have := (hcoef.tendsto.add (hcoef.tendsto.pow 2)).const_mul Cg
      simpa using this
    have := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at this
    exact this
  have key := a34_converges_conv _ _ (fun N => νG N) νGlim hμ hνp hμc
    (fun N => Real.sqrt (Cg * (Δ N + Δ N ^ 2))) hε ?_
  · exact key
  · intro N hN
    obtain ⟨Ω, mΩ, P, hP, G₁, G₂, hm₁, hm₂, hl₁, hl₂, hint, hbd⟩ :=
      hg' S L hs hT hcoef N hN t ht (νG N) νGlim (hνG N hN) hνGlim
    haveI := hP
    obtain ⟨hi1, hi2⟩ := a34_E_norm_le (hm₁.sub hm₂).aestronglyMeasurable hint
    refine ⟨Ω, mΩ, P, hP, G₁, G₂, hm₁, hm₂, hl₁, hl₂, hi1, ?_⟩
    refine hi2.trans (Real.sqrt_le_sqrt ?_)
    exact hbd

end HRS.A34
