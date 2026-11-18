import HRS.Main.A34Aux21

/-!
# Packet A34, helper 22: Proposition A.34 (ii), quantitative (field part)
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A34

open HRS HRS.PDE HRS.PDE.ET HRS.A33 HRS.Main

variable {d : ℕ}

/-- measurability of the transported initial field map. -/
theorem a34_transport_meas (S : MainData d) (L : LimitCoeffs d) (Rg : Regime)
    (ν₀ MB Λ VB : ℝ) (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d + 2) (gammaIdx d))
    (N : ℕ) (hN : 1 ≤ N) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) :
    (Measurable fun F : NegSobolev d (gammaIdx d : ℝ) =>
      transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F) ∧
    (Measurable fun F : NegSobolev d (gammaIdx d : ℝ) =>
      transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F) := by
  obtain ⟨e⟩ := a33_exists_equiv S.hd
  have hm3 := ClassicalPart.three_le_mStar d
  have hγ : gammaIdx d = mStar d + d + 3 := rfl
  have hAN := HRS.PDE.StabAux.adjointData_mono (m' := gammaIdx d) (by omega) (hcoef.seq_adjoint N hN)
  have hAL := HRS.PDE.StabAux.adjointData_mono (m' := gammaIdx d) (by omega) hcoef.limit_adjoint
  let S₁ : A33Setup d := ⟨gammaIdx d, by omega, by omega, S.hd, Rg, MB, Λ, VB, ν₀, S.dyn N, S.T,
    S.ρ N, hAN⟩
  let S₂ : A33Setup d := ⟨gammaIdx d, by omega, by omega, S.hd, Rg, MB, Λ, VB, ν₀, L.dyn S, S.T,
    L.ρ, hAL⟩
  exact ⟨S₁.transport_measurable ht e, S₂.transport_measurable ht e⟩

/-- `E‖X‖ ≤ (E‖X‖²)^{1/2}` -/
theorem a34_E_norm_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {E : Type*} [NormedAddCommGroup E] {X : Ω → E} (hX : AEStronglyMeasurable X P)
    (h : Integrable (fun ω => ‖X ω‖ ^ 2) P) :
    Integrable (fun ω => ‖X ω‖) P ∧ ∫ ω, ‖X ω‖ ∂P ≤ Real.sqrt (∫ ω, ‖X ω‖ ^ 2 ∂P) := by
  have hm : MemLp (fun ω => ‖X ω‖) 2 P := by
    refine (memLp_two_iff_integrable_sq_norm hX.norm).2 ?_
    simpa [Real.norm_eq_abs, sq_abs] using h
  refine ⟨hm.integrable one_le_two, ?_⟩
  have := a33_integral_abs_le (P := P) (fun ω => ‖X ω‖) hm
  simpa [abs_of_nonneg (norm_nonneg _)] using this

theorem a34_sqrt_Δ_le (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    Real.sqrt (Δ + Δ ^ 2) ≤ Δ + Real.sqrt Δ := by
  have hs := Real.sqrt_nonneg Δ
  have hsq := Real.sq_sqrt hΔ
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [mul_nonneg hΔ hs]

theorem a34_field_main (s : ℝ) (Rg : Regime) (ν₀ MB Λ T VB Cs : ℝ) :
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : MainData d), S.s = s → S.T = T →
      ∀ (L : LimitCoeffs d),
        CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d + 2) (gammaIdx d) →
      ∀ (νin : Measure (NegSobolev d (gammaIdx d : ℝ))), IsProbabilityMeasure νin →
        (∀ N : ℕ, 1 ≤ N → ∀ t' ∈ Set.Icc (0 : ℝ) T,
          smoothDist 2
            (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
              S.AN N • transportField (S.dyn N) (S.ρ N) t' (gammaIdx d : ℝ) F))
            (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
              L.A • transportField (L.dyn S) L.ρ t' (gammaIdx d : ℝ) F)) ≤
            Cs * S.coeffDiscrepancy L (gammaIdx d) N) →
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ N : ℕ, 1 ≤ N →
      ∀ νG νGlim : Measure (NegSobolev d (gammaIdx d : ℝ)),
        IsLinearFieldNoise (S.dyn N) (S.ρ N) (S.qN N) t (gammaIdx d : ℝ) νG →
        IsLinearFieldNoise (L.dyn S) L.ρ L.invβstar t (gammaIdx d : ℝ) νGlim →
        smoothDist 2
          (linearFieldLaw νin (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) id νG)
          (limitFieldLaw S L (gammaIdx d : ℝ) νin t νGlim) ≤
        C * Real.exp (ΛT * t) *
          (S.coeffDiscrepancy L (gammaIdx d) N + Real.sqrt (S.coeffDiscrepancy L (gammaIdx d) N)) := by
  by_cases hg : 1 ≤ d ∧ 0 ≤ s ∧ s < d
  swap
  · exact ⟨1, 1, one_pos, one_pos, fun S hs _ => absurd ⟨S.hd, hs ▸ S.hs0, hs ▸ S.hsd⟩ hg⟩
  obtain ⟨hd, hs0, hsd⟩ := hg
  obtain ⟨Cg, hCg, hg'⟩ := a34_gauss_couple hd s hs0 hsd Rg ν₀ MB Λ VB T
  refine ⟨|Cs| + Real.sqrt Cg + 1, 1, by positivity, one_pos, ?_⟩
  intro S hs hT L hcoef νin hνin hinit t ht N hN νG νGlim hνG hνGlim
  obtain ⟨Ω, mΩ, P, hP, G₁, G₂, hm₁, hm₂, hl₁, hl₂, hint, hbd⟩ :=
    hg' S L hs hT hcoef N hN t ht νG νGlim hνG hνGlim
  subst hs hT
  haveI := hP
  haveI := InitialDataAux.negSobolev_secondCountable d (gammaIdx d : ℝ)
  haveI := hνG.1
  haveI := hνGlim.1
  obtain ⟨hmT₁, hmT₂⟩ := a34_transport_meas S L Rg ν₀ MB Λ VB hcoef N hN ht
  have hmA₁ : Measurable (fun F : NegSobolev d (gammaIdx d : ℝ) =>
      S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F) := hmT₁.const_smul (S.AN N)
  have hmA₂ : Measurable (fun F : NegSobolev d (gammaIdx d : ℝ) =>
      L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F) := hmT₂.const_smul L.A
  have hμ₁ : IsProbabilityMeasure (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
      S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F)) :=
    (Measure.isProbabilityMeasure_map_iff hmA₁.aemeasurable).2 hνin
  have hμ₂ : IsProbabilityMeasure (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
      L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F)) :=
    (Measure.isProbabilityMeasure_map_iff hmA₂.aemeasurable).2 hνin
  have hΔ0 : 0 ≤ S.coeffDiscrepancy L (gammaIdx d) N :=
    (a34_delta_facts S L (gammaIdx d) N Rg ν₀ MB Λ VB
      (HRS.PDE.StabAux.adjointData_mono (by omega) (hcoef.seq_adjoint N hN))
      (HRS.PDE.StabAux.adjointData_mono (by omega) hcoef.limit_adjoint)).1
  set Δ := S.coeffDiscrepancy L (gammaIdx d) N with hΔ
  unfold linearFieldLaw limitFieldLaw linearFieldLaw
  refine (a34_smoothDist_conv _ _ νG νGlim).trans ?_
  have h1 : smoothDist 2 (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
      S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F)) (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
      L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F)) ≤ Cs * Δ := hinit N hN t ht
  have h2 : smoothDist 2 νG νGlim ≤ ∫ ω, ‖G₁ ω - G₂ ω‖ ∂P := by
    rw [← hl₁, ← hl₂]
    exact a34_smoothDist_coupling P G₁ G₂ hm₁ hm₂ (a34_E_norm_le (hm₁.sub hm₂).aestronglyMeasurable hint).1
  have h3 : ∫ ω, ‖G₁ ω - G₂ ω‖ ∂P ≤ Real.sqrt (∫ ω, ‖G₁ ω - G₂ ω‖ ^ 2 ∂P) :=
    (a34_E_norm_le (hm₁.sub hm₂).aestronglyMeasurable hint).2
  have h4 : Real.sqrt (∫ ω, ‖G₁ ω - G₂ ω‖ ^ 2 ∂P) ≤ Real.sqrt Cg * (Δ + Real.sqrt Δ) := by
    refine (Real.sqrt_le_sqrt hbd).trans ?_
    rw [Real.sqrt_mul hCg.le]
    exact mul_le_mul_of_nonneg_left (a34_sqrt_Δ_le Δ hΔ0) (Real.sqrt_nonneg _)
  have hexp : 1 ≤ Real.exp (1 * t) := by rw [one_mul]; exact Real.one_le_exp ht.1
  have hΔs : 0 ≤ Δ + Real.sqrt Δ := by positivity
  have hfin : smoothDist 2 (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
      S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F)) (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
      L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F)) + smoothDist 2 νG νGlim ≤
      (|Cs| + Real.sqrt Cg + 1) * Real.exp (1 * t) * (Δ + Real.sqrt Δ) := by
    have e1 : Cs * Δ ≤ |Cs| * (Δ + Real.sqrt Δ) := by
      have := Real.sqrt_nonneg Δ
      calc Cs * Δ ≤ |Cs| * Δ := mul_le_mul_of_nonneg_right (le_abs_self _) hΔ0
        _ ≤ |Cs| * (Δ + Real.sqrt Δ) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    have hbase : smoothDist 2 (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
        S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F)) (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
        L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F)) + smoothDist 2 νG νGlim ≤
        (|Cs| + Real.sqrt Cg) * (Δ + Real.sqrt Δ) := by nlinarith [h1, h2, h3, h4, e1]
    calc _ ≤ (|Cs| + Real.sqrt Cg) * (Δ + Real.sqrt Δ) := hbase
      _ ≤ (|Cs| + Real.sqrt Cg + 1) * (Δ + Real.sqrt Δ) :=
          mul_le_mul_of_nonneg_right (by linarith) hΔs
      _ ≤ (|Cs| + Real.sqrt Cg + 1) * Real.exp (1 * t) * (Δ + Real.sqrt Δ) := by
          have : 0 ≤ (|Cs| + Real.sqrt Cg + 1) * (Δ + Real.sqrt Δ) := by positivity
          nlinarith [mul_nonneg this (sub_nonneg.2 hexp)]
  exact hfin

end HRS.A34
