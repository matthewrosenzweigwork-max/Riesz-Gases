import HRS.MC.CepN5Aux12
import HRS.MC.CepN5Aux13
import HRS.MC.CepN5Aux14

/-!
# Packet N5: the one-dimensional Bessel-type hitting estimate (relocated proof)

`cep_N5_bessel_hitting_proof` has the statement of the frozen spec theorem `HRS.MC.Cepa.cep_N5_bessel_hitting`
(with the duplicated `cep_scale`); see `HRS/MC/CepN5Tie.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.CepN5

open HRS

/-- Pure measure-theoretic bookkeeping of the final inequality. -/
theorem n5_final_arith {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {A E R T1 D A1 : Set Ω} {r1 r2 : ℝ} (hsub : A ⊆ E ∪ R ∪ T1 ∪ D) (hA1 : A1 ⊆ A)
    (hT1 : P.real T1 ≤ r1 * P.real A1) (hD : P.real D ≤ r2 * P.real A1) (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2) :
    (1 - r1 - r2) * P.real A - P.real R ≤ P.real E := by
  have h1 : P.real A ≤ P.real (E ∪ R ∪ T1 ∪ D) := measureReal_mono hsub
  have h2 : P.real (E ∪ R ∪ T1 ∪ D) ≤ P.real E + P.real R + P.real T1 + P.real D := by
    calc P.real (E ∪ R ∪ T1 ∪ D) ≤ P.real (E ∪ R ∪ T1) + P.real D := measureReal_union_le _ _
      _ ≤ (P.real (E ∪ R) + P.real T1) + P.real D := by
          gcongr; exact measureReal_union_le _ _
      _ ≤ ((P.real E + P.real R) + P.real T1) + P.real D := by
          gcongr; exact measureReal_union_le _ _
  have h3 : P.real A1 ≤ P.real A := measureReal_mono hA1
  have e1 : r1 * P.real A1 ≤ r1 * P.real A := mul_le_mul_of_nonneg_left h3 hr1
  have e2 : r2 * P.real A1 ≤ r2 * P.real A := mul_le_mul_of_nonneg_left h3 hr2
  nlinarith

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **N5 (one-dimensional Bessel-type hitting estimate)**, relocated proof. -/
theorem cep_N5_bessel_hitting_proof [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianFiltration P ℱ (fun t ω (_ : Fin 1) => B t ω))
    {G c : ℝ → Ω → ℝ} {κ σ C : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (hκσ : κ < σ ^ 2 / 2) (hC : 0 ≤ C)
    {ρ : Ω → WithTop ℝ} (hρ : IsStoppingTime ℱ ρ) {t₁ dur : ℝ} (ht₁ : 0 ≤ t₁) (hdur : 0 < dur)
    (hG : ∀ ω, Continuous fun t => G t ω) (hGad : ∀ t, 0 ≤ t → Measurable[ℱ t] (G t))
    (hc : ∀ u ω, |c u ω| ≤ C) (hcad : ∀ u, 0 ≤ u → Measurable[ℱ u] (c u))
    (hpos : ∀ᵐ ω ∂P, ∀ u ∈ Set.Icc t₁ (t₁ + dur), ((u : ℝ) : WithTop ℝ) ≤ ρ ω → 0 < G u ω)
    (hdyn : ∀ᵐ ω ∂P, ∀ s t : ℝ, t₁ ≤ s → s ≤ t → t ≤ t₁ + dur → ((t : ℝ) : WithTop ℝ) ≤ ρ ω →
      G t ω - G s ω = (∫ u in s..t, (κ / G u ω + c u ω)) + σ * (B (Real.toNNReal t) ω - B (Real.toNNReal s) ω))
    {ε δ : ℝ} (hε : 0 < ε) (hεC : C * ε ≤ κ) (hδ : 0 < δ) (hδε : δ < ε / 2)
    {A : Set Ω} (hA : MeasurableSet[ℱ t₁] A) (hA0 : ∀ ω ∈ A, 0 < G t₁ ω ∧ G t₁ ω ≤ ε / 2) :
    (1 - HRS.MC.CepN5b.cep_scale (2 * κ / σ ^ 2) (2 * C / σ ^ 2) (ε / 2) /
          HRS.MC.CepN5b.cep_scale (2 * κ / σ ^ 2) (2 * C / σ ^ 2) ε
        - ε ^ 2 / (σ ^ 2 * dur)) * (P A).toReal - (P (A ∩ {ω | ρ ω < ((t₁ + dur : ℝ) : WithTop ℝ)})).toReal
      ≤ (P (A ∩ {ω | ∃ u ∈ Set.Icc t₁ (t₁ + dur), ((u : ℝ) : WithTop ℝ) ≤ ρ ω ∧ G u ω ≤ δ})).toReal := by
  obtain ⟨t, rfl⟩ : ∃ t : ℝ≥0, (t : ℝ) = t₁ := ⟨t₁.toNNReal, Real.coe_toNNReal _ ht₁⟩
  have h : N5H P ℱ B G c κ σ C ρ t dur ε δ A :=
    ⟨hB, hκ, hσ, hC, hρ, hdur, hG, hGad, hc, hdyn, hε, hεC, hδ, hδε, hA, hA0⟩
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hθ : 2 * κ / σ ^ 2 < 1 := by
    rw [div_lt_one hσ2]; linarith
  have hlam : 0 ≤ 2 * C / σ ^ 2 := by positivity
  have hSb := n5_S_bound h hθ
  have hTb := n5_T_bound h
  have hSpos := n5_scale_pos hθ hlam hε
  have hSh : 0 ≤ HRS.MC.CepN5b.cep_scale (2 * κ / σ ^ 2) (2 * C / σ ^ 2) (ε / 2) :=
    n5_scale_nonneg hθ hlam (by linarith)
  have hsd : 0 < σ ^ 2 * dur := mul_pos hσ2 hdur
  have hsub : A ⊆ (A ∩ {ω | ∃ u ∈ Set.Icc (t : ℝ) ((t : ℝ) + dur), ((u : ℝ) : WithTop ℝ) ≤ ρ ω ∧ G u ω ≤ δ}) ∪
        (A ∩ {ω | ρ ω < (((t : ℝ) + dur : ℝ) : WithTop ℝ)}) ∪
        (n5_A1 G ρ t δ A ∩ {ω | ε ≤ n5_H G t (n5_tauR G ρ t δ ε dur A ω) ω}) ∪
        (n5_A1 G ρ t δ A ∩ {ω | dur ≤ n5_tauR G ρ t δ ε dur A ω}) := by
    intro ω hωA
    by_cases hω1 : ω ∈ n5_A1 G ρ t δ A
    · rcases n5_cover (ε := ε) hdur (hG ω) hω1 with h1 | h1 | h1 | h1
      · exact Or.inl (Or.inl (Or.inl ⟨hωA, h1⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨hωA, h1⟩))
      · exact Or.inl (Or.inr ⟨hω1, h1⟩)
      · exact Or.inr ⟨hω1, h1⟩
    · by_cases hρω : ((t : ℝ) : WithTop ℝ) ≤ ρ ω
      · have hGt : G t ω ≤ δ := by
          by_contra hlt
          exact hω1 ⟨⟨hωA, hρω⟩, not_le.1 hlt⟩
        refine Or.inl (Or.inl (Or.inl ⟨hωA, (t : ℝ), ⟨le_rfl, by linarith⟩, hρω, hGt⟩))
      · refine Or.inl (Or.inl (Or.inr ⟨hωA, ?_⟩))
        have h1 : ρ ω < ((t : ℝ) : WithTop ℝ) := not_le.1 hρω
        refine lt_of_lt_of_le h1 ?_
        exact_mod_cast (by linarith : (t : ℝ) ≤ (t : ℝ) + dur)
  have hT1 : P.real (n5_A1 G ρ t δ A ∩ {ω | ε ≤ n5_H G t (n5_tauR G ρ t δ ε dur A ω) ω}) ≤
      HRS.MC.CepN5b.cep_scale (2 * κ / σ ^ 2) (2 * C / σ ^ 2) (ε / 2) /
          HRS.MC.CepN5b.cep_scale (2 * κ / σ ^ 2) (2 * C / σ ^ 2) ε * P.real (n5_A1 G ρ t δ A) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hSpos]
    have : _ := hSb
    unfold Measure.real
    linarith
  have hD : P.real (n5_A1 G ρ t δ A ∩ {ω | dur ≤ n5_tauR G ρ t δ ε dur A ω}) ≤
      ε ^ 2 / (σ ^ 2 * dur) * P.real (n5_A1 G ρ t δ A) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hsd]
    have : _ := hTb
    unfold Measure.real
    linarith
  have hA1 : n5_A1 G ρ t δ A ⊆ A := fun ω hω => hω.1.1
  have key := n5_final_arith (P := P) hsub hA1 hT1 hD (div_nonneg hSh hSpos.le)
    (div_nonneg (sq_nonneg ε) hsd.le)
  simpa only [measureReal_def] using key

end HRS.MC.CepN5
