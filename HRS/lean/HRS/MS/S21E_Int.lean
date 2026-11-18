import HRS.Whole.HeadlineStatement

/-!
# S2.1(iii) packet G3: spatial integrability of the cross-density terms

`χ/ρ ∈ L²(μ)` with `μ = ρ dx` finite gives (Lemma cross) the absolute integrability of
* `(∇f_i·∇f_j) χ_k` for bounded gradients (noise term of `cubicFormula`),
* `h(x,y) χ_j(x) χ_k(y)` for a kernel `h ∈ L²(μ ⊗ μ)` (commutator term).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S21E

open HRS HRS.Whole

variable {d : ℕ}

/-- Integrability against `ρ dx` is integrability of `ρ G` against `dx` (for a measurable positive `ρ`). -/
theorem s21e_integrable_density {ρ : Euc d → ℝ} (hρm : Measurable ρ) (hρ : ∀ x, 0 < ρ x) {G : Euc d → ℝ} :
    Integrable G (HRS.Whole.withDensityReal ρ) ↔ Integrable (fun x => ρ x * G x) (volume : Measure (Euc d)) := by
  unfold HRS.Whole.withDensityReal
  rw [integrable_withDensity_iff_integrable_smul' (hρm.ennreal_ofReal)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integrable_congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (hρ x).le]

/-- **G3a.**  The noise term: a bounded (a.e. strongly measurable) factor times `χ`, `χ/ρ ∈ L²(μ)`, `μ` finite. -/
theorem s21e_noise_integrable {ρ : Euc d → ℝ} (hρm : Measurable ρ) (hρ : ∀ x, 0 < ρ x)
    [IsFiniteMeasure (HRS.Whole.withDensityReal ρ)] {χ g : Euc d → ℝ}
    (hχ : MemLp (fun x => χ x / ρ x) 2 (HRS.Whole.withDensityReal ρ)) (C : ℝ) (hgb : ∀ x, ‖g x‖ ≤ C)
    (hgm : AEStronglyMeasurable g volume) :
    Integrable (fun x => g x * χ x) (volume : Measure (Euc d)) := by
  have hμ : HRS.Whole.withDensityReal ρ ≪ (volume : Measure (Euc d)) := withDensity_absolutelyContinuous _ _
  have hgm' : AEStronglyMeasurable g (HRS.Whole.withDensityReal ρ) := hgm.mono_ac hμ
  have hL : MemLp (fun x => g x * (χ x / ρ x)) 2 (HRS.Whole.withDensityReal ρ) := by
    refine MemLp.of_le_mul (c := C) hχ (hgm'.mul hχ.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hgb x) (norm_nonneg _)
  have hI : Integrable (fun x => g x * (χ x / ρ x)) (HRS.Whole.withDensityReal ρ) :=
    hL.integrable (by norm_num)
  have := (s21e_integrable_density hρm hρ).1 hI
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  have : ρ x ≠ 0 := (hρ x).ne'
  field_simp

/-- **G3b.**  The commutator term: a kernel in `L²(μ⊗μ)` times `χ₁(x) χ₂(y)`, `χ_i/ρ ∈ L²(μ)`. -/
theorem s21e_pair_integrable {ρ : Euc d → ℝ} (hρm : Measurable ρ) (hρ : ∀ x, 0 < ρ x) [IsFiniteMeasure (HRS.Whole.withDensityReal ρ)] {χ₁ χ₂ : Euc d → ℝ}
    (h₁ : MemLp (fun x => χ₁ x / ρ x) 2 (HRS.Whole.withDensityReal ρ))
    (h₂ : MemLp (fun x => χ₂ x / ρ x) 2 (HRS.Whole.withDensityReal ρ))
    {K : Euc d → Euc d → ℝ}
    (hK : MemLp (fun p : Euc d × Euc d => K p.1 p.2) 2
      ((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ))) :
    Integrable (fun p : Euc d × Euc d => K p.1 p.2 * χ₁ p.1 * χ₂ p.2) (volume : Measure (Euc d × Euc d)) := by
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hsq₁ : Integrable (fun x => (χ₁ x / ρ x) ^ 2) μ := h₁.integrable_sq
  have hsq₂ : Integrable (fun x => (χ₂ x / ρ x) ^ 2) μ := h₂.integrable_sq
  have hprod : Integrable (fun p : Euc d × Euc d => (χ₁ p.1 / ρ p.1) ^ 2 * (χ₂ p.2 / ρ p.2) ^ 2) (μ.prod μ) :=
    hsq₁.mul_prod hsq₂
  have hKsq : Integrable (fun p : Euc d × Euc d => (K p.1 p.2) ^ 2) (μ.prod μ) := hK.integrable_sq
  have hmeas : AEStronglyMeasurable (fun p : Euc d × Euc d => K p.1 p.2 * ((χ₁ p.1 / ρ p.1) * (χ₂ p.2 / ρ p.2)))
      (μ.prod μ) := by
    have e1 : AEStronglyMeasurable (fun p : Euc d × Euc d => χ₁ p.1 / ρ p.1) (μ.prod μ) := h₁.aestronglyMeasurable.comp_fst
    have e2 : AEStronglyMeasurable (fun p : Euc d × Euc d => χ₂ p.2 / ρ p.2) (μ.prod μ) := h₂.aestronglyMeasurable.comp_snd
    exact hK.aestronglyMeasurable.mul (e1.mul e2)
  have hI : Integrable (fun p : Euc d × Euc d => K p.1 p.2 * ((χ₁ p.1 / ρ p.1) * (χ₂ p.2 / ρ p.2))) (μ.prod μ) := by
    refine ((hKsq.add hprod).div_const 2).mono' hmeas (Filter.Eventually.of_forall fun p => ?_)
    set a := K p.1 p.2
    set b := (χ₁ p.1 / ρ p.1) * (χ₂ p.2 / ρ p.2)
    have : (χ₁ p.1 / ρ p.1) ^ 2 * (χ₂ p.2 / ρ p.2) ^ 2 = b ^ 2 := by simp only [b]; ring
    simp only [Pi.add_apply, this]
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_abs a, sq_abs b, sq_nonneg (|a| - |b|)]
  have hden : μ.prod μ = ((volume : Measure (Euc d)).prod (volume : Measure (Euc d))).withDensity
      (fun z : Euc d × Euc d => ENNReal.ofReal (ρ z.1) * ENNReal.ofReal (ρ z.2)) := by
    rw [hμ]
    unfold HRS.Whole.withDensityReal
    exact prod_withDensity hρm.ennreal_ofReal hρm.ennreal_ofReal
  rw [hden] at hI
  have hmf : Measurable (fun z : Euc d × Euc d => ENNReal.ofReal (ρ z.1) * ENNReal.ofReal (ρ z.2)) :=
    (hρm.comp measurable_fst).ennreal_ofReal.mul (hρm.comp measurable_snd).ennreal_ofReal
  rw [integrable_withDensity_iff_integrable_smul' hmf
    (Filter.Eventually.of_forall fun z => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)] at hI
  rw [Measure.volume_eq_prod]
  refine hI.congr (Filter.Eventually.of_forall fun p => ?_)
  have h1 : ρ p.1 ≠ 0 := (hρ p.1).ne'
  have h2 : ρ p.2 ≠ 0 := (hρ p.2).ne'
  simp only [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hρ p.1).le, ENNReal.toReal_ofReal (hρ p.2).le]
  field_simp

end HRS.MS.S21E
