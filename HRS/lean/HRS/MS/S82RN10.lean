import HRS.MS.S82RN9

/-!
# S8.2 R02 (S82R), N10: from set inequalities to pointwise (a.e.) density inequalities
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators

namespace HRS.MS.S82R

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

lemma s82r_rn_integrable {P : Measure E} [IsFiniteMeasure P] :
    Integrable (fun x => (P.rnDeriv μ x).toReal) μ :=
  Measure.integrable_toReal_rnDeriv

lemma s82r_rn_set {P : Measure E} [IsFiniteMeasure P] (hP : P ≪ μ) (S : Set E) :
    ∫ x in S, (P.rnDeriv μ x).toReal ∂μ = P.real S :=
  Measure.setIntegral_toReal_rnDeriv hP S

/-- `P ≤ K μ` gives the a.e. density bound. -/
lemma s82r_rn_le {P : Measure E} [IsFiniteMeasure P] {K : ℝ} (hK0 : 0 ≤ K)
    (hP : P ≤ ENNReal.ofReal K • μ) :
    ∀ᵐ x ∂μ, (P.rnDeriv μ x).toReal ≤ K := by
  have hac : P ≪ μ := Measure.absolutelyContinuous_of_le_smul hP
  have hi : Integrable (fun x => K - (P.rnDeriv μ x).toReal) μ :=
    (integrable_const K).sub s82r_rn_integrable
  have h0 : 0 ≤ᵐ[μ] fun x => K - (P.rnDeriv μ x).toReal := by
    refine ae_nonneg_of_forall_setIntegral_nonneg hi fun S hS _ => ?_
    rw [integral_sub (integrable_const K).integrableOn s82r_rn_integrable.integrableOn,
      s82r_rn_set hac S]
    have h1 := hP S
    simp only [Measure.smul_apply, smul_eq_mul] at h1
    have h2 : P.real S ≤ K * μ.real S := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ S)) h1
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0] at this
    simp only [setIntegral_const, smul_eq_mul]
    nlinarith [h2, mul_comm K (μ.real S)]
  filter_upwards [h0] with x hx
  have hx' : 0 ≤ K - (P.rnDeriv μ x).toReal := hx
  linarith

/-- Set inequality `|P₁ S - P₂ S| ≤ ∫_S ρ` for all measurable `S` gives `|f₁ - f₂| ≤ ρ` a.e. -/
lemma s82r_rn_abs_le {P₁ P₂ : Measure E} [IsFiniteMeasure P₁] [IsFiniteMeasure P₂]
    (h₁ : P₁ ≪ μ) (h₂ : P₂ ≪ μ) {ρ : E → ℝ} (hρ : Integrable ρ μ)
    (h : ∀ S : Set E, MeasurableSet S → |P₁.real S - P₂.real S| ≤ ∫ z in S, ρ z ∂μ) :
    ∀ᵐ x ∂μ, |(P₁.rnDeriv μ x).toReal - (P₂.rnDeriv μ x).toReal| ≤ ρ x := by
  have hd : Integrable (fun x => (P₁.rnDeriv μ x).toReal - (P₂.rnDeriv μ x).toReal) μ :=
    s82r_rn_integrable.sub s82r_rn_integrable
  have hset : ∀ S : Set E, ∫ z in S, ((P₁.rnDeriv μ z).toReal - (P₂.rnDeriv μ z).toReal) ∂μ
      = P₁.real S - P₂.real S := fun S => by
    rw [integral_sub s82r_rn_integrable.integrableOn s82r_rn_integrable.integrableOn,
      s82r_rn_set h₁, s82r_rn_set h₂]
  have hlo : 0 ≤ᵐ[μ] fun x => ρ x + ((P₁.rnDeriv μ x).toReal - (P₂.rnDeriv μ x).toReal) := by
    refine ae_nonneg_of_forall_setIntegral_nonneg (hρ.add hd) fun S hS _ => ?_
    rw [integral_add hρ.integrableOn hd.integrableOn, hset S]
    have := (abs_le.1 (h S hS)).1
    linarith
  have hhi : 0 ≤ᵐ[μ] fun x => ρ x - ((P₁.rnDeriv μ x).toReal - (P₂.rnDeriv μ x).toReal) := by
    refine ae_nonneg_of_forall_setIntegral_nonneg (hρ.sub hd) fun S hS _ => ?_
    rw [integral_sub hρ.integrableOn hd.integrableOn, hset S]
    have := (abs_le.1 (h S hS)).2
    linarith
  filter_upwards [hlo, hhi] with x h1 h2
  have h1' : 0 ≤ ρ x + ((P₁.rnDeriv μ x).toReal - (P₂.rnDeriv μ x).toReal) := h1
  have h2' : 0 ≤ ρ x - ((P₁.rnDeriv μ x).toReal - (P₂.rnDeriv μ x).toReal) := h2
  rw [abs_le]; constructor <;> linarith

end HRS.MS.S82R

end
