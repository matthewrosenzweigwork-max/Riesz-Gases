import HRS.MS.FldRemCen4

/-! Convert a squared-integral ENNReal bound into a Bochner energy bound. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HRS.Fp81.S21

theorem fp81s21_g4_bochner_energy {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) [SFinite μ] (ν : Measure ℝ) [SFinite ν] {C : ℝ}
    {G : Ω × ℝ → E} (hG : Measurable G)
    (hC : (∫⁻ z, (∫⁻ q, ‖G (z, q)‖ₑ ∂ν)^2 ∂μ) ≤ ENNReal.ofReal C)
    (hC0 : 0 ≤ C) :
    Integrable (fun z => ‖∫ q, G (z, q) ∂ν‖^2) μ ∧
      (∫ z, ‖∫ q, G (z, q) ∂ν‖^2 ∂μ) ≤ C := by
  let D : Ω → E := fun z => ∫ q, G (z, q) ∂ν
  let F : Ω → ℝ := fun z => ‖D z‖^2
  have hDm : StronglyMeasurable D := hG.stronglyMeasurable.integral_prod_right'
  have hFm : StronglyMeasurable F := hDm.norm.pow 2
  have hle : ∀ z, ENNReal.ofReal (F z) ≤ (∫⁻ q, ‖G (z, q)‖ₑ ∂ν)^2 := by
    intro z
    dsimp [F, D]
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    gcongr
    exact enorm_integral_le_lintegral_enorm _
  have hlin : (∫⁻ z, ENNReal.ofReal (F z) ∂μ) ≤ ENNReal.ofReal C :=
    (lintegral_mono hle).trans hC
  have hint : Integrable F μ := by
    refine ⟨hFm.aestronglyMeasurable, (hasFiniteIntegral_iff_enorm).2 ?_⟩
    have htop : (∫⁻ z, ENNReal.ofReal (F z) ∂μ) < ∞ :=
      lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
    have heq : (∫⁻ z, ‖F z‖ₑ ∂μ) = ∫⁻ z, ENNReal.ofReal (F z) ∂μ := by
      apply lintegral_congr
      intro z
      exact Real.enorm_eq_ofReal (sq_nonneg ‖D z‖)
    rw [heq]
    exact htop
  refine ⟨hint, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hC0).1
  rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun z => sq_nonneg _)]
  exact hlin

#print axioms fp81s21_g4_bochner_energy
end HRS.Fp81.S21
end
