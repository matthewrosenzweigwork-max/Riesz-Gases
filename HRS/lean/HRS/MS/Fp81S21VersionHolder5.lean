import HRS.MS.Fp81S21VersionHolder4

set_option autoImplicit false
noncomputable section
open Classical MeasureTheory Filter
open scoped ENNReal

namespace HRS.Fp81.S21

/-- A nonnegative L4 random variable has a measurable nonnegative
representative whose squared integral is controlled by its fourth moment. -/
theorem fp81s21_measurable_envelope_second_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Ω → ℝ) (hL0 : ∀ ω, 0 ≤ L ω) (hL : MemLp L 4 P)
    {K : ℝ} (hK : (∫ ω, L ω ^ 4 ∂P) ≤ K) :
    ∃ B : Ω → ℝ, Measurable B ∧ (∀ ω, 0 ≤ B ω) ∧ L =ᵐ[P] B ∧
      Integrable (fun ω => B ω ^ 2) P ∧ (∫ ω, B ω ^ 2 ∂P) ≤ 1 + K := by
  let B : Ω → ℝ := fun ω => |hL.aestronglyMeasurable.mk L ω|
  have hBm : Measurable B := hL.aestronglyMeasurable.stronglyMeasurable_mk.measurable.abs
  have hB0 : ∀ ω, 0 ≤ B ω := fun ω => abs_nonneg _
  have heq : L =ᵐ[P] B := by
    filter_upwards [hL.aestronglyMeasurable.ae_eq_mk] with ω hω
    dsimp only [B]
    rw [← hω, abs_of_nonneg (hL0 ω)]
  have hB4 : MemLp B 4 P := (memLp_congr_ae heq).1 hL
  have hB2 : MemLp B 2 P := hB4.mono_exponent (by norm_num)
  have hi2 : Integrable (fun ω => B ω ^ 2) P := by
    simpa only [Real.norm_of_nonneg (hB0 _)] using
      hB2.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hi4 : Integrable (fun ω => B ω ^ 4) P := by
    simpa only [Real.norm_of_nonneg (hB0 _)] using
      hB4.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  have hbound : (∫ ω, B ω ^ 4 ∂P) ≤ K := by
    rw [← integral_congr_ae (heq.mono fun ω hω => congrArg (fun x : ℝ => x ^ 4) hω)]
    exact hK
  have hpoint : ∀ᵐ ω ∂P, B ω ^ 2 ≤ 1 + B ω ^ 4 := by
    filter_upwards with ω
    nlinarith [sq_nonneg (B ω ^ 2 - 1)]
  have htotal := integral_mono_ae hi2 (integrable_const 1 |>.add hi4) hpoint
  change (∫ ω, B ω ^ 2 ∂P) ≤ ∫ ω, (1 : ℝ) + B ω ^ 4 ∂P at htotal
  rw [integral_add (integrable_const 1) hi4] at htotal
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at htotal
  exact ⟨B, hBm, hB0, heq, hi2, by linarith⟩

#print axioms fp81s21_measurable_envelope_second_moment

end HRS.Fp81.S21
