import HRS.MS.FixEqP3Aux31

/-!
# S5.7 `fixed_equation` (worker S57P), part 44: the `L^p` combination of the initial and the noise part
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MS.FixEq

theorem s57p_lp_combine {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (P : Measure Ω₁)
    [IsProbabilityMeasure P] (Q : Measure Ω₂) [IsProbabilityMeasure Q] {p : ℝ} (hp : p = 1 ∨ p = 2)
    (F : Ω₁ × Ω₂ → ℝ≥0∞) (dual : Ω₁ → ℝ≥0∞) (B : Ω₂ → ℝ≥0∞) (hB : Measurable B) {E N : ℝ≥0∞} (hE : E ≠ ⊤)
    (hBN : ∫⁻ w, B w ^ (4 : ℝ) ∂Q ≤ N) (hF : ∀ᵐ ζ ∂(P.prod Q), F ζ ≤ E * dual ζ.1 + B ζ.2) :
    (∫⁻ ζ, F ζ ^ p ∂(P.prod Q)) ^ (1 / p) ≤ 2 * (E * (∫⁻ x, dual x ^ p ∂P) ^ (1 / p) + N ^ (1 / (4 : ℝ))) := by
  have hp1 : 1 ≤ p := by rcases hp with rfl | rfl <;> norm_num
  have hp0 : 0 < p := by linarith
  have h2p : (2 : ℝ≥0∞) ^ (p - 1) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)
  have hBp : Measurable fun ζ : Ω₁ × Ω₂ => B ζ.2 ^ p := (hB.comp measurable_snd).pow_const p
  have s1 : ∫⁻ ζ, F ζ ^ p ∂(P.prod Q) ≤ (2 : ℝ≥0∞) ^ (p - 1) *
      ((∫⁻ ζ, (E * dual ζ.1) ^ p ∂(P.prod Q)) + ∫⁻ ζ, B ζ.2 ^ p ∂(P.prod Q)) := by
    calc ∫⁻ ζ, F ζ ^ p ∂(P.prod Q) ≤ ∫⁻ ζ, (2 : ℝ≥0∞) ^ (p - 1) * ((E * dual ζ.1) ^ p + B ζ.2 ^ p) ∂(P.prod Q) :=
          lintegral_mono_ae (hF.mono fun ζ h => (ENNReal.rpow_le_rpow h hp0.le).trans
            (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp1))
      _ = (2 : ℝ≥0∞) ^ (p - 1) * ∫⁻ ζ, ((E * dual ζ.1) ^ p + B ζ.2 ^ p) ∂(P.prod Q) :=
          lintegral_const_mul' _ _ h2p
      _ = _ := by rw [lintegral_add_right _ hBp]
  have s2 : ∫⁻ ζ, (E * dual ζ.1) ^ p ∂(P.prod Q) ≤ E ^ p * ∫⁻ x, dual x ^ p ∂P := by
    refine (s57p_lint_fst_le P Q (fun x => (E * dual x) ^ p)).trans (le_of_eq ?_)
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    exact lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le hE)
  have s3 : ∫⁻ ζ, B ζ.2 ^ p ∂(P.prod Q) = ∫⁻ w, B w ^ p ∂Q := s57p_lint_snd P Q (hB.pow_const p)
  have s4 : (∫⁻ w, B w ^ p ∂Q) ^ (1 / p) ≤ N ^ (1 / (4 : ℝ)) :=
    (s57p_jensen hB.aemeasurable hp).trans (ENNReal.rpow_le_rpow hBN (by norm_num))
  have s5 : ((2 : ℝ≥0∞) ^ (p - 1)) ^ (1 / p) ≤ 2 := by
    calc ((2 : ℝ≥0∞) ^ (p - 1)) ^ (1 / p) ≤ ((2 : ℝ≥0∞) ^ p) ^ (1 / p) :=
          ENNReal.rpow_le_rpow (ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)) (by positivity)
      _ = 2 := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]
  have hq0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hq1 : 1 / p ≤ 1 := by rw [div_le_one hp0]; exact hp1
  calc (∫⁻ ζ, F ζ ^ p ∂(P.prod Q)) ^ (1 / p)
      ≤ ((2 : ℝ≥0∞) ^ (p - 1) * (E ^ p * ∫⁻ x, dual x ^ p ∂P + ∫⁻ w, B w ^ p ∂Q)) ^ (1 / p) := by
        refine ENNReal.rpow_le_rpow (s1.trans (mul_le_mul' le_rfl ?_)) hq0
        rw [← s3]; exact add_le_add s2 le_rfl
    _ = ((2 : ℝ≥0∞) ^ (p - 1)) ^ (1 / p) * (E ^ p * ∫⁻ x, dual x ^ p ∂P + ∫⁻ w, B w ^ p ∂Q) ^ (1 / p) :=
        ENNReal.mul_rpow_of_nonneg _ _ hq0
    _ ≤ 2 * ((E ^ p * ∫⁻ x, dual x ^ p ∂P) ^ (1 / p) + (∫⁻ w, B w ^ p ∂Q) ^ (1 / p)) :=
        mul_le_mul' s5 (ENNReal.rpow_add_le_add_rpow _ _ hq0 hq1)
    _ ≤ 2 * (E * (∫⁻ x, dual x ^ p ∂P) ^ (1 / p) + N ^ (1 / (4 : ℝ))) := by
        refine mul_le_mul' le_rfl (add_le_add (le_of_eq ?_) s4)
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq0, ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

end HRS.MS.FixEq
