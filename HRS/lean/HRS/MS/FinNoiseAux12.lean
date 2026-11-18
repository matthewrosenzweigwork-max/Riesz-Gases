import HRS.MS.FinNoiseAux11

/-!
# S8.6 `finite_noise`, packet P6d (S86): differences of Hilbert-Schmidt integrands

`s86_hs_sub`: if `Φ₁, Φ₂` are `IsHSIntegrand P ℱ T`, so is `Φ₁ - Φ₂`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.FinNoise

open HRS HRS.Whole

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem s86_enorm_sq_sub_le' (a b : H) : ‖a - b‖ₑ ^ 2 ≤ 2 * (‖a‖ₑ ^ 2 + ‖b‖ₑ ^ 2) := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2, sq_nonneg (‖a‖ - ‖b‖)]

theorem s86_hs_sub {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {κ : Type*} [Countable κ] {Φ₁ Φ₂ : ℝ → Ω → κ → H} {T : ℝ}
    (h₁ : IsHSIntegrand P ℱ T Φ₁) (h₂ : IsHSIntegrand P ℱ T Φ₂) :
    IsHSIntegrand P ℱ T (fun r w k => Φ₁ r w k - Φ₂ r w k) := by
  refine ⟨fun k i => (h₁.prog k i).sub (h₂.prog k i), fun r w => ?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun k => ?_)
      (((h₁.summable r w).add (h₂.summable r w)).mul_left 2)
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (Φ₁ r w k) (Φ₂ r w k)) 2,
      sq_nonneg (‖Φ₁ r w k‖ - ‖Φ₂ r w k‖)]
  · have e1 := h₁.sq
    have e2 := h₂.sq
    have hc : ∀ (Φ : ℝ → Ω → κ → H) (w : Ω),
        ∫⁻ r in Icc (0 : ℝ) T, ∑' k, ‖Φ r w k‖ₑ ^ 2 =
        ∫⁻ r in Icc (0 : ℝ) T, ∑' k, ‖Φ (min r T) w k‖ₑ ^ 2 := fun Φ w =>
      setLIntegral_congr_fun measurableSet_Icc (fun r hr => by simp only [min_eq_left hr.2])
    have hm : ∀ (Φ : ℝ → Ω → κ → H), (∀ k, IsProgressive ℱ (fun r w => Φ r w k)) → ∀ w,
        Measurable fun r : ℝ => ∑' k, ‖Φ (min r T) w k‖ₑ ^ 2 := fun Φ hΦ w =>
      (hdsum_measurable_tsum Φ hΦ T).comp (measurable_id.prodMk measurable_const)
    unfold hsSqIntegralOn at e1 e2 ⊢
    calc ∫⁻ w, (∫⁻ r in Icc (0 : ℝ) T, ∑' k, ‖Φ₁ r w k - Φ₂ r w k‖ₑ ^ 2) ∂P
        ≤ ∫⁻ w, 2 * ((∫⁻ r in Icc (0 : ℝ) T, ∑' k, ‖Φ₁ r w k‖ₑ ^ 2) +
            (∫⁻ r in Icc (0 : ℝ) T, ∑' k, ‖Φ₂ r w k‖ₑ ^ 2)) ∂P := by
          refine lintegral_mono fun w => ?_
          rw [hc Φ₁ w, hc Φ₂ w, ← lintegral_add_left (hm Φ₁ h₁.prog w),
            ← lintegral_const_mul' _ _ (by simp)]
          refine setLIntegral_mono' measurableSet_Icc fun r hr => ?_
          simp only [min_eq_left hr.2]
          rw [← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
          exact ENNReal.tsum_le_tsum fun k => s86_enorm_sq_sub_le' _ _
      _ = 2 * ((∫⁻ w, (∫⁻ r in Icc (0 : ℝ) T, ∑' k, ‖Φ₁ r w k‖ₑ ^ 2) ∂P) +
            (∫⁻ w, (∫⁻ r in Icc (0 : ℝ) T, ∑' k, ‖Φ₂ r w k‖ₑ ^ 2) ∂P)) := by
          rw [lintegral_const_mul' _ _ (by simp),
            lintegral_add_left (hdsum_measurable_hsSq Φ₁ h₁.prog T)]
      _ < ⊤ := ENNReal.mul_lt_top (by simp) (ENNReal.add_lt_top.2 ⟨e1, e2⟩)

end HRS.MS.FinNoise
