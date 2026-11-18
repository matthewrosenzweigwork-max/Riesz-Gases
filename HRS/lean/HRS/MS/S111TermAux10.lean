import HRS.MS.S111TermAux9

/-!
# S11.1 terminal wave, T06: a mean-zero Lipschitz function has a controlled third moment
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal

namespace HRS.MS.S111T

open HRS HRS.Whole

/-- **T06.** `f` measurable, integrable, mean zero, `L`-Lipschitz on a space whose probability measure has a finite
third moment: `∫|f|³ ≤ 8 L³ ∫‖x‖³`. -/
theorem s111t_centered_lipschitz_third_moment {d : ℕ}
    (mu : Measure (Euc d)) [IsProbabilityMeasure mu]
    (hmu : Integrable (fun x : Euc d => ‖x‖ ^ 3) mu)
    (f : Euc d → ℝ) (hf : Measurable f) (hfi : Integrable f mu)
    (hmean : ∫ x, f x ∂mu = 0)
    (L : ℝ≥0) (hL : LipschitzWith L f) :
    Integrable (fun x => |f x| ^ 3) mu ∧
      (∫ x, |f x| ^ 3 ∂mu) ≤ 8 * (L : ℝ) ^ 3 * ∫ x, ‖x‖ ^ 3 ∂mu := by
  set m3 : ℝ := ∫ x, ‖x‖ ^ 3 ∂mu with hm3
  have hm3nn : 0 ≤ m3 := integral_nonneg fun x => by positivity
  have hnorm1 : Integrable (fun x : Euc d => ‖x‖) mu := by
    refine (hmu.add (integrable_const (1 : ℝ))).mono' (by fun_prop : Measurable fun x : Euc d => ‖x‖).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 1), sq_nonneg ‖x‖]
  set m1 : ℝ := ∫ x, ‖x‖ ∂mu with hm1
  have hm1nn : 0 ≤ m1 := integral_nonneg fun x => norm_nonneg _
  have hjensen : m1 ^ 3 ≤ m3 := by
    have := (convexOn_pow 3).map_integral_le (μ := mu) (f := fun x : Euc d => ‖x‖)
      (continuousOn_pow 3) isClosed_Ici (ae_of_all _ fun x => norm_nonneg x) hnorm1 hmu
    simpa [hm1, hm3, Function.comp] using this
  -- pointwise bound
  have hpt : ∀ x, |f x| ≤ (L : ℝ) * (‖x‖ + m1) := by
    intro x
    have h0 : f x = ∫ y, (f x - f y) ∂mu := by
      rw [integral_sub (integrable_const _) hfi, hmean]; simp
    have hint : Integrable (fun y => f x - f y) mu := (integrable_const _).sub hfi
    calc |f x| = |∫ y, (f x - f y) ∂mu| := by rw [← h0]
      _ ≤ ∫ y, |f x - f y| ∂mu := abs_integral_le_integral_abs
      _ ≤ ∫ y, (L : ℝ) * (‖x‖ + ‖y‖) ∂mu := by
          refine integral_mono hint.abs (((integrable_const ‖x‖).add hnorm1).const_mul _) fun y => ?_
          have h1 := hL.dist_le_mul x y
          rw [Real.dist_eq] at h1
          have h2 : dist x y ≤ ‖x‖ + ‖y‖ := by
            rw [dist_eq_norm]; exact norm_sub_le x y
          calc |f x - f y| ≤ L * dist x y := by simpa [abs_sub_comm] using h1
            _ ≤ L * (‖x‖ + ‖y‖) := mul_le_mul_of_nonneg_left h2 L.2
      _ = (L : ℝ) * (‖x‖ + m1) := by
          rw [integral_const_mul, integral_add (integrable_const _) hnorm1]
          simp [hm1]
  have hcube : ∀ x, |f x| ^ 3 ≤ 4 * (L : ℝ) ^ 3 * (‖x‖ ^ 3 + m3) := by
    intro x
    have h1 : |f x| ^ 3 ≤ ((L : ℝ) * (‖x‖ + m1)) ^ 3 := by
      gcongr
      exact hpt x
    have h2 : (‖x‖ + m1) ^ 3 ≤ 4 * (‖x‖ ^ 3 + m1 ^ 3) := by
      nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - m1), mul_nonneg (norm_nonneg x) hm1nn,
        sq_nonneg (‖x‖ + m1), mul_nonneg (add_nonneg (norm_nonneg x) hm1nn) (sq_nonneg (‖x‖ - m1))]
    calc |f x| ^ 3 ≤ ((L : ℝ) * (‖x‖ + m1)) ^ 3 := h1
      _ = (L : ℝ) ^ 3 * (‖x‖ + m1) ^ 3 := by ring
      _ ≤ (L : ℝ) ^ 3 * (4 * (‖x‖ ^ 3 + m1 ^ 3)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ (L : ℝ) ^ 3 * (4 * (‖x‖ ^ 3 + m3)) := by gcongr
      _ = _ := by ring
  have hbig : Integrable (fun x : Euc d => 4 * (L : ℝ) ^ 3 * (‖x‖ ^ 3 + m3)) mu :=
    (hmu.add (integrable_const m3)).const_mul _
  have hint : Integrable (fun x => |f x| ^ 3) mu :=
    hbig.mono' ((hf.abs.pow_const 3).aestronglyMeasurable)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hcube x)
  refine ⟨hint, ?_⟩
  calc (∫ x, |f x| ^ 3 ∂mu) ≤ ∫ x, 4 * (L : ℝ) ^ 3 * (‖x‖ ^ 3 + m3) ∂mu :=
        integral_mono hint hbig hcube
    _ = 8 * (L : ℝ) ^ 3 * m3 := by
        rw [integral_const_mul, integral_add hmu (integrable_const _)]
        simp [hm3]; ring

end HRS.MS.S111T
