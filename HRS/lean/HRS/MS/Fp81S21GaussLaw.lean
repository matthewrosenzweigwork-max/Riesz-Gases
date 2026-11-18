import HRS.MS.S21F_D01

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

/-- The exponentially weighted remote part of the Gaussian time integral is bounded by its tail. -/
theorem fp81s21_gaussian_remote_exp_integral
    (a L c : ℝ) (ha : 0 ≤ a) (hL : 0 < L) (hc : 0 < c) :
    (∫ v in Set.Ioc (0 : ℝ) (max (a - L) 0), Real.exp (-c * (a - v))) ≤
      c⁻¹ * Real.exp (-c * L) := by
  by_cases hle : a ≤ L
  · have hmax : max (a - L) 0 = 0 := max_eq_right (sub_nonpos.mpr hle)
    rw [hmax]
    simp
    positivity
  · have hLa : L < a := lt_of_not_ge hle
    have hb : 0 < a - L := sub_pos.mpr hLa
    have hmax : max (a - L) 0 = a - L := max_eq_left (le_of_lt hb)
    rw [hmax]
    let F : ℝ → ℝ := fun v => c⁻¹ * Real.exp (-c * (a - v))
    have hFderiv (v : ℝ) : HasDerivAt F (Real.exp (-c * (a - v))) v := by
      have hlin : HasDerivAt ((fun x : ℝ => a) - id) (-1) v := by
        simpa using (hasDerivAt_const v a).sub (hasDerivAt_id v)
      have harg : HasDerivAt (fun x : ℝ => -c * (a - x)) c v := by
        convert hlin.const_mul (-c) using 1
        · funext x
          simp
        · ring
      have hexp := (Real.hasDerivAt_exp _).comp v harg
      simpa [F, mul_assoc, mul_comm, mul_left_comm, hc.ne'] using hexp.const_mul c⁻¹
    have hcontArg : Continuous (fun v : ℝ => -c * (a - v)) :=
      continuous_const.mul (continuous_const.sub continuous_id)
    have hcontExp : Continuous (fun v : ℝ => Real.exp (-c * (a - v))) :=
      Real.continuous_exp.comp hcontArg
    have hformula :
        (∫ v in Set.Ioc (0 : ℝ) (a - L), Real.exp (-c * (a - v))) =
          c⁻¹ * (Real.exp (-c * L) - Real.exp (-c * a)) := by
      calc
        _ = ∫ v in (0 : ℝ)..(a - L), Real.exp (-c * (a - v)) := by
          rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ a - L by linarith)]
        _ = F (a - L) - F 0 :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
            (a := (0 : ℝ)) (b := a - L) (f := F)
            (f' := fun v => Real.exp (-c * (a - v)))
            (show (0 : ℝ) ≤ a - L by linarith)
            (hcontExp.const_mul c⁻¹).continuousOn
            (fun v _ => hFderiv v)
            (hcontExp.intervalIntegrable (μ := volume) 0 (a - L))
        _ = c⁻¹ * (Real.exp (-c * L) - Real.exp (-c * a)) := by
          simp only [F, show a - (a - L) = L by ring, sub_zero]
          ring
    rw [hformula]
    have hcinv : 0 < c⁻¹ := inv_pos.mpr hc
    have hexp : 0 ≤ Real.exp (-c * a) := Real.exp_nonneg _
    calc
      c⁻¹ * (Real.exp (-c * L) - Real.exp (-c * a)) ≤
          c⁻¹ * Real.exp (-c * L) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hcinv)
      _ = c⁻¹ * Real.exp (-c * L) := rfl

#print axioms fp81s21_gaussian_remote_exp_integral

end HRS.Fp81.S21

end
