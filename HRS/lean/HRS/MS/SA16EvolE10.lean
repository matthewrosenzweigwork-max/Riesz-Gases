import Mathlib

/-!
# S.A.16 E10: `stability_convolution_bound`

For `0 ≤ r ≤ t`, `a (t - r) + b r ≤ max a b * t ≤ K t`; integrating the constant bound over `[0, t]`
(measure `t`) gives the exact factor `t`, with value `0` at `t = 0`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Evolution

theorem stability_convolution_bound (a b C D K t : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hK : max a b ≤ K) (ht : 0 ≤ t) :
    (∫ r in Icc (0 : ℝ) t, C*Real.exp (a*(t-r))*D*Real.exp (b*r)) ≤
      C*D*t*Real.exp (K*t) := by
  have haK : a ≤ K := (le_max_left a b).trans hK
  have hbK : b ≤ K := (le_max_right a b).trans hK
  have hcont : Continuous (fun r : ℝ => C*Real.exp (a*(t-r))*D*Real.exp (b*r)) := by fun_prop
  calc (∫ r in Icc (0 : ℝ) t, C*Real.exp (a*(t-r))*D*Real.exp (b*r))
      ≤ ∫ r in Icc (0 : ℝ) t, C*D*Real.exp (K*t) := by
        refine setIntegral_mono_on (hcont.continuousOn.integrableOn_Icc)
          (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
          measurableSet_Icc fun r hr => ?_
        have h1 : a * (t - r) + b * r ≤ K * t := by
          nlinarith [mul_le_mul_of_nonneg_right haK (sub_nonneg.2 hr.2),
            mul_le_mul_of_nonneg_right hbK hr.1]
        have h2 : Real.exp (a * (t - r)) * Real.exp (b * r) ≤ Real.exp (K * t) := by
          rw [← Real.exp_add]
          exact Real.exp_le_exp.2 h1
        have h3 : C * Real.exp (a * (t - r)) * D * Real.exp (b * r) =
            C * D * (Real.exp (a * (t - r)) * Real.exp (b * r)) := by ring
        rw [h3]
        exact mul_le_mul_of_nonneg_left h2 (mul_nonneg hC hD)
    _ = C*D*t*Real.exp (K*t) := by
        rw [setIntegral_const]
        simp [Measure.real, Real.volume_Icc, ht]
        ring

end HRS.Whole.AppendixA.Phase2SA16Evolution
