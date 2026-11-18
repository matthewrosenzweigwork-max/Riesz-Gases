import HRS.MS.CritForceLead2
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# S8.2 NormalForm packet R03, part 1: one-dimensional integrals with the repulsion cutoff

`∫_0^{r0} r^{s-1} (r^s + A)^{-k} dr` in closed form (fundamental theorem of calculus), used for the radial
rows with the cutoff `exp(-A r^{-s})`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.MS.S82N

lemma s82n_hasDerivAt_rpow_add (s A r : ℝ) (hr : 0 < r) :
    HasDerivAt (fun x : ℝ => x ^ s + A) (s * r ^ (s - 1)) r :=
  (Real.hasDerivAt_rpow_const (Or.inl hr.ne')).add_const A

lemma s82n_integrand_intervalIntegrable (s r0 A : ℝ) (hs : 0 < s) (hr0 : 0 < r0) (hA : 0 < A)
    (k : ℕ) :
    IntervalIntegrable (fun r : ℝ => r ^ (s - 1) / (r ^ s + A) ^ (k + 1)) volume 0 r0 := by
  have h1 : IntervalIntegrable (fun r : ℝ => r ^ (s - 1)) volume 0 r0 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  refine (h1.const_mul (1 / A ^ (k + 1))).mono_fun ?_ ?_
  · exact (Measurable.aestronglyMeasurable (by fun_prop))
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall fun r hr => ?_
    rw [Set.uIoc_of_le hr0.le] at hr
    have hr' : 0 < r := hr.1
    have hrs : 0 < r ^ s := Real.rpow_pos_of_pos hr' s
    have hp : 0 ≤ r ^ (s - 1) := (Real.rpow_pos_of_pos hr' _).le
    have hApos : 0 < A ^ (k + 1) := pow_pos hA _
    have hle : A ^ (k + 1) ≤ (r ^ s + A) ^ (k + 1) := pow_le_pow_left₀ hA.le (by linarith) _
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    rw [div_le_iff₀ (by positivity)]
    calc r ^ (s - 1) = 1 / A ^ (k + 1) * r ^ (s - 1) * A ^ (k + 1) := by field_simp
      _ ≤ 1 / A ^ (k + 1) * r ^ (s - 1) * (r ^ s + A) ^ (k + 1) := by gcongr

lemma s82n_continuousOn_rpow_add (s A r0 : ℝ) (hs : 0 < s) :
    ContinuousOn (fun r : ℝ => r ^ s + A) (Set.Icc 0 r0) :=
  ((Real.continuous_rpow_const hs.le).add continuous_const).continuousOn

/-- `∫_0^{r0} r^{s-1} (r^s + A)^{-(m+2)} dr`. -/
lemma s82n_ftc_pow (s r0 A : ℝ) (hs : 0 < s) (hr0 : 0 < r0) (hA : 0 < A) (m : ℕ) :
    ∫ r in (0 : ℝ)..r0, r ^ (s - 1) / (r ^ s + A) ^ (m + 2) =
      (1 / (s * ((m : ℝ) + 1))) * (1 / A ^ (m + 1) - 1 / (r0 ^ s + A) ^ (m + 1)) := by
  set F : ℝ → ℝ := fun r => -(1 / (s * ((m : ℝ) + 1))) * (1 / (r ^ s + A) ^ (m + 1)) with hF
  have hcont : ContinuousOn F (Set.Icc 0 r0) := by
    refine continuousOn_const.mul (ContinuousOn.div continuousOn_const
      ((s82n_continuousOn_rpow_add s A r0 hs).pow _) fun r hr => ?_)
    have : 0 ≤ r ^ s := Real.rpow_nonneg hr.1 _
    positivity
  have hderiv : ∀ r ∈ Set.Ioo 0 r0, HasDerivAt F (r ^ (s - 1) / (r ^ s + A) ^ (m + 2)) r := by
    intro r hr
    have hr' : 0 < r := hr.1
    have hu := s82n_hasDerivAt_rpow_add s A r hr'
    have hurs : 0 < r ^ s + A := by have := Real.rpow_pos_of_pos hr' s; linarith
    have hne : (r ^ s + A) ^ (m + 1) ≠ 0 := by positivity
    have hp : HasDerivAt (fun x : ℝ => (x ^ s + A) ^ (m + 1))
        (((m : ℝ) + 1) * (r ^ s + A) ^ m * (s * r ^ (s - 1))) r := by
      have := (hasDerivAt_pow (m + 1) (r ^ s + A)).comp r hu
      refine HasDerivAt.congr_deriv this ?_
      simp
    have h2 := hp.inv hne
    have h3 := h2.const_mul (-(1 / (s * ((m : ℝ) + 1))))
    have hFe : F = fun y => -(1 / (s * ((m : ℝ) + 1))) * ((y ^ s + A) ^ (m + 1))⁻¹ := by
      funext y; simp [hF, one_div]
    rw [hFe]
    convert h3 using 1
    have hpos : r ^ s + A ≠ 0 := hurs.ne'
    have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
    have hs0 : s ≠ 0 := hs.ne'
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr0.le hcont hderiv
    (s82n_integrand_intervalIntegrable s r0 A hs hr0 hA (m + 1))]
  simp only [hF, Real.zero_rpow hs.ne', zero_add]
  ring

/-- `∫_0^{r0} r^{s-1} (r^s + A)^{-1} dr = (log (r0^s + A) - log A)/s`. -/
lemma s82n_ftc_log (s r0 A : ℝ) (hs : 0 < s) (hr0 : 0 < r0) (hA : 0 < A) :
    ∫ r in (0 : ℝ)..r0, r ^ (s - 1) / (r ^ s + A) ^ 1 =
      (Real.log (r0 ^ s + A) - Real.log A) / s := by
  set F : ℝ → ℝ := fun r => Real.log (r ^ s + A) / s with hF
  have hcont : ContinuousOn F (Set.Icc 0 r0) := by
    refine ContinuousOn.div_const (ContinuousOn.log (s82n_continuousOn_rpow_add s A r0 hs)
      fun r hr => ?_) s
    have : 0 ≤ r ^ s := Real.rpow_nonneg hr.1 _
    linarith
  have hderiv : ∀ r ∈ Set.Ioo 0 r0, HasDerivAt F (r ^ (s - 1) / (r ^ s + A) ^ 1) r := by
    intro r hr
    have hr' : 0 < r := hr.1
    have hu := s82n_hasDerivAt_rpow_add s A r hr'
    have hurs : 0 < r ^ s + A := by have := Real.rpow_pos_of_pos hr' s; linarith
    have h2 := (hu.log hurs.ne').div_const s
    convert h2 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr0.le hcont hderiv
    (by simpa using s82n_integrand_intervalIntegrable s r0 A hs hr0 hA 0)]
  simp only [hF, Real.zero_rpow hs.ne', zero_add]
  ring

end HRS.MS.S82N
