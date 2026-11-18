import HRS.MS.S113Exponent
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# S11.3 endpoint (worker S113X), part 1: the variable exponent `p(t)` is locally absolutely continuous and solves
`p' = -(L/c_L) p (p-1)` almost everywhere (scalar part of the power-chain argument)
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S113BD

open HRS.Whole

theorem s113x_Icc_eq_interval (L : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ r in Set.Icc (0 : ℝ) t, L r = ∫ r in (0 : ℝ)..t, L r := by
  rw [intervalIntegral.integral_of_le ht, MeasureTheory.integral_Icc_eq_integral_Ioc]

theorem s113x_intervalIntegrable {L : ℝ → ℝ}
    (hLi : Integrable L (volume.restrict (Set.Ioi (0 : ℝ)))) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable L volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  exact (show IntegrableOn L (Set.Ioi (0 : ℝ)) volume from hLi).mono_set Set.Ioc_subset_Ioi_self

theorem s113x_exponent_eq (cL p₀ : ℝ) (L : ℝ → ℝ) (t : ℝ) :
    r2MovExponent cL p₀ L t = (s113_den cL p₀ (∫ r in Set.Icc (0 : ℝ) t, L r))⁻¹ := rfl

theorem s113x_exponent_zero {cL p₀ : ℝ} (L : ℝ → ℝ) : r2MovExponent cL p₀ L 0 = p₀ := by
  rw [s113x_exponent_eq]
  simp [s113_den_zero]

theorem s113x_integral_nonneg {L : ℝ → ℝ} (hL0 : ∀ t, 0 ≤ t → 0 ≤ L t) {t : ℝ} (_ : 0 ≤ t) :
    0 ≤ ∫ r in Set.Icc (0 : ℝ) t, L r := by
  refine setIntegral_nonneg measurableSet_Icc fun r hr => hL0 r hr.1

theorem s113x_exponent_bounds {cL p₀ : ℝ} (hcL : 0 < cL) (hp₀ : 1 < p₀) {L : ℝ → ℝ}
    (hL0 : ∀ t, 0 ≤ t → 0 ≤ L t) {t : ℝ} (ht : 0 ≤ t) :
    1 < r2MovExponent cL p₀ L t ∧ r2MovExponent cL p₀ L t ≤ p₀ := by
  rw [s113x_exponent_eq]
  have hI := s113x_integral_nonneg hL0 ht
  have h1 := s113_den_pos hcL hp₀ hI
  have h2 := s113_den_lt_one (cL := cL) hp₀ (∫ r in Set.Icc (0 : ℝ) t, L r)
  have h3 := s113_den_mono hcL hp₀ hI
  rw [s113_den_zero] at h3
  refine ⟨?_, ?_⟩
  · exact (one_lt_inv₀ h1).2 h2
  · calc (s113_den cL p₀ _)⁻¹ ≤ (p₀⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 (by linarith)) h3
      _ = p₀ := inv_inv p₀

theorem s113x_den_contDiff {cL p₀ : ℝ} (hcL : 0 < cL) (hp₀ : 1 < p₀) :
    ContDiffOn ℝ 1 (fun x => (s113_den cL p₀ x)⁻¹) (Set.Ici 0) := by
  have h1 : ContDiff ℝ 1 (fun x : ℝ => s113_den cL p₀ x) := by
    unfold s113_den
    fun_prop
  exact h1.contDiffOn.inv (fun x hx => (s113_den_pos hcL hp₀ (Set.mem_Ici.1 hx)).ne')

theorem s113x_exponent_ac {cL p₀ : ℝ} (hcL : 0 < cL) (hp₀ : 1 < p₀) {L : ℝ → ℝ}
    (hL0 : ∀ t, 0 ≤ t → 0 ≤ L t) (hLi : Integrable L (volume.restrict (Set.Ioi (0 : ℝ))))
    {T : ℝ} (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (r2MovExponent cL p₀ L) 0 T := by
  set J : ℝ → ℝ := fun x => ∫ v in (0 : ℝ)..x, L v with hJ
  have hLT := s113x_intervalIntegrable hLi hT
  have hJac : AbsolutelyContinuousOnInterval J 0 T :=
    hLT.absolutelyContinuousOnInterval_intervalIntegral (by simp [hT])
  set G : ℝ → ℝ := fun x => (s113_den cL p₀ x)⁻¹ with hG
  have hJ0 : ∀ t ∈ Set.uIcc (0 : ℝ) T, 0 ≤ J t := fun t ht => by
    rw [Set.uIcc_of_le hT] at ht
    simp only [hJ]
    rw [← s113x_Icc_eq_interval L ht.1]
    exact s113x_integral_nonneg hL0 ht.1
  have hJmono : ∀ t ∈ Set.uIcc (0 : ℝ) T, J t ≤ J T := fun t ht => by
    rw [Set.uIcc_of_le hT] at ht
    simp only [hJ]
    refine intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 ?_ hLT
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun x hx => hL0 x hx.1.le
  have hcd : ContDiffOn ℝ 1 G (Set.Icc 0 (J T)) :=
    (s113x_den_contDiff hcL hp₀).mono Set.Icc_subset_Ici_self
  obtain ⟨K, hK⟩ := hcd.exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
  have hcomp := hK.comp_absolutelyContinuousOnInterval (a := 0) (b := T)
    (g := J) (fun t ht => ⟨hJ0 t ht, hJmono t ht⟩) hJac
  refine hcomp.congr ?_
  intro t ht
  rw [Set.uIcc_of_le hT] at ht
  simp only [Function.comp, hJ, hG]
  rw [s113x_exponent_eq, s113x_Icc_eq_interval L ht.1]

/-- The exponent ODE, almost everywhere on a finite horizon. -/
theorem s113x_exponent_deriv {cL p₀ : ℝ} (hcL : 0 < cL) (hp₀ : 1 < p₀) {L : ℝ → ℝ}
    (hL0 : ∀ t, 0 ≤ t → 0 ≤ L t) (hLi : Integrable L (volume.restrict (Set.Ioi (0 : ℝ))))
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ t : ℝ, t ∈ Set.Ioo 0 T →
      HasDerivAt (r2MovExponent cL p₀ L)
        (-(L t / cL) * r2MovExponent cL p₀ L t * (r2MovExponent cL p₀ L t - 1)) t := by
  have hLT := s113x_intervalIntegrable hLi hT
  filter_upwards [hLT.ae_hasDerivAt_integral] with t hLt ht
  have hJ : HasDerivAt (fun x => ∫ v in (0 : ℝ)..x, L v) (L t) t :=
    hLt (by rw [Set.uIcc_of_le hT]; exact ⟨ht.1.le, ht.2.le⟩) 0 (by simp [hT])
  set a : ℝ := 1 - p₀⁻¹ with ha
  set I : ℝ := ∫ v in (0 : ℝ)..t, L v with hI
  have hI0 : 0 ≤ I := by
    rw [hI, ← s113x_Icc_eq_interval L ht.1.le]
    exact s113x_integral_nonneg hL0 ht.1.le
  have hden : s113_den cL p₀ I ≠ 0 := (s113_den_pos hcL hp₀ hI0).ne'
  -- derivative of `D(x) = 1 - a e^{-x/c}` composed with `J`
  have hD : HasDerivAt (fun x => s113_den cL p₀ (∫ v in (0 : ℝ)..x, L v))
      (a * Real.exp (-(cL⁻¹) * I) * cL⁻¹ * L t) t := by
    have h1 : HasDerivAt (fun x => -(cL⁻¹) * ∫ v in (0 : ℝ)..x, L v) (-(cL⁻¹) * L t) t :=
      hJ.const_mul _
    have h2 := (h1.exp).const_mul a
    have h3 := h2.const_sub 1
    unfold s113_den
    convert h3 using 1
    ring
  have hP : HasDerivAt (fun x => (s113_den cL p₀ (∫ v in (0 : ℝ)..x, L v))⁻¹)
      (-(a * Real.exp (-(cL⁻¹) * I) * cL⁻¹ * L t) / (s113_den cL p₀ I) ^ 2) t := hD.inv hden
  have hev : (r2MovExponent cL p₀ L) =ᶠ[𝓝 t] fun x => (s113_den cL p₀ (∫ v in (0 : ℝ)..x, L v))⁻¹ := by
    filter_upwards [Ioi_mem_nhds ht.1] with x hx
    rw [s113x_exponent_eq, s113x_Icc_eq_interval L (le_of_lt hx)]
  refine (hP.congr_of_eventuallyEq hev).congr_deriv ?_
  have hpt : r2MovExponent cL p₀ L t = (s113_den cL p₀ I)⁻¹ := by
    rw [s113x_exponent_eq, s113x_Icc_eq_interval L ht.1.le]
  rw [hpt]
  have hE : a * Real.exp (-(cL⁻¹) * I) = 1 - s113_den cL p₀ I := by
    unfold s113_den; ring
  rw [hE]
  field_simp

end HRS.MS.S113BD
