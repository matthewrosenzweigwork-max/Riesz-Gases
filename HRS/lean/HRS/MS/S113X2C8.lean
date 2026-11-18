import HRS.MS.S113X2C7
import HRS.MS.S113X2C2

/-!
# S11.3 X2 wiring (worker S11W), C8: conversion between the abstract power mass / tilt of the endpoint and the
configuration-space integrals of the chain inequality
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2C

open HRS.MS.S113BD (s113_powerMass s113_powerTilt)

section Conv

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A statement almost everywhere for `μ.withDensity q` with `q > 0` holds `μ`-almost everywhere. -/
theorem s113c_ae_of_withDensity {q : α → ℝ} (hqm : Measurable q) (hq : ∀ x, 0 < q x) {P : α → Prop}
    (h : ∀ᵐ x ∂(μ.withDensity (fun x => ENNReal.ofReal (q x))), P x) : ∀ᵐ x ∂μ, P x := by
  have := (ae_withDensity_iff (ENNReal.measurable_ofReal.comp hqm)).1 h
  filter_upwards [this] with x hx
  exact hx (ENNReal.ofReal_pos.2 (hq x)).ne'

theorem s113c_mass_conv (q : α → ℝ) (hqm : Measurable q) (hq : ∀ x, 0 < q x) (u rr : α → ℝ)
    (hrr : rr =ᵐ[μ.withDensity (fun x => ENNReal.ofReal (q x))] fun x => u x / q x) (p : ℝ) :
    s113_powerMass (μ.withDensity (fun x => ENNReal.ofReal (q x))) rr p = ∫ x, q x * (u x / q x) ^ p ∂μ := by
  have hae := s113c_ae_of_withDensity hqm hq hrr
  have hqm' : Measurable (fun x => ENNReal.ofReal (q x)) := ENNReal.measurable_ofReal.comp hqm
  unfold s113_powerMass
  rw [integral_withDensity_eq_integral_toReal_smul hqm'
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hq x).le, hx]

theorem s113c_tilt_conv [SigmaFinite μ] (q u rr f f' : α → ℝ) (hqm : Measurable q) (hq : ∀ x, 0 < q x)
    (hu0 : ∀ x, 0 ≤ u x) (hrrm : Measurable rr) (hrr0 : ∀ x, 0 ≤ rr x)
    (hrr : rr =ᵐ[μ.withDensity (fun x => ENNReal.ofReal (q x))] fun x => u x / q x)
    (hf : f =ᵐ[μ.withDensity (fun x => ENNReal.ofReal (q x))] f') (p : ℝ)
    (hint : Integrable (fun x => q x * (u x / q x) ^ p) μ) :
    s113_powerMass (μ.withDensity (fun x => ENNReal.ofReal (q x))) rr p *
        ∫ x, f x ∂(s113_powerTilt (μ.withDensity (fun x => ENNReal.ofReal (q x))) rr p) =
      ∫ x, q x * f' x * (u x / q x) ^ p ∂μ := by
  have hM := s113c_mass_conv q hqm hq u rr hrr p
  have hae := s113c_ae_of_withDensity hqm hq hrr
  have haf := s113c_ae_of_withDensity hqm hq hf
  have hnn : ∀ x, 0 ≤ q x * (u x / q x) ^ p := fun x =>
    mul_nonneg (hq x).le (Real.rpow_nonneg (div_nonneg (hu0 x) (hq x).le) p)
  have hM0 : 0 ≤ s113_powerMass (μ.withDensity (fun x => ENNReal.ofReal (q x))) rr p := by
    rw [hM]; exact integral_nonneg hnn
  by_cases hz : s113_powerMass (μ.withDensity (fun x => ENNReal.ofReal (q x))) rr p = 0
  · rw [hz, zero_mul]
    rw [hz] at hM
    have h0 := (integral_eq_zero_iff_of_nonneg hnn hint).1 hM.symm
    symm
    rw [← integral_zero (μ := μ) (G := ℝ)]
    refine integral_congr_ae ?_
    filter_upwards [h0] with x hx
    have : q x * f' x * (u x / q x) ^ p = f' x * (q x * (u x / q x) ^ p) := by ring
    rw [this]
    simp only [Pi.zero_apply] at hx
    rw [hx]; simp
  · have hMpos : 0 < s113_powerMass (μ.withDensity (fun x => ENNReal.ofReal (q x))) rr p :=
      lt_of_le_of_ne hM0 (Ne.symm hz)
    set M := s113_powerMass (μ.withDensity (fun x => ENNReal.ofReal (q x))) rr p with hMdef
    have hg : Measurable (fun x => ENNReal.ofReal (rr x ^ p / M)) :=
      ENNReal.measurable_ofReal.comp ((hrrm.pow_const p).div_const M)
    unfold s113_powerTilt
    rw [← hMdef]
    rw [integral_withDensity_eq_integral_toReal_smul hg
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    have hqm' : Measurable (fun x => ENNReal.ofReal (q x)) := ENNReal.measurable_ofReal.comp hqm
    rw [integral_withDensity_eq_integral_toReal_smul hqm'
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae, haf] with x hx hfx
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (hq x).le, ENNReal.toReal_ofReal (div_nonneg (Real.rpow_nonneg (hrr0 x) p) hMpos.le),
      hx, hfx]
    field_simp

end Conv

end HRS.MS.S113X2C

end
