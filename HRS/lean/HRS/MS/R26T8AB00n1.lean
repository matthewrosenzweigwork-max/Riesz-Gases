import HRS.MS.R26T8AB00m

/-!
# S8.2 observed-time layer, packet T8A.B00 (helper n1): Minkowski for a.e.-measurable integrands

The squared `L²(P)` norm of `w ↦ ∫⁻_ν F w b` is at most `ν univ` times `∫⁻_ν ‖F · b‖²`, for a function `F` that is
only almost-everywhere measurable on the product, and a finite-or-s-finite parameter measure `ν`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A

theorem r26t8a_b00n1_mink_ae {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω) [SFinite P] (ν : Measure β) [SFinite ν]
    {F : Ω → β → ℝ≥0∞} (hF : AEMeasurable (Function.uncurry F) (P.prod ν)) :
    ∫⁻ w, (∫⁻ b, F w b ∂ν) ^ (2 : ℝ) ∂P ≤
      ν Set.univ * ∫⁻ b, ∫⁻ w, F w b ^ (2 : ℝ) ∂P ∂ν := by
  set G : Ω → β → ℝ≥0∞ := fun w b => hF.mk (Function.uncurry F) (w, b) with hG
  have hGm : Measurable (Function.uncurry G) := hF.measurable_mk
  have hae : ∀ᵐ p ∂(P.prod ν), Function.uncurry F p = Function.uncurry G p := hF.ae_eq_mk
  have h1 : ∀ᵐ w ∂P, ∀ᵐ b ∂ν, F w b = G w b := Measure.ae_ae_of_ae_prod hae
  have hsw : ∀ᵐ p ∂(ν.prod P), F p.2 p.1 = G p.2 p.1 :=
    (Measure.measurePreserving_swap (μ := ν) (ν := P)).quasiMeasurePreserving.ae hae
  have h2 : ∀ᵐ b ∂ν, ∀ᵐ w ∂P, F w b = G w b := Measure.ae_ae_of_ae_prod hsw
  have key := HRS.Whole.AppendixA.Phase2SA16.sa16j_mink (μ := P) (ν := ν)
    (p := 2) (by norm_num) (a := fun _ => (1 : ℝ≥0∞)) measurable_const hGm
  rw [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at key
  simp only [one_mul, lintegral_const] at key
  calc ∫⁻ w, (∫⁻ b, F w b ∂ν) ^ (2 : ℝ) ∂P
      = ∫⁻ w, (∫⁻ b, G w b ∂ν) ^ (2 : ℝ) ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [h1] with w hw
        rw [lintegral_congr_ae hw]
    _ ≤ ν Set.univ * ∫⁻ b, ∫⁻ w, G w b ^ (2 : ℝ) ∂P ∂ν := key
    _ = ν Set.univ * ∫⁻ b, ∫⁻ w, F w b ^ (2 : ℝ) ∂P ∂ν := by
        congr 1
        refine lintegral_congr_ae ?_
        filter_upwards [h2] with b hb
        refine lintegral_congr_ae ?_
        filter_upwards [hb] with w hw
        rw [hw]

end HRS.MS.R26T8A

end
