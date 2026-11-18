import HRS.MS.R26T6CI11MeasFTC

/-! I11: cubic integrability identity for Banach-valued L³ random variables. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C

theorem r26t6c_vector_lpNorm_cube
    {Omega B : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup B] (P : Measure Omega)
    (F : Omega → B) (hF : MemLp F 3 P) :
    lpNorm F 3 P ^ 3 = ∫ w, ‖F w‖ ^ 3 ∂P := by
  have hi : Integrable (fun w => ‖F w‖ ^ 3) P :=
    hF.integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0)
  have hI0 : 0 ≤ ∫ w, ‖F w‖ ^ 3 ∂P :=
    integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) 3)
  rw [lpNorm_eq_integral_norm_rpow_toReal
    (by norm_num : (3 : ℝ≥0∞) ≠ 0)
    (by norm_num : (3 : ℝ≥0∞) ≠ ∞) hF.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  have heq : (∫ w, ‖F w‖ ^ (3 : ℝ) ∂P) =
      ∫ w, ‖F w‖ ^ (3 : ℕ) ∂P := by
    apply integral_congr_ae
    exact ae_of_all _ fun w => by
      simpa using (Real.rpow_natCast ‖F w‖ 3)
  rw [heq]
  have hdiv : (3 : ℝ)⁻¹ = 1 / 3 := by ring
  rw [hdiv, ← Real.rpow_natCast, ← Real.rpow_mul hI0]
  norm_num

theorem r26t6c_vector_cube_le
    {Omega B : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup B] (P : Measure Omega)
    (F : Omega → B) (hF : MemLp F 3 P)
    (A : ℝ) (hA : 0 ≤ A)
    (hbound : eLpNorm F 3 P ≤ ENNReal.ofReal A) :
    (∫ w, ‖F w‖ ^ 3 ∂P) ≤ A ^ 3 := by
  have hN : lpNorm F 3 P ≤ A := by
    have hn := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    simpa [lpNorm, ENNReal.toReal_ofReal hA] using hn
  rw [← r26t6c_vector_lpNorm_cube P F hF]
  exact pow_le_pow_left₀ lpNorm_nonneg hN 3

end HRS.MS.R26T6C
