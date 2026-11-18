import HRS.MS.R26T6CI09

/-!
# S11.1 I11 — cubic moment bounds give exact L³ coordinate norms

This works for arbitrary measure and does not assume a density, a Gaussian
law or a pointwise envelope. It is the quantitative input to I09.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole

theorem r26t6c_generic_lpNorm_cube {Omega : Type*}
    [MeasurableSpace Omega] (P : Measure Omega) (f : Omega → ℝ)
    (hf : MemLp f 3 P) :
    lpNorm f 3 P ^ 3 = ∫ w, |f w| ^ 3 ∂P := by
  have hi : Integrable (fun w => |f w| ^ 3) P := by
    simpa only [Real.norm_eq_abs] using
      (hf.integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0))
  have hI0 : 0 ≤ ∫ w, |f w| ^ 3 ∂P :=
    integral_nonneg (fun _ => by positivity)
  rw [lpNorm_eq_integral_norm_rpow_toReal
    (by norm_num : (3 : ℝ≥0∞) ≠ 0)
    (by norm_num : (3 : ℝ≥0∞) ≠ ∞) hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
  have heq : (∫ w, |f w| ^ (3 : ℝ) ∂P) =
      ∫ w, |f w| ^ (3 : ℕ) ∂P := by
    apply integral_congr_ae
    exact ae_of_all _ fun w => by
      simpa using (Real.rpow_natCast |f w| 3)
  rw [heq]
  have hdiv : (3 : ℝ)⁻¹ = 1 / 3 := by ring
  rw [hdiv, ← Real.rpow_natCast, ← Real.rpow_mul hI0]
  norm_num

theorem r26t6c_cube_bound_to_eLpNorm {Omega : Type*}
    [MeasurableSpace Omega] (P : Measure Omega) (f : Omega → ℝ)
    (hf : MemLp f 3 P) (C : ℝ) (hC : 0 ≤ C)
    (hbound : (∫ w, |f w| ^ 3 ∂P) ≤ C ^ 3) :
    eLpNorm f 3 P ≤ ENNReal.ofReal C := by
  have hp := r26t6c_generic_lpNorm_cube P f hf
  have hn0 : 0 ≤ lpNorm f 3 P := lpNorm_nonneg
  have hle : lpNorm f 3 P ≤ C := by
    by_contra hn
    have hx : C < lpNorm f 3 P := lt_of_not_ge hn
    have hcube : C ^ 3 < lpNorm f 3 P ^ 3 :=
      pow_lt_pow_left₀ hx hC (by norm_num)
    linarith [hp, hbound]
  rw [← ofReal_lpNorm hf]
  exact ENNReal.ofReal_le_ofReal hle

end HRS.MS.R26T6C
