import HRS.MS.R26T6CI07CubeLp

/-! S11.1 I07: identify the L3 norm cube with the cubic moment. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace HRS.MS.R26T6C
open HRS
variable {d : ℕ}

theorem r26t6c_lpNorm_three_pow
    (mu : Measure (Euc d)) (f : Euc d → ℝ) (hf : MemLp f 3 mu) :
    lpNorm f 3 mu ^ 3 = ∫ x, |f x| ^ 3 ∂mu := by
  have hi : Integrable (fun x => |f x| ^ 3) mu := by
    simpa only [Real.norm_eq_abs] using
      (hf.integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0))
  have hI0 : 0 ≤ ∫ x, |f x| ^ 3 ∂mu :=
    integral_nonneg (fun _ => by positivity)
  rw [lpNorm_eq_integral_norm_rpow_toReal
    (by norm_num : (3 : ENNReal) ≠ 0)
    (by norm_num : (3 : ENNReal) ≠ ⊤) hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
  have heq : (∫ x, |f x| ^ (3 : ℝ) ∂mu) =
      ∫ x, |f x| ^ (3 : ℕ) ∂mu := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      simpa using (Real.rpow_natCast |f x| 3)
  rw [heq]
  have hdiv : (3 : ℝ)⁻¹ = 1 / 3 := by ring
  rw [hdiv, ← Real.rpow_natCast, ← Real.rpow_mul hI0]
  norm_num

end HRS.MS.R26T6C
