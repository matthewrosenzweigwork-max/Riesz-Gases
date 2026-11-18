import HRS.MH.CommSuperDefs

/-!
# CS6: scaling of the correction `o_N` under the dilation `Λ ↦ (t^d)⁻¹ Λ` (packet `oN_scale`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MH.CommSuper

variable {d N : ℕ} {s : ℝ}

theorem cs6_rpow_dilate {d : ℕ} {s t Λ : ℝ} (hd : 1 ≤ d) (ht : 0 < t) (hΛ : 0 < Λ) :
    ((t ^ d)⁻¹ * Λ) ^ (s / d) = (t ^ s)⁻¹ * Λ ^ (s / d) := by
  have hdR : (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    exact this.ne'
  have hT : (t ^ d : ℝ) = t ^ (d : ℝ) := (Real.rpow_natCast t d).symm
  have hpowsd : (t ^ d) ^ (s / d) = t ^ s := by
    rw [hT, ← Real.rpow_mul ht.le]
    congr 1
    field_simp
  rw [Real.mul_rpow (inv_nonneg.mpr (pow_nonneg ht.le d)) hΛ.le,
    Real.inv_rpow (pow_nonneg ht.le d), hpowsd]

theorem cs6_log_dilate {d N : ℕ} {t Λ : ℝ} (hd : 1 ≤ d) (hN : 1 ≤ N) (ht : 0 < t) (hΛ : 0 < Λ) :
    Real.log (N * ((t ^ d)⁻¹ * Λ)) = Real.log (N * Λ) - d * Real.log t := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNΛ : (0 : ℝ) < N * Λ := mul_pos hNR hΛ
  have htd : (0 : ℝ) < t ^ d := pow_pos ht d
  rw [show (N : ℝ) * ((t ^ d)⁻¹ * Λ) = (N * Λ) / t ^ d by field_simp,
    Real.log_div hNΛ.ne' htd.ne', Real.log_pow]

theorem oN_scale_proof (hd : 1 ≤ d) {t Λ : ℝ} (ht : 0 < t) (hΛ : 0 < Λ) (C₀ : ℝ) (hN : 1 ≤ N) :
    oNΛ d s C₀ ((t ^ d)⁻¹ * Λ) N =
      (t ^ s)⁻¹ * (C₀ * Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1)) +
        (if s = 0 then Real.log (N * Λ) / (2 * d * N) - Real.log t / (2 * N) else 0) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  unfold oNΛ
  rw [cs6_rpow_dilate hd ht hΛ]
  by_cases hs : s = 0
  · subst hs
    rw [if_pos rfl, if_pos rfl, cs6_log_dilate hd hN ht hΛ]
    simp only [zero_div, Real.rpow_zero, mul_one, one_mul, zero_mul, Real.rpow_zero]
    field_simp
    ring
  · rw [if_neg hs, if_neg hs]
    ring

end HRS.MH.CommSuper
