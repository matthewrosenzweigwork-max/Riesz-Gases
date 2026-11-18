import HRS.MS.SuppU8Aux11

/-!
# Worker U8 aux 12: the singular integral of a Schwartz function equals `M 𝓕⁻[(2π|ξ|)^α 𝓕φ]`
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace HRS.U8

variable {d : ℕ}

theorem u8_Lam_eq (hd : 1 ≤ d) (m : ℕ) (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α) (hαm : α < 2 * m)
    (M : ℝ) (hM : ∀ ξ, u8_sym d m α ξ = M * (2 * Real.pi * ‖ξ‖) ^ α)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) (x : EuclideanSpace ℝ (Fin d)) :
    ∫ y, ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L m y) (⇑φ) x =
      (M : ℂ) * 𝓕⁻ (fun ξ : EuclideanSpace ℝ (Fin d) =>
        (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 (⇑φ) ξ) x := by
  rw [u8_Lam_phi hd m hm α hα hαm M hM φ x, Real.fourierInv_eq, ← integral_const_mul]
  congr 1; funext ξ
  rw [Circle.smul_def, Real.fourierChar_apply, hM ξ, smul_eq_mul]
  unfold u8_E
  push_cast
  ring

end HRS.U8
