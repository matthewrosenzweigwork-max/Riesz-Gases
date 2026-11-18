import HRS.MS.SuppU8Aux9

/-!
# Worker U8 aux 10: `∫ ‖y‖^{-d-α} Δ_y^m φ(x) dy = M · |D|^α φ (x)` for Schwartz `φ`
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace HRS.U8

variable {d : ℕ}

theorem u8_fourier_coe (φ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) :
    ((𝓕 φ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) : EuclideanSpace ℝ (Fin d) → ℂ) =
      𝓕 (⇑φ) :=
  SchwartzMap.fourier_coe φ

theorem u8_fourier_integrable (φ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) :
    Integrable (𝓕 (⇑φ)) := by
  rw [← u8_fourier_coe]; exact (𝓕 φ).integrable

theorem u8_fourier_continuous (φ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) :
    Continuous (𝓕 (⇑φ)) := by
  rw [← u8_fourier_coe]; exact (𝓕 φ).continuous

theorem u8_inversion (φ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ)
    (x : EuclideanSpace ℝ (Fin d)) :
    φ x = ∫ ξ, u8_E ξ x * 𝓕 (⇑φ) ξ := by
  have h := congrFun (Continuous.fourierInv_fourier_eq φ.continuous φ.integrable
    (u8_fourier_integrable φ)) x
  rw [Real.fourierInv_eq] at h
  rw [← h]
  congr 1

theorem u8_fd_phi (m : ℕ) (φ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ)
    (y x : EuclideanSpace ℝ (Fin d)) :
    u8_fd (u8_L m y) (⇑φ) x =
      ∫ ξ, ((u8_g m (inner ℝ y ξ) : ℝ) : ℂ) * (u8_E ξ x * 𝓕 (⇑φ) ξ) := by
  have hφ : (⇑φ : EuclideanSpace ℝ (Fin d) → ℂ) = fun x' => ∫ ξ, u8_E ξ x' * 𝓕 (⇑φ) ξ :=
    funext (u8_inversion φ)
  have hFint : ∀ x', Integrable (fun ξ => u8_E ξ x' * 𝓕 (⇑φ) ξ) := by
    intro x'
    exact (u8_fourier_integrable φ).bdd_mul (c := 1) (u8_E_cont x').aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => (u8_E_norm ξ x').le))
  conv_lhs => rw [hφ]
  rw [u8_fd_integral volume (u8_L m y) (fun ξ x' => u8_E ξ x' * 𝓕 (⇑φ) ξ) hFint]
  beta_reduce
  congr 1; funext ξ
  rw [u8_fd_exp (u8_L m y) (fun h => u8_E ξ h) (fun x' => u8_E ξ x' * 𝓕 (⇑φ) ξ) ?_ x]
  · congr 1
    simp only [u8_L, List.map_map, List.map_append, List.map_replicate, List.prod_append,
      List.prod_replicate, Function.comp]
    have h1 : ((1 : ℤ) • y) = y := one_zsmul y
    have h2 : ((-1 : ℤ) • y) = -y := by simp
    rw [h1, h2, ← mul_pow, u8_E_mul_neg]
    unfold u8_g
    push_cast
    rfl
  · intro x' h; rw [u8_E_add]; ring

end HRS.U8
