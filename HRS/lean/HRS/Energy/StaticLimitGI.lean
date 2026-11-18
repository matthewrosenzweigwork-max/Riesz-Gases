import Mathlib

/-!
# Finite-dimensional Gaussian integrals (work package STAT-4.21)

Hubbard–Stratonovich identity and the "complete the square" Gaussian integral used to identify
the tilted Gaussian.
-/

open MeasureTheory Complex
open scoped RealInnerProductSpace

noncomputable section

namespace HRS.StaticLimitAux

section GI

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The normalising constant of the Gaussian weight. -/
def gaussC (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] : ℂ :=
  (Real.pi / (1 / 2 : ℂ)) ^ ((Module.finrank ℝ V : ℂ) / 2)

omit [MeasurableSpace V] [BorelSpace V] in
theorem gaussC_ne_zero : gaussC V ≠ 0 := by
  unfold gaussC
  rw [Ne, Complex.cpow_eq_zero_iff]
  push_neg
  intro h
  simp at h

/-- Hubbard–Stratonovich: Fourier transform of the Gaussian weight. -/
theorem hs_gaussian (s : V) :
    ∫ ξ : V, cexp (-(1 / 2 : ℂ) * (‖ξ‖ : ℂ) ^ 2 + Complex.I * (⟪s, ξ⟫ : ℝ)) =
      gaussC V * cexp (-((‖s‖ ^ 2 : ℝ) : ℂ) / 2) := by
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := V) (b := (1 / 2 : ℂ)) (by norm_num)
    Complex.I s
  rw [h]
  unfold gaussC
  congr 2
  push_cast
  simp [Complex.I_sq]
  ring

theorem gauss_integral_eq : ∫ ξ : V, cexp (-(1 / 2 : ℂ) * (‖ξ‖ : ℂ) ^ 2) = gaussC V := by
  have := hs_gaussian (V := V) 0
  simpa using this

/-- Completing the square. -/
theorem gi_complete (T : V →L[ℝ] H) (g h : H) (ξ₀ : V) (hg : g + T ξ₀ = h)
    (hp : ∀ η, ⟪h, T η⟫ = -⟪ξ₀, η⟫) :
    ∫ ξ : V, cexp (-(1 / 2 : ℂ) * (‖ξ‖ : ℂ) ^ 2) * cexp (-(1 / 2 : ℂ) * (‖g + T ξ‖ : ℂ) ^ 2) =
      cexp (-(((‖h‖ ^ 2 + ‖ξ₀‖ ^ 2 : ℝ) : ℂ)) / 2) *
        ∫ η : V, cexp (-(1 / 2 : ℂ) * (‖η‖ : ℂ) ^ 2) * cexp (-(1 / 2 : ℂ) * (‖T η‖ : ℂ) ^ 2) := by
  rw [← integral_add_right_eq_self (μ := (volume : Measure V)) _ ξ₀, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  simp only
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have e1 : g + T (η + ξ₀) = h + T η := by rw [map_add, ← hg]; abel
  rw [e1]
  have e2 : ‖η + ξ₀‖ ^ 2 + ‖h + T η‖ ^ 2 = (‖h‖ ^ 2 + ‖ξ₀‖ ^ 2) + (‖η‖ ^ 2 + ‖T η‖ ^ 2) := by
    rw [@norm_add_sq_real V _ _ η ξ₀, @norm_add_sq_real H _ _ h (T η), hp η, real_inner_comm ξ₀ η]
    ring
  have e3 : -(1 / 2 : ℂ) * (‖η + ξ₀‖ : ℂ) ^ 2 + -(1 / 2 : ℂ) * (‖h + T η‖ : ℂ) ^ 2 =
      -(((‖η + ξ₀‖ ^ 2 + ‖h + T η‖ ^ 2 : ℝ)) : ℂ) / 2 := by push_cast; ring
  rw [e3, e2]
  push_cast
  ring

end GI

end HRS.StaticLimitAux
