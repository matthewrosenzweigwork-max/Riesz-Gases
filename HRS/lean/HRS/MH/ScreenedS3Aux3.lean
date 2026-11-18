import HRS.MH.ScreenedS3Aux2

/-!
# Packet S3, part 3: the Schwartz functions `Θ = ∂_iφ(y - ·)` and `Φ = 𝓕⁻ Θ`

`s3Theta φ i y : 𝓢(ℝ^d, ℂ)` is `x ↦ ∂_iφ(y - x)`; `s3Phi φ i y = 𝓕⁻ Θ` is explicitly
`ξ ↦ e^{2πi⟨y,ξ⟩} · 2πi ξ_i · 𝓕φ(ξ)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

/-- Complexification of a real Schwartz function. -/
def s3Cx (φ : SchwartzMap (Euc d) ℝ) : SchwartzMap (Euc d) ℂ :=
  φ.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM

lemma s3Cx_apply (φ : SchwartzMap (Euc d) ℝ) (x : Euc d) : s3Cx φ x = ((φ x : ℝ) : ℂ) := rfl

/-- The directional derivative `∂_iφ` of the complexification. -/
def s3D (φ : SchwartzMap (Euc d) ℝ) (i : Fin d) : SchwartzMap (Euc d) ℂ :=
  LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) (s3Cx φ)

lemma s3D_apply (φ : SchwartzMap (Euc d) ℝ) (i : Fin d) (x : Euc d) :
    s3D φ i x = ((fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) : ℝ) : ℂ) := by
  unfold s3D
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have h : HasFDerivAt (s3Cx φ) (Complex.ofRealCLM.comp (fderiv ℝ φ x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (φ.differentiableAt.hasFDerivAt)
  rw [h.fderiv]
  rfl

/-- `Θ(x) = ∂_iφ(y - x)`. -/
def s3Theta (φ : SchwartzMap (Euc d) ℝ) (i : Fin d) (y : Euc d) : SchwartzMap (Euc d) ℂ :=
  SchwartzMap.compCLM ℝ (g := fun x : Euc d => y - x) (by fun_prop)
    ⟨1, 1 + ‖y‖, fun x => by
      have : ‖x‖ ≤ ‖y - x‖ + ‖y‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub (0 : Euc d) (y - x) y
        calc ‖x‖ = ‖y - (y - x)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖y‖ + ‖y - x‖ := norm_sub_le _ _
          _ = _ := by ring
      nlinarith [norm_nonneg y, norm_nonneg (y - x)]⟩ (s3D φ i)

lemma s3Theta_apply (φ : SchwartzMap (Euc d) ℝ) (i : Fin d) (y x : Euc d) :
    s3Theta φ i y x = ((fderiv ℝ φ (y - x) (EuclideanSpace.single i (1 : ℝ)) : ℝ) : ℂ) := by
  show s3D φ i (y - x) = _
  exact s3D_apply φ i _

/-- `Φ = 𝓕⁻ Θ`. -/
def s3Phi (φ : SchwartzMap (Euc d) ℝ) (i : Fin d) (y : Euc d) : SchwartzMap (Euc d) ℂ :=
  𝓕⁻ (s3Theta φ i y)

lemma fourier_s3Phi (φ : SchwartzMap (Euc d) ℝ) (i : Fin d) (y : Euc d) :
    (𝓕 (⇑(s3Phi φ i y)) : Euc d → ℂ) = ⇑(s3Theta φ i y) := by
  have h : (𝓕 (s3Phi φ i y) : SchwartzMap (Euc d) ℂ) = s3Theta φ i y :=
    FourierInvPair.fourier_fourierInv_eq _
  rw [← SchwartzMap.fourier_coe, h]

lemma s3Phi_apply (φ : SchwartzMap (Euc d) ℝ) (i : Fin d) (y ξ : Euc d) :
    s3Phi φ i y ξ = Complex.exp (2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ)) *
      ((2 * Real.pi * Complex.I * (ξ i : ℂ)) * 𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ) := by
  have h1 : (⇑(s3Phi φ i y) : Euc d → ℂ) = 𝓕⁻ (⇑(s3Theta φ i y)) := SchwartzMap.fourierInv_coe _
  rw [h1, Real.fourierInv_eq']
  have hF := HRS.Commutator.Whole.cmxMY_fourier_partial (s3Cx φ) i ξ
  have hD : (fun ζ : Euc d => fderiv ℝ (s3Cx φ) ζ (EuclideanSpace.single i (1 : ℝ))) =
      ⇑(s3D φ i) := by
    funext ζ; unfold s3D; rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [hD] at hF
  have hF' : 𝓕 (⇑(s3D φ i)) ξ = (2 * Real.pi * Complex.I * (ξ i : ℂ)) *
      𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ := hF
  rw [← hF', Real.fourier_eq']
  have key : ∀ x : Euc d, Complex.exp (↑(2 * Real.pi * inner ℝ x ξ) * Complex.I) •
      (s3Theta φ i y) x = (fun z : Euc d => (Complex.exp (2 * Real.pi * Complex.I *
        (inner ℝ y ξ : ℝ)) * Complex.exp (↑(-2 * Real.pi * inner ℝ z ξ) * Complex.I)) •
        s3D φ i z) (y - x) := by
    intro x
    simp only [s3Theta, SchwartzMap.compCLM_apply, Function.comp_apply, smul_eq_mul]
    rw [mul_assoc]
    congr 1
    rw [← Complex.exp_add]
    congr 1
    rw [inner_sub_left]
    push_cast
    ring
  have := integral_sub_left_eq_self
    (fun z : Euc d => (Complex.exp (2 * Real.pi * Complex.I *
        (inner ℝ y ξ : ℝ)) * Complex.exp (↑(-2 * Real.pi * inner ℝ z ξ) * Complex.I)) •
        s3D φ i z) volume y
  simp_rw [key]
  rw [this]
  simp only [smul_eq_mul, mul_assoc]
  rw [integral_const_mul]

lemma norm_s3Phi_le (φ : SchwartzMap (Euc d) ℝ) (i : Fin d) (y ξ : Euc d) :
    ‖s3Phi φ i y ξ‖ ≤ ‖ξ‖ * (2 * Real.pi * ‖𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ‖) := by
  rw [s3Phi_apply, norm_mul, norm_mul, Complex.norm_exp]
  have h0 : (2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ)).re = 0 := by simp
  rw [h0, Real.exp_zero, one_mul]
  have hi : |ξ i| ≤ ‖ξ‖ := by simpa using PiLp.norm_apply_le ξ i
  have hc : ‖(2 * Real.pi * Complex.I * (ξ i : ℂ))‖ = 2 * Real.pi * |ξ i| := by
    simp [norm_mul, abs_of_pos Real.pi_pos]
  rw [hc]
  have : 2 * Real.pi * |ξ i| ≤ 2 * Real.pi * ‖ξ‖ :=
    mul_le_mul_of_nonneg_left hi (by positivity)
  calc 2 * Real.pi * |ξ i| * ‖𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ‖
      ≤ 2 * Real.pi * ‖ξ‖ * ‖𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ‖ :=
        mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ = _ := by ring

lemma integral_s3Theta (φ : SchwartzMap (Euc d) ℝ) (i : Fin d) (y : Euc d) :
    ∫ x : Euc d, s3Theta φ i y x = 0 := by
  have h1 : ∫ x : Euc d, s3Theta φ i y x = ∫ x : Euc d, s3D φ i x :=
    integral_sub_left_eq_self (fun z => s3D φ i z) volume y
  rw [h1]
  have hF := HRS.Commutator.Whole.cmxMY_fourier_partial (s3Cx φ) i 0
  have hD : (fun ζ : Euc d => fderiv ℝ (s3Cx φ) ζ (EuclideanSpace.single i (1 : ℝ))) =
      ⇑(s3D φ i) := by
    funext ζ; unfold s3D; rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [hD] at hF
  have : 𝓕 (⇑(s3D φ i)) 0 = 0 := by rw [hF]; simp
  rw [Real.fourier_eq'] at this
  simpa using this

lemma convFun_eq_integral_theta (φ : SchwartzMap (Euc d) ℝ) (i : Fin d) (y : Euc d) (s : ℝ) :
    ((HRS.Whole.convFun (rieszKernel d s)
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y : ℝ) : ℂ) =
      ∫ x : Euc d, ((rieszKernel d s x : ℝ) : ℂ) * s3Theta φ i y x := by
  unfold HRS.Whole.convFun
  rw [← integral_complex_ofReal]
  calc ∫ z : Euc d, ((HRS.Whole.rieszKernel d s (y - z) *
          fderiv ℝ φ z (EuclideanSpace.single i 1) : ℝ) : ℂ)
      = ∫ z : Euc d, ((rieszKernel d s (y - z) : ℝ) : ℂ) * s3Theta φ i y (y - z) := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only [s3Theta_apply, sub_sub_cancel]
        push_cast; ring
    _ = _ := integral_sub_left_eq_self
        (fun z : Euc d => ((rieszKernel d s z : ℝ) : ℂ) * s3Theta φ i y z) volume y

end HRS.MH.Screened
