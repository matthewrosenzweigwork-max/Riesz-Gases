import HRS.Whole.Q09AAux3
import HRS.MS.MovOpAux1

/-!
# S8.2 observed-time layer, packet T8A.F05 (helper 05a): Sobolev derivative bound on real Schwartz functions

For a real Schwartz function `g` and a coordinate `i`, the partial derivative `∂_i g` satisfies
`‖∂_i g‖_{H^r} ≤ ‖g‖_{H^{r+1}}` (constant one), because `|2π ξ_i|² ≤ 1 + 4π²|ξ|²` on the Fourier side.
Route: the pointwise Fourier identity `𝓕(∂_i ψ) = 2πi ξ_i 𝓕 ψ` (Mathlib `fourier_lineDerivOp_eq`, via `HRS.Whole.Q09A`),
transferred to `fourierL2` by `fourierL2_schwartz`, then monotonicity of the Sobolev integrand.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux
open LineDeriv

variable {d : ℕ}

theorem r26t8a_f05a_fderiv_ofReal (g : SchwartzMap (Euc d) ℝ) (x v : Euc d) :
    fderiv ℝ (fun y => ((g y : ℝ) : ℂ)) x v = ((fderiv ℝ g x v : ℝ) : ℂ) := by
  have h1 : HasFDerivAt (fun y => ((g y : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ g x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (g.differentiableAt.hasFDerivAt)
  rw [h1.fderiv]
  simp

theorem r26t8a_f05a_fourier_pt (g : SchwartzMap (Euc d) ℝ) (i : Fin d) (ξ : Euc d) :
    𝓕 (fun x => ((fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ)) : ℝ) : ℂ)) ξ =
      (2 * Real.pi * Complex.I * (ξ i : ℂ)) * 𝓕 (fun x => ((g x : ℝ) : ℂ)) ξ := by
  set ψ : SchwartzMap (Euc d) ℂ := g.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM with hψdef
  have hψ : ⇑ψ = fun x => ((g x : ℝ) : ℂ) := rfl
  have hD : (fun x => ((fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ)) : ℝ) : ℂ)) =
      ⇑((LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ) : Euc d) ψ : SchwartzMap (Euc d) ℂ)) := by
    funext x
    rw [show ((LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ) : Euc d) ψ : SchwartzMap (Euc d) ℂ)) x =
        fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) from rfl, hψ,
      r26t8a_f05a_fderiv_ofReal]
  have h1 : 𝓕 ⇑((LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ) : Euc d) ψ : SchwartzMap (Euc d) ℂ)) ξ =
      (2 * Real.pi * Complex.I * (ξ i : ℂ)) * 𝓕 ⇑ψ ξ :=
    HRS.Whole.Q09A.fourier_lineDeriv_apply ψ i ξ
  rw [hD, h1, hψ]

theorem r26t8a_f05a_fourierL2_pd (g : SchwartzMap (Euc d) ℝ) (i : Fin d) :
    ∀ᵐ ξ ∂(volume : Measure (Euc d)),
      fourierL2 (fun x : Euc d => fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) ξ =
        (2 * Real.pi * Complex.I * (ξ i : ℂ)) * fourierL2 (⇑g) ξ := by
  filter_upwards [fourierL2_schwartz ((LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ) : Euc d) g : SchwartzMap (Euc d) ℝ)),
    fourierL2_schwartz g] with ξ h1 h2
  rw [h2]
  have h3 : fourierL2 (fun x : Euc d => fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) ξ =
      fourierL2 ⇑((LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ) : Euc d) g : SchwartzMap (Euc d) ℝ)) ξ := rfl
  rw [h3, h1]
  exact r26t8a_f05a_fourier_pt g i ξ

theorem r26t8a_f05a_norm_pd_le (g : SchwartzMap (Euc d) ℝ) (i : Fin d) :
    ∀ᵐ ξ ∂(volume : Measure (Euc d)),
      ‖fourierL2 (fun x : Euc d => fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) ξ‖ ^ 2 ≤
        wt ξ * ‖fourierL2 (⇑g) ξ‖ ^ 2 := by
  filter_upwards [r26t8a_f05a_fourierL2_pd g i] with ξ hξ
  rw [hξ, norm_mul, mul_pow]
  have hn : ‖(2 * Real.pi * Complex.I * (ξ i : ℂ))‖ ^ 2 ≤ wt ξ := by
    have e : ‖(2 * Real.pi * Complex.I * (ξ i : ℂ))‖ = 2 * Real.pi * |ξ i| := by
      simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [e, mul_pow]
    have hi : |ξ i| ^ 2 ≤ ‖ξ‖ ^ 2 := by
      have := PiLp.norm_apply_le ξ i
      rw [Real.norm_eq_abs] at this
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have h4 := mul_le_mul_of_nonneg_left hi (sq_nonneg (2 * Real.pi))
    unfold wt
    nlinarith [h4, Real.pi_pos]
  exact mul_le_mul_of_nonneg_right hn (sq_nonneg _)

theorem r26t8a_f05a_sobolevNormSq_pd (g : SchwartzMap (Euc d) ℝ) (i : Fin d) (r : ℝ) :
    sobolevNormSq r (fun x : Euc d => fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) ≤
      sobolevNormSq (r + 1) (⇑g) := by
  have hI1 := (HRS.MS.MovC1.movc1_memSob_schwartz
    ((LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ) : Euc d) g : SchwartzMap (Euc d) ℝ)) r).2
  have hI2 := (HRS.MS.MovC1.movc1_memSob_schwartz g (r + 1)).2
  unfold sobolevNormSq
  refine integral_mono_ae hI1 hI2 ?_
  filter_upwards [r26t8a_f05a_norm_pd_le g i] with ξ hξ
  have hw : wt ξ ^ (r + 1) = wt ξ ^ r * wt ξ := by
    rw [Real.rpow_add (wt_pos ξ), Real.rpow_one]
  show wt ξ ^ r * ‖fourierL2 (fun x : Euc d => fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) ξ‖ ^ 2 ≤
    wt ξ ^ (r + 1) * ‖fourierL2 (⇑g) ξ‖ ^ 2
  rw [hw, mul_assoc]
  exact mul_le_mul_of_nonneg_left hξ (Real.rpow_nonneg (wt_pos ξ).le r)

theorem r26t8a_f05a_sobolevNormE_pd (g : SchwartzMap (Euc d) ℝ) (i : Fin d) (r : ℝ) :
    sobolevNormE r (fun x : Euc d => fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) ≤
      sobolevNormE (r + 1) (⇑g) := by
  have h1 : HRS.PDE.ToolboxRd.MemSobolev r (fun x : Euc d => fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) :=
    HRS.MS.MovC1.movc1_memSob_schwartz ((LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ) : Euc d) g : SchwartzMap (Euc d) ℝ)) r
  have h2 : HRS.PDE.ToolboxRd.MemSobolev (r + 1) (⇑g) := HRS.MS.MovC1.movc1_memSob_schwartz g (r + 1)
  unfold sobolevNormE
  rw [if_pos h1, if_pos h2]
  exact ENNReal.ofReal_le_ofReal
    (Real.sqrt_le_sqrt (r26t8a_f05a_sobolevNormSq_pd g i r))

end HRS.MS.R26T8A

end
