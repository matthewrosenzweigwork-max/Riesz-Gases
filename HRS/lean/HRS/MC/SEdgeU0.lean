import HRS.MC.SEdgeVocab

/-!
# Packet U0: characteristic function of the scalar Gaussian (relocated proof of `sed_U0_gauss_char`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.U0

open HRS HRS.Sec7

theorem sed_U0_gauss_char_proof (v : ℝ) (hv : 0 ≤ v) (t : ℝ) :
    (∫ z : EuclideanSpace ℝ (Fin 1), Real.cos (t * z 0)
        ∂(multivariateGaussian 0 (Matrix.of fun _ _ : Fin 1 => v))) = Real.exp (-(v * t ^ 2) / 2) ∧
    (∫ z : EuclideanSpace ℝ (Fin 1), Real.sin (t * z 0)
        ∂(multivariateGaussian 0 (Matrix.of fun _ _ : Fin 1 => v))) = 0 := by
  set S : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ : Fin 1 => v with hS
  have hpsd : S.PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · ext i j; simp [hS, Matrix.conjTranspose_apply]
    · simp [hS, dotProduct, Matrix.mulVec, Fin.sum_univ_one]
      nlinarith [mul_nonneg hv (mul_self_nonneg (x 0))]
  set x : EuclideanSpace ℝ (Fin 1) := t • EuclideanSpace.single 0 1 with hx
  have hc := charFun_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin 1))) hpsd x
  have hcf : charFun (multivariateGaussian 0 S) x =
      ∫ z, Complex.exp (((t * z 0 : ℝ) : ℂ) * Complex.I) ∂(multivariateGaussian 0 S) := by
    rw [charFun_apply]
    congr 1
    ext z
    simp [hx, PiLp.inner_apply, mul_comm]
  have hq : dotProduct x.ofLp (S.mulVec x.ofLp) = v * t ^ 2 := by
    simp [hx, hS, dotProduct, Matrix.mulVec, Fin.sum_univ_one]; ring
  rw [hq] at hc
  have hint : Integrable (fun z : EuclideanSpace ℝ (Fin 1) =>
      Complex.exp (((t * z 0 : ℝ) : ℂ) * Complex.I)) (multivariateGaussian 0 S) := by
    refine Integrable.of_bound (C := 1) (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
    rw [Complex.norm_exp_ofReal_mul_I]
  have hre := integral_re hint
  have him := integral_im hint
  rw [← hcf, hc] at hre him
  have e1 : Complex.exp (↑(inner ℝ x (0 : EuclideanSpace ℝ (Fin 1))) * Complex.I -
      ↑(v * t ^ 2) / 2) = ((Real.exp (-(v * t ^ 2) / 2) : ℝ) : ℂ) := by
    simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  rw [e1] at hre him
  simp only [RCLike.re_to_complex, RCLike.im_to_complex, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.ofReal_re,
    Complex.ofReal_im] at hre him
  exact ⟨hre, him⟩


end HRS.MC.SEdge.U0
