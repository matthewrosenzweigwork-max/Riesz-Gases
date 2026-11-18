import HRS.MC.S7PIDefs

/-!
# Packet piS3, part 3: `s7_PIH_gauss_conv` (splitting of a finite Gaussian along a PSD increment)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIS3

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

/-- The convolution of two centred multivariate Gaussians adds the covariances. -/
theorem S7PIS3_mvG_conv {q : ℕ} (A B : Matrix (Fin q) (Fin q) ℝ) (hA : A.PosSemidef)
    (hB : B.PosSemidef) :
    multivariateGaussian 0 A ∗ multivariateGaussian 0 B = multivariateGaussian 0 (A + B) := by
  refine Measure.ext_of_charFun ?_
  ext t
  rw [charFun_conv, charFun_multivariateGaussian hA, charFun_multivariateGaussian hB,
    charFun_multivariateGaussian (hA.add hB), ← Complex.exp_add]
  congr 1
  simp only [Matrix.add_mulVec, dotProduct_add, inner_zero_right, Complex.ofReal_zero, zero_mul,
    zero_sub, Complex.ofReal_add]
  ring

theorem S7PIS3_cb0_integrable {q : ℕ} {G : EuclideanSpace ℝ (Fin q) → ℝ} (hG : MemCb 0 G)
    (μ : Measure (EuclideanSpace ℝ (Fin q))) [IsFiniteMeasure μ] (c : EuclideanSpace ℝ (Fin q)) :
    Integrable (fun x => G (c + x)) μ := by
  obtain ⟨hc, hb⟩ := hG
  obtain ⟨C, hC⟩ := hb 0 le_rfl
  have hGc : Continuous G := by simpa using hc.continuous
  refine Integrable.of_bound (C := C) (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  have := hC ⟨c + x, rfl⟩
  simpa [norm_iteratedFDeriv_zero] using this

theorem s7_PIH_gauss_conv_proof {q : ℕ} (S : ℝ → Matrix (Fin q) (Fin q) ℝ) (u v : ℝ)
    (hv : (S v).PosSemidef)
    (huv : (S u - S v).PosSemidef) (G : EuclideanSpace ℝ (Fin q) → ℝ) (hG : MemCb 0 G)
    (c : EuclideanSpace ℝ (Fin q)) :
    gaussHeat S G u c = ∫ k, gaussHeat S G v (c + k) ∂(multivariateGaussian 0 (S u - S v)) := by
  have hconv := S7PIS3_mvG_conv (S u - S v) (S v) huv hv
  rw [sub_add_cancel] at hconv
  unfold gaussHeat
  rw [← hconv]
  have hint : Integrable (fun x => G (c + x))
      (multivariateGaussian 0 (S u - S v) ∗ multivariateGaussian 0 (S v)) := by
    rw [hconv]; exact S7PIS3_cb0_integrable hG _ c
  rw [integral_conv hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [add_assoc]

end HRS.MC.Sec7.S7PIS3

end
