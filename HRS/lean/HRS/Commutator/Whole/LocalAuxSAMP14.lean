import HRS.Commutator.Whole.LocalAuxSAMP13

/-!
# Convolution and `𝓕⁻` (packet CMX-SAMP, helper file 14)
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff Convolution

noncomputable section

namespace HRS.Commutator.Whole.SAMP1

open HRS HRS.Whole HRS.Commutator.Whole

variable {d : ℕ}

lemma conv_fourierInv {k G : Euc d → ℂ} (hk : Integrable k) (hG : Integrable G) (x : Euc d) :
    ∫ t, k t * 𝓕⁻ G (x - t) = 𝓕⁻ (fun ξ => 𝓕 k ξ * G ξ) x := by
  have e1 : ∀ t : Euc d, k t * 𝓕⁻ G (x - t) =
      ∫ ξ : Euc d, k t * (Complex.exp (((2 * Real.pi * inner ℝ ξ (x - t) : ℝ) : ℂ) * Complex.I) *
        G ξ) := by
    intro t
    rw [Real.fourierInv_eq', ← integral_const_mul]
    simp only [smul_eq_mul]
  simp_rw [e1]
  have hint : Integrable (fun p : Euc d × Euc d => k p.1 * (Complex.exp
      (((2 * Real.pi * inner ℝ p.2 (x - p.1) : ℝ) : ℂ) * Complex.I) * G p.2))
      (volume.prod volume) := by
    have hb : Integrable (fun p : Euc d × Euc d => ‖k p.1‖ * ‖G p.2‖) (volume.prod volume) :=
      hk.norm.mul_prod hG.norm
    refine hb.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have h1 : AEStronglyMeasurable (fun p : Euc d × Euc d => k p.1) (volume.prod volume) :=
        hk.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
      have h2 : AEStronglyMeasurable (fun p : Euc d × Euc d => G p.2) (volume.prod volume) :=
        hG.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
      have h3 : Continuous (fun p : Euc d × Euc d => Complex.exp
          (((2 * Real.pi * inner ℝ p.2 (x - p.1) : ℝ) : ℂ) * Complex.I)) := by fun_prop
      exact h1.mul (h3.aestronglyMeasurable.mul h2)
    · rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [integral_integral_swap hint]
  rw [Real.fourierInv_eq']
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul]
  rw [Real.fourier_eq', ← integral_mul_const, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul]
  have : Complex.exp (((2 * Real.pi * inner ℝ ξ (x - t) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((-2 * Real.pi * inner ℝ t ξ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add, inner_sub_right, real_inner_comm ξ t]
    congr 1; push_cast; ring
  rw [this]; ring

end HRS.Commutator.Whole.SAMP1
