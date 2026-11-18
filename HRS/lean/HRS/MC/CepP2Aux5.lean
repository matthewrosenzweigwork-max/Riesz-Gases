import HRS.MC.CepP2Aux4

/-!
# Packet CEPP2 (aux 5): a finite measure with rapidly decaying `∫ e^{iℓ} dν` has a smooth density-functional
-/

open MeasureTheory
open scoped FourierTransform
noncomputable section
namespace HRS.MC.CepP2
variable {n : ℕ}

/-- The bilinear form `(ζ, q) ↦ ℓ_ζ(q)`. -/
def ellB : XS n →L[ℝ] XS n →L[ℝ] ℝ :=
  ((ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin n)))
      (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin n)))) +
    ∑ k : Fin n, ((ContinuousLinearMap.mul ℝ ℝ).bilinearComp
      ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n))))
      ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n)))))

lemma ellB_apply (ζ q : XS n) : ellB ζ q = ell ζ q := by
  simp [ellB, ell_apply, PiLp.inner_apply, mul_comm]

/-- `G_ν(ζ) = ∫ e^{i ℓ_ζ(p)} dν(p)`. -/
def Gf (ν : Measure (XS n)) (ζ : XS n) : ℂ := ∫ p, Complex.exp ((ell ζ p : ℂ) * Complex.I) ∂ν

/-- The bilinear form used for `e^{-i ℓ}` in the `𝐞`-convention. -/
def Lc : XS n →L[ℝ] XS n →L[ℝ] ℝ := (2 * Real.pi)⁻¹ • ellB

lemma Lc_apply (ζ q : XS n) : (ContinuousLinearMap.toLinearMap₁₂ (Lc (n := n))) ζ q = (2 * Real.pi)⁻¹ * ell ζ q := by
  simp [Lc, ellB_apply]

lemma fourierIntegral_Gf (ν : Measure (XS n)) (q : XS n) :
    VectorFourier.fourierIntegral Real.fourierChar (volume : Measure (XS n))
      (ContinuousLinearMap.toLinearMap₁₂ (Lc (n := n))) (Gf ν) q =
    ∫ ζ, Gf ν ζ * Complex.exp (-(ell ζ q : ℂ) * Complex.I) := by
  unfold VectorFourier.fourierIntegral
  refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
  simp only [Lc_apply, smul_eq_mul, Circle.smul_def, Real.fourierChar_apply]
  rw [mul_comm]
  congr 2
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  push_cast
  field_simp


lemma continuous_ell_pair : Continuous fun z : XS n × XS n => ell z.1 z.2 := by
  simp only [ell_apply]; fun_prop

lemma continuous_Gf (ν : Measure (XS n)) [IsFiniteMeasure ν] : Continuous (Gf ν) := by
  unfold Gf
  refine continuous_of_dominated (bound := fun _ => (1 : ℝ)) (fun ζ => ?_) (fun ζ => ?_)
    (integrable_const _) (Filter.Eventually.of_forall fun p => ?_)
  · exact (Continuous.aestronglyMeasurable (by
      have : Continuous fun p : XS n => ell ζ p := (ell ζ).continuous
      fun_prop))
  · refine Filter.Eventually.of_forall fun p => ?_
    rw [Complex.norm_exp_ofReal_mul_I]
  · have : Continuous fun ζ : XS n => ell ζ p := by simp only [ell_apply]; fun_prop
    fun_prop

/-- The normalising constant `(2π)^{-(n+1)}`. -/
def cst (n : ℕ) : ℝ := ((2 * Real.pi) ^ (n + 1))⁻¹

/-- The candidate density `H(q) = (2π)^{-(n+1)} ∫ G_ν(ζ) e^{-i ℓ_ζ(q)} dζ`. -/
def Hf (ν : Measure (XS n)) (q : XS n) : ℂ :=
  (cst n : ℂ) * ∫ ζ, Gf ν ζ * Complex.exp (-(ell ζ q : ℂ) * Complex.I)

lemma contDiff_Hf (ν : Measure (XS n))
    (hν : ∀ m : ℕ, Integrable (fun ζ : XS n => ‖ζ‖ ^ m * ‖Gf ν ζ‖)) : ContDiff ℝ smTop (Hf ν) := by
  have h := VectorFourier.contDiff_fourierIntegral (E := ℂ) (L := Lc (n := n)) (f := Gf ν)
    (μ := (volume : Measure (XS n))) (N := ⊤) (fun m _ => hν m)
  have e : Hf ν = fun q => (cst n : ℂ) * VectorFourier.fourierIntegral Real.fourierChar
      (volume : Measure (XS n)) (ContinuousLinearMap.toLinearMap₁₂ (Lc (n := n))) (Gf ν) q := by
    funext q; rw [fourierIntegral_Gf]; rfl
  rw [e]
  exact contDiff_const.mul h


theorem dens_identity (ν : Measure (XS n)) [IsFiniteMeasure ν]
    (hν : ∀ m : ℕ, Integrable (fun ζ : XS n => ‖ζ‖ ^ m * ‖Gf ν ζ‖))
    {φ : XS n → ℝ} (hφ : ContDiff ℝ smTop φ) (hc : HasCompactSupport φ) :
    ((∫ p, φ p ∂ν : ℝ) : ℂ) = ∫ q, (φ q : ℂ) * Hf ν q := by
  obtain ⟨hphat, hinv⟩ := inv_X hφ hc
  have hG : Integrable (fun ζ => ‖Gf ν ζ‖) := by simpa using hν 0
  have hGc := continuous_Gf ν
  have hφint : Integrable φ (volume : Measure (XS n)) :=
    hφ.continuous.integrable_of_hasCompactSupport hc
  -- Step 1
  have s1 : ((∫ p, φ p ∂ν : ℝ) : ℂ) = ∫ p, (φ p : ℂ) ∂ν := (integral_ofReal).symm
  have s2 : ∫ p, (φ p : ℂ) ∂ν =
      (cst n : ℂ) * ∫ p, ∫ ζ, Complex.exp ((ell ζ p : ℂ) * Complex.I) * phat φ ζ ∂volume ∂ν := by
    have : ∀ p, (φ p : ℂ) = (cst n : ℂ) * ∫ ζ, Complex.exp ((ell ζ p : ℂ) * Complex.I) * phat φ ζ := by
      intro p
      rw [hinv p, Complex.real_smul]; rfl
    simp_rw [this]
    rw [integral_const_mul]
  have s3 : ∫ p, ∫ ζ, Complex.exp ((ell ζ p : ℂ) * Complex.I) * phat φ ζ ∂volume ∂ν =
      ∫ ζ, Gf ν ζ * phat φ ζ := by
    rw [integral_integral_swap]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
      simp only
      rw [integral_mul_const]; rfl
    · have hb : Integrable (fun z : XS n × XS n => (1 : ℝ) * ‖phat φ z.2‖) (ν.prod volume) :=
        (integrable_const (1 : ℝ)).mul_prod hphat.norm
      refine hb.mono' ?_ ?_
      · refine AEStronglyMeasurable.mul ?_ (hphat.aestronglyMeasurable.comp_snd)
        exact (Continuous.aestronglyMeasurable (by
          have := continuous_ell_pair (n := n)
          fun_prop))
      · refine Filter.Eventually.of_forall fun z => ?_
        show ‖Complex.exp ((ell z.2 z.1 : ℂ) * Complex.I) * phat φ z.2‖ ≤ 1 * ‖phat φ z.2‖
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have s4 : ∫ ζ, Gf ν ζ * phat φ ζ = ∫ q, (φ q : ℂ) * ∫ ζ, Gf ν ζ * Complex.exp (-(ell ζ q : ℂ) * Complex.I) := by
    have e1 : ∀ ζ, Gf ν ζ * phat φ ζ = ∫ q, Gf ν ζ * ((φ q : ℂ) * Complex.exp (-(ell ζ q : ℂ) * Complex.I)) := by
      intro ζ; unfold phat; rw [integral_const_mul]
    simp_rw [e1]
    rw [integral_integral_swap]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
      dsimp only
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
      ring
    · have hb : Integrable (fun z : XS n × XS n => ‖Gf ν z.1‖ * |φ z.2|) (volume.prod volume) :=
        hG.mul_prod hφint.abs
      refine hb.mono' ?_ ?_
      · refine Continuous.aestronglyMeasurable ?_
        have := continuous_ell_pair (n := n)
        have h2 : Continuous fun z : XS n × XS n => ell z.1 z.2 := this
        show Continuous fun z : XS n × XS n => Gf ν z.1 * ((φ z.2 : ℂ) * Complex.exp (-(ell z.1 z.2 : ℂ) * Complex.I))
        have h3 := hGc
        have h4 := hφ.continuous
        fun_prop
      · refine Filter.Eventually.of_forall fun z => ?_
        show ‖Gf ν z.1 * ((φ z.2 : ℂ) * Complex.exp (-(ell z.1 z.2 : ℂ) * Complex.I))‖ ≤ ‖Gf ν z.1‖ * |φ z.2|
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have : ‖Complex.exp (-(ell z.1 z.2 : ℂ) * Complex.I)‖ = 1 := by
          rw [show -(ell z.1 z.2 : ℂ) * Complex.I = ((-(ell z.1 z.2) : ℝ) : ℂ) * Complex.I by push_cast; ring]
          exact Complex.norm_exp_ofReal_mul_I _
        rw [this]; simp
  rw [s1, s2, s3, s4]
  simp only [Hf]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  ring


theorem dens_of_fourier (ν : Measure (XS n)) [IsFiniteMeasure ν]
    (hν : ∀ m : ℕ, Integrable (fun ζ : XS n => ‖ζ‖ ^ m * ‖Gf ν ζ‖)) :
    ∃ h : XS n → ℝ, ContDiff ℝ smTop h ∧ ∀ φ : XS n → ℝ, ContDiff ℝ smTop φ → HasCompactSupport φ →
      ∫ p, φ p ∂ν = ∫ q, φ q * h q := by
  refine ⟨fun q => (Hf ν q).re, Complex.reCLM.contDiff.comp (contDiff_Hf ν hν), fun φ hφ hc => ?_⟩
  have h := congrArg Complex.re (dens_identity ν hν hφ hc)
  rw [Complex.ofReal_re] at h
  rw [h]
  have hcont : Continuous fun q : XS n => (φ q : ℂ) * Hf ν q :=
    (Complex.continuous_ofReal.comp hφ.continuous).mul (contDiff_Hf ν hν).continuous
  have hcs : HasCompactSupport fun q : XS n => (φ q : ℂ) * Hf ν q :=
    (hc.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)).mul_right
  have hint : Integrable (fun q : XS n => (φ q : ℂ) * Hf ν q) := hcont.integrable_of_hasCompactSupport hcs
  have := integral_re hint
  simp only [RCLike.re_to_complex] at this
  rw [← this]
  simp [Complex.re_ofReal_mul]

end HRS.MC.CepP2
