import HRS.Commutator.Whole.XBBAux5

/-!
# Packet XBB, part 6: identification of `ϖ ⋆ ∂_a v_c` with a convolution against `|∇|^α v_c`

Integration by parts against the reflected translate of a Schwartz kernel, and the distributional
definition `IsFracDerivRep` of `|∇|^α v_c` applied to the test function `z ↦ Φ(x - z)`.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section
namespace HRS.Commutator.Whole.XBB
open HRS.Commutator.Whole HRS.Commutator.Whole.XLI HRS.Commutator.Whole.XNRS
variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- reflection and translation of a Schwartz function: `z ↦ F (x - z)` -/
def xbbRT (x : 𝔼) (F : 𝓢(𝔼, ℂ)) : 𝓢(𝔼, ℂ) :=
  SchwartzMap.compCLM ℝ (g := fun z : 𝔼 => x - z) (by fun_prop)
    ⟨1, 1 + ‖x‖, fun z => by
      have : ‖z‖ ≤ ‖x - z‖ + ‖x‖ := by
        have := norm_sub_le x (x - z)
        have h2 : ‖x - (x - z)‖ = ‖z‖ := by simp
        rw [h2] at this
        linarith
      nlinarith [norm_nonneg x, norm_nonneg (x - z)]⟩ F

lemma xbbRT_apply (x : 𝔼) (F : 𝓢(𝔼, ℂ)) (z : 𝔼) : xbbRT x F z = F (x - z) := rfl

lemma xbb_fourier_RT (x : 𝔼) (F : 𝓢(𝔼, ℂ)) (ξ : 𝔼) :
    𝓕 (⇑(xbbRT x F)) ξ =
      Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑F) (-ξ) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  have key : ∀ z : 𝔼, Complex.exp (((-2 * Real.pi * inner ℝ z ξ : ℝ) : ℂ) * Complex.I) • xbbRT x F z =
      (fun u : 𝔼 => (Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((-2 * Real.pi * inner ℝ u (-ξ) : ℝ) : ℂ) * Complex.I)) • F u) (x - z) := by
    intro z
    simp only [xbbRT_apply, smul_eq_mul]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    rw [← add_mul]
    congr 1
    push_cast
    simp only [inner_sub_left, inner_neg_right, Complex.ofReal_sub, Complex.ofReal_neg]
    ring
  simp_rw [key]
  rw [integral_sub_left_eq_self (fun u : 𝔼 => (Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((-2 * Real.pi * inner ℝ u (-ξ) : ℝ) : ℂ) * Complex.I)) • F u) volume x]
  simp only [smul_eq_mul, mul_assoc]
  rw [integral_const_mul]


lemma xbb_ibp {v : 𝔼 → 𝔼} (hv : XTVF v) (a c : Fin d) (ϖ : 𝓢(𝔼, ℂ)) (x : 𝔼) :
    ∫ z, ϖ (x - z) * ((xw v a c z : ℝ) : ℂ) = ∫ z, xdr a ϖ (x - z) * ((v z c : ℝ) : ℂ) := by
  have hI1 : Integrable (fun z => (ContinuousLinearMap.mul ℝ ℂ) (-(xdr a ϖ (x - z))) ((v z c : ℝ) : ℂ)) := by
    have : Integrable (⇑(xvmul v c (xbbRT x (xdr a ϖ)))) volume := (xvmul v c (xbbRT x (xdr a ϖ))).integrable
    refine (this.neg).congr (Eventually.of_forall fun z => ?_)
    simp only [xvmul_apply hv, xbbRT_apply, ContinuousLinearMap.mul_apply', Pi.neg_apply]
    ring
  have hI2 : Integrable (fun z => (ContinuousLinearMap.mul ℝ ℂ) (ϖ (x - z)) ((xw v a c z : ℝ) : ℂ)) := by
    have : Integrable (⇑(xwmul v a c (xbbRT x ϖ))) volume := (xwmul v a c (xbbRT x ϖ)).integrable
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [xwmul_apply hv, xbbRT_apply, ContinuousLinearMap.mul_apply']
    ring
  have hI3 : Integrable (fun z => (ContinuousLinearMap.mul ℝ ℂ) (ϖ (x - z)) ((v z c : ℝ) : ℂ)) := by
    have : Integrable (⇑(xvmul v c (xbbRT x ϖ))) volume := (xvmul v c (xbbRT x ϖ)).integrable
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [xvmul_apply hv, xbbRT_apply, ContinuousLinearMap.mul_apply']
    ring
  have hf : ∀ z ∈ tsupport (fun z : 𝔼 => ((v z c : ℝ) : ℂ)),
      HasLineDerivAt ℝ (fun z : 𝔼 => ϖ (x - z)) (-(xdr a ϖ (x - z))) z (xe a) := by
    intro z _
    have h1 : HasFDerivAt (fun z : 𝔼 => x - z) (-(ContinuousLinearMap.id ℝ 𝔼)) z :=
      (hasFDerivAt_id z).const_sub x
    have h2 := ϖ.differentiableAt.hasFDerivAt.comp z h1
    have h3 := h2.hasLineDerivAt (xe a)
    have hval : (fderiv ℝ (⇑ϖ) (x - z) ∘L (-ContinuousLinearMap.id ℝ 𝔼)) (xe a) =
        -(xdr a ϖ (x - z)) := by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
        ContinuousLinearMap.id_apply, map_neg]
      rw [xdr_apply, ϖ.differentiableAt.lineDeriv_eq_fderiv]
    rw [hval] at h3
    exact h3
  have hg : ∀ z ∈ tsupport (fun z : 𝔼 => ϖ (x - z)),
      HasLineDerivAt ℝ (fun z : 𝔼 => ((v z c : ℝ) : ℂ)) ((xw v a c z : ℝ) : ℂ) z (xe a) := by
    intro z _
    have h1 : HasFDerivAt (fun y => ((v y c : ℝ) : ℂ))
        (Complex.ofRealCLM.comp (fderiv ℝ (fun y => v y c) z)) z :=
      Complex.ofRealCLM.hasFDerivAt.comp z (((hv c).1.differentiable (by simp)) z).hasFDerivAt
    have h3 := h1.hasLineDerivAt (xe a)
    have hval : (Complex.ofRealCLM.comp (fderiv ℝ (fun y => v y c) z)) (xe a) = ((xw v a c z : ℝ) : ℂ) := by
      simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
      rw [xw_eq_fderiv v a c hv z]
    rw [hval] at h3
    exact h3
  have := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure 𝔼)) (B := ContinuousLinearMap.mul ℝ ℂ) (v := xe a)
    (f := fun z : 𝔼 => ϖ (x - z)) (f' := fun z => -(xdr a ϖ (x - z)))
    (g := fun z : 𝔼 => ((v z c : ℝ) : ℂ)) (g' := fun z => ((xw v a c z : ℝ) : ℂ))
    hI1 hI2 hI3 hf hg
  simp only [ContinuousLinearMap.mul_apply'] at this
  rw [this, ← integral_neg]
  congr 1
  funext z
  ring


lemma xbb_fourier_xdr (c : Fin d) (f : 𝓢(𝔼, ℂ)) (ξ : 𝔼) :
    𝓕 (⇑(xdr c f)) ξ = (2 * Real.pi * Complex.I * ((ξ c : ℝ) : ℂ)) * 𝓕 (⇑f) ξ := by
  simpa only [SchwartzMap.fourier_coe] using fourier_xdr c f ξ

lemma xbb_fourierInv_fourier (S : 𝓢(𝔼, ℂ)) : 𝓕⁻ (𝓕 (⇑S)) = ⇑S := by
  have h1 : (𝓕⁻ (𝓕 S) : 𝓢(𝔼, ℂ)) = S := FourierTransform.fourierInv_fourier_eq S
  have h2 := congrArg (⇑) h1
  rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe] at h2
  exact h2

/-- the identification of `ϖ ⋆ ∂_a v_c` with the convolution of `Φ = ∂_a |∇|^{-α} ϖ` against
`w_c = |∇|^α v_c` -/
lemma xbb_ident {v : 𝔼 → 𝔼} (hv : XTVF v) (a c : Fin d) {α : ℝ} (hα : 0 < α) {wc : 𝔼 → ℝ}
    (hrep : HRS.Whole.IsFracDerivRep α (fun x => v x c) wc) (ϖ Φ : 𝓢(𝔼, ℂ))
    (hΦ : ∀ ξ : 𝔼, 𝓕 (⇑Φ) ξ = (2 * Real.pi * Complex.I * ((ξ a : ℝ) : ℂ)) *
      (((2 * Real.pi * ‖ξ‖) ^ (-α) : ℝ) : ℂ) * 𝓕 (⇑ϖ) ξ) (x : 𝔼) :
    ∫ z, ϖ (x - z) * ((xw v a c z : ℝ) : ℂ) = ∫ z, Φ (x - z) * ((wc z : ℝ) : ℂ) := by
  rw [xbb_ibp hv a c ϖ x]
  have hF : ∀ ξ : 𝔼, (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 (⇑(xbbRT x Φ)) ξ =
      𝓕 (⇑(xbbRT x (xdr a ϖ))) ξ := by
    intro ξ
    rw [xbb_fourier_RT, xbb_fourier_RT, hΦ (-ξ), xbb_fourier_xdr]
    by_cases hξ : ξ = 0
    · subst hξ
      simp [Real.zero_rpow hα.ne']
    · have hw : 0 < 2 * Real.pi * ‖ξ‖ := by
        have := norm_pos_iff.2 hξ
        positivity
      have h1 : (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * (((2 * Real.pi * ‖ξ‖) ^ (-α) : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, ← Real.rpow_add hw]; simp
      rw [norm_neg]
      linear_combination (Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) *
        (2 * Real.pi * Complex.I * (((-ξ) a : ℝ) : ℂ)) * 𝓕 (⇑ϖ) (-ξ)) * h1
  have hinv : 𝓕⁻ (fun ξ : 𝔼 => (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 (⇑(xbbRT x Φ)) ξ) =
      ⇑(xbbRT x (xdr a ϖ)) := by
    have e : (fun ξ : 𝔼 => (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 (⇑(xbbRT x Φ)) ξ) =
        𝓕 (⇑(xbbRT x (xdr a ϖ))) := funext hF
    rw [e]
    exact xbb_fourierInv_fourier _
  obtain ⟨-, -, h3⟩ := hrep (xbbRT x Φ)
  rw [hinv] at h3
  calc ∫ z, xdr a ϖ (x - z) * ((v z c : ℝ) : ℂ)
      = ∫ z, ((v z c : ℝ) : ℂ) * (xbbRT x (xdr a ϖ)) z := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only [xbbRT_apply]; ring
    _ = ∫ z, ((wc z : ℝ) : ℂ) * (xbbRT x Φ) z := h3
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only [xbbRT_apply]; ring

end HRS.Commutator.Whole.XBB
