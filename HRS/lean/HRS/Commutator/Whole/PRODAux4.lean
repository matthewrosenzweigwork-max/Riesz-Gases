import HRS.Commutator.Whole.PRODAux3

/-!
# CMX-PROD helper file 4: the Bessel operator on Schwartz kernels, distributional identities
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

noncomputable section

namespace HRS.Commutator.Whole.PROD

open HRS HRS.Whole HRS.Commutator.Whole

variable {d : ℕ}

/-- `⟨∇⟩^α φ` as a Schwartz function. -/
def prod_J (α : ℝ) (φ : SchwartzMap (Euc d) ℂ) : SchwartzMap (Euc d) ℂ := XLI.Fm α φ

lemma prod_besselS_eq (α : ℝ) (φ : SchwartzMap (Euc d) ℂ) : besselS α φ = ⇑(prod_J α φ) := by
  funext x
  exact (XLI.mulS_apply (XLI.bsymX α) (XLI.bsymX_temperate α) φ x).symm

lemma prod_fourier_J (α : ℝ) (φ : SchwartzMap (Euc d) ℂ) (ξ : Euc d) :
    𝓕 (⇑(prod_J α φ)) ξ = (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) : ℝ) : ℂ) * 𝓕 (⇑φ) ξ :=
  XLI.fourier_mulS (XLI.bsymX α) (XLI.bsymX_temperate α) φ ξ

lemma prod_schwartz_ext {A B : SchwartzMap (Euc d) ℂ} (h : ∀ ξ, 𝓕 (⇑A) ξ = 𝓕 (⇑B) ξ) : A = B := by
  have hA : (𝓕 A : SchwartzMap (Euc d) ℂ) = 𝓕 B :=
    SchwartzMap.ext (fun ξ => by simpa [SchwartzMap.fourier_coe] using h ξ)
  calc A = 𝓕⁻ (𝓕 A) := (FourierPair.fourierInv_fourier_eq A).symm
    _ = 𝓕⁻ (𝓕 B) := by rw [hA]
    _ = B := FourierPair.fourierInv_fourier_eq B

/-- The Schwartz convolution. -/
abbrev prod_sconv (K φ : SchwartzMap (Euc d) ℂ) : SchwartzMap (Euc d) ℂ :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) K φ

lemma prod_sconv_apply (K φ : SchwartzMap (Euc d) ℂ) (x : Euc d) :
    prod_sconv K φ x = prod_conv K φ x := conv_kernel_apply K φ x

/-- `J (K ⋆ s) = (J K) ⋆ s`. -/
lemma prod_J_sconv (α : ℝ) (K s : SchwartzMap (Euc d) ℂ) :
    prod_J α (prod_sconv K s) = prod_sconv (prod_J α K) s := by
  refine prod_schwartz_ext fun ξ => ?_
  rw [prod_fourier_J, fourier_conv_kernel, fourier_conv_kernel, prod_fourier_J]
  ring

/-- `K ⋆ J s = (J K) ⋆ s`. -/
lemma prod_sconv_J (α : ℝ) (K s : SchwartzMap (Euc d) ℂ) :
    prod_sconv K (prod_J α s) = prod_sconv (prod_J α K) s := by
  refine prod_schwartz_ext fun ξ => ?_
  rw [fourier_conv_kernel, prod_fourier_J, fourier_conv_kernel, prod_fourier_J]
  ring

/-- If `𝓕 A` is even then `A` is even. -/
lemma prod_even_of_fourier_even {A : SchwartzMap (Euc d) ℂ} (h : ∀ ξ, 𝓕 (⇑A) (-ξ) = 𝓕 (⇑A) ξ)
    (x : Euc d) : A (-x) = A x := by
  have hA : ∀ y, A y = 𝓕⁻ (𝓕 (⇑A)) y := fun y => by
    have := congrArg (fun F : SchwartzMap (Euc d) ℂ => F y)
      (FourierPair.fourierInv_fourier_eq (E := SchwartzMap (Euc d) ℂ)
        (F := SchwartzMap (Euc d) ℂ) A)
    simp only [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe] at this
    exact this.symm
  rw [hA, hA, Real.fourierInv_eq', Real.fourierInv_eq']
  rw [← integral_neg_eq_self (fun v => Complex.exp (↑(2 * Real.pi * inner ℝ v (-x)) * Complex.I) •
    𝓕 (⇑A) v) volume]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [inner_neg_left, inner_neg_right, neg_neg, h v]

lemma prod_fourier_even_of_even {K : Euc d → ℂ} (hK : ∀ t, K (-t) = K t) (ξ : Euc d) :
    𝓕 K (-ξ) = 𝓕 K ξ := by
  rw [Real.fourier_eq', Real.fourier_eq']
  rw [← integral_neg_eq_self (fun v => Complex.exp (↑(-2 * Real.pi * inner ℝ v (-ξ)) * Complex.I) •
    K v) volume]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [inner_neg_left, inner_neg_right, neg_neg, hK v]

lemma prod_J_even (α : ℝ) {K : SchwartzMap (Euc d) ℂ} (hK : ∀ t, K (-t) = K t) (x : Euc d) :
    prod_J α K (-x) = prod_J α K x := by
  refine prod_even_of_fourier_even (fun ξ => ?_) x
  rw [prod_fourier_J, prod_fourier_J, norm_neg, prod_fourier_even_of_even hK]

end HRS.Commutator.Whole.PROD
