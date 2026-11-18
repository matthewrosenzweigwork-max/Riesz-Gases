import HRS.Commutator.Whole.XLIAux7

/-!
# X-LI part 8: multiplier operators on Schwartz functions, Fourier support of products
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- the Fourier multiplier `φ ↦ 𝓕⁻(τ 𝓕φ)` on Schwartz functions -/
def mulS (τ : 𝔼 → ℂ) (hτ : τ.HasTemperateGrowth) (φ : SchwartzMap 𝔼 ℂ) : SchwartzMap 𝔼 ℂ :=
  𝓕⁻ (SchwartzMap.smulLeftCLM ℂ τ (𝓕 φ))

lemma mulS_apply (τ : 𝔼 → ℂ) (hτ : τ.HasTemperateGrowth) (φ : SchwartzMap 𝔼 ℂ) (x : 𝔼) :
    mulS τ hτ φ x = 𝓕⁻ (fun ξ => τ ξ * 𝓕 (⇑φ) ξ) x := by
  unfold mulS
  rw [show ((𝓕⁻ (SchwartzMap.smulLeftCLM ℂ τ (𝓕 φ)) : SchwartzMap 𝔼 ℂ) x) =
      𝓕⁻ (⇑(SchwartzMap.smulLeftCLM ℂ τ (𝓕 φ))) x from by
    rw [← SchwartzMap.fourierInv_coe]]
  have : ⇑(SchwartzMap.smulLeftCLM ℂ τ (𝓕 φ)) = fun ξ => τ ξ * 𝓕 (⇑φ) ξ := by
    funext ξ
    rw [SchwartzMap.smulLeftCLM_apply_apply hτ, smul_eq_mul, SchwartzMap.fourier_coe]
  rw [this]

lemma fourier_mulS (τ : 𝔼 → ℂ) (hτ : τ.HasTemperateGrowth) (φ : SchwartzMap 𝔼 ℂ) (ξ : 𝔼) :
    𝓕 (⇑(mulS τ hτ φ)) ξ = τ ξ * 𝓕 (⇑φ) ξ := by
  have h : (𝓕 (mulS τ hτ φ) : SchwartzMap 𝔼 ℂ) = SchwartzMap.smulLeftCLM ℂ τ (𝓕 φ) :=
    FourierTransform.fourier_fourierInv_eq _
  have := congrArg (fun f : SchwartzMap 𝔼 ℂ => f ξ) h
  simp only [SchwartzMap.fourier_coe, SchwartzMap.smulLeftCLM_apply_apply hτ, smul_eq_mul] at this
  exact this

lemma temperate_symbol {θ : 𝔼 → ℂ} (hθ : ContDiff ℝ ∞ θ) (hcs : HasCompactSupport θ) (j : ℤ) :
    (fun ξ : 𝔼 => θ (((2 : ℝ) ^ j)⁻¹ • ξ)).HasTemperateGrowth :=
  (symbol_cs hcs j).hasTemperateGrowth (symbol_contDiff hθ j)

/-- the convolution with a dyadic kernel is the corresponding Fourier multiplier -/
lemma cv_symK_eq_mulS {θ : 𝔼 → ℂ} (hθ : ContDiff ℝ ∞ θ) (hcs : HasCompactSupport θ)
    (φ : SchwartzMap 𝔼 ℂ) (j : ℤ) :
    cv (symK θ j) φ = ⇑(mulS (fun ξ => θ (((2 : ℝ) ^ j)⁻¹ • ξ)) (temperate_symbol hθ hcs j) φ) := by
  funext x
  rw [mulS_apply]
  set C := cv (symK θ j) φ with hC
  have hCi : Integrable C :=
    Integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) (symK_integrable hθ hcs j)
      φ.integrable
  have hF : 𝓕 C = fun ξ => θ (((2 : ℝ) ^ j)⁻¹ • ξ) * 𝓕 (⇑φ) ξ := by
    funext ξ
    have := Real.fourier_mul_convolution_eq (symK_integrable hθ hcs j) φ.integrable ξ
    rw [hC]
    show 𝓕 (symK θ j ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] ⇑φ) ξ = _
    rw [this, symK_fourier hθ hcs]
  have hFcont : Continuous (𝓕 (⇑φ)) := by
    rw [← SchwartzMap.fourier_coe]; exact (𝓕 φ).continuous
  have hFint : Integrable (𝓕 C) := by
    rw [hF]
    have h2 : Integrable (𝓕 (⇑φ)) := by rw [← SchwartzMap.fourier_coe]; exact (𝓕 φ).integrable
    obtain ⟨Cθ, hCθ⟩ := (symbol_contDiff hθ j).continuous.bounded_above_of_compact_support
      (symbol_cs hcs j)
    have := Integrable.bdd_mul h2 (symbol_contDiff hθ j).continuous.aestronglyMeasurable
      (Eventually.of_forall hCθ)
    simpa using this
  have hcont : Continuous C := by
    refine BddAbove.continuous_convolution_right_of_integrable (ContinuousLinearMap.mul ℂ ℂ) ?_
      (symK_integrable hθ hcs j) φ.continuous
    obtain ⟨B, -, hB⟩ := φ.decay 0 0
    exact ⟨B, by rintro _ ⟨y, rfl⟩; simpa using hB y⟩
  have := Integrable.fourierInv_fourier_eq hCi hFint hcont.continuousAt (v := x)
  rw [hF] at this
  exact this.symm

lemma fourier_mul_eq (u v : SchwartzMap 𝔼 ℂ) (ξ : 𝔼) :
    𝓕 (fun x => u x * v x) ξ = ∫ η, 𝓕 (⇑u) η * 𝓕 (⇑v) (ξ - η) := by
  set U : 𝔼 → ℂ := 𝓕 (⇑u) with hU
  have hUi : Integrable U := by rw [hU, ← SchwartzMap.fourier_coe]; exact (𝓕 u).integrable
  have hu : ∀ x, u x = ∫ η, Complex.exp (↑(2 * Real.pi * inner ℝ η x) * Complex.I) • U η := by
    intro x
    have := congrArg (fun f : 𝔼 → ℂ => f x) (congrArg (⇑) (FourierTransform.fourierInv_fourier_eq
      (E := SchwartzMap 𝔼 ℂ) (F := SchwartzMap 𝔼 ℂ) u))
    simp only [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe] at this
    rw [← this, Real.fourierInv_eq']
  have hvi : Integrable (⇑v) := v.integrable
  -- the integrand on the product
  set Gf : 𝔼 → 𝔼 → ℂ := fun η x => Complex.exp (↑(-2 * Real.pi * inner ℝ x (ξ - η)) * Complex.I) *
    (U η * v x) with hGf
  have hGcont : Continuous (Function.uncurry Gf) := by
    have h1 : Continuous (fun p : 𝔼 × 𝔼 => U p.1) := by
      rw [hU, ← SchwartzMap.fourier_coe]; exact (𝓕 u).continuous.comp continuous_fst
    have h2 : Continuous (fun p : 𝔼 × 𝔼 => v p.2) := v.continuous.comp continuous_snd
    have h3 : Continuous (fun p : 𝔼 × 𝔼 => Complex.exp (↑(-2 * Real.pi * inner ℝ p.2 (ξ - p.1)) * Complex.I)) := by
      refine Complex.continuous_exp.comp ?_
      refine Continuous.mul (Complex.continuous_ofReal.comp ?_) continuous_const
      exact continuous_const.mul (Continuous.inner continuous_snd (continuous_const.sub continuous_fst))
    exact h3.mul (h1.mul h2)
  have hGint : Integrable (Function.uncurry Gf) (volume.prod volume) := by
    have hb : Integrable (fun p : 𝔼 × 𝔼 => ‖U p.1‖ * ‖v p.2‖) (volume.prod volume) :=
      Integrable.mul_prod hUi.norm hvi.norm
    refine hb.mono' hGcont.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, hGf]
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  calc 𝓕 (fun x => u x * v x) ξ
      = ∫ x, ∫ η, Gf η x := by
        rw [Real.fourier_eq']
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [hGf, smul_eq_mul]
        rw [hu x]
        simp only [smul_eq_mul]
        rw [← integral_mul_const, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun η => ?_)
        beta_reduce
        have e : Complex.exp (↑(-2 * Real.pi * inner ℝ x ξ) * Complex.I) *
            Complex.exp (↑(2 * Real.pi * inner ℝ η x) * Complex.I) =
            Complex.exp (↑(-2 * Real.pi * inner ℝ x (ξ - η)) * Complex.I) := by
          rw [← Complex.exp_add]
          congr 1
          rw [inner_sub_right, real_inner_comm η x]
          push_cast
          ring
        rw [← e]
        ring
    _ = ∫ η, ∫ x, Gf η x := by
        refine integral_integral_swap (f := fun x η => Gf η x) ?_
        have := hGint.swap
        exact this
    _ = ∫ η, 𝓕 (⇑u) η * 𝓕 (⇑v) (ξ - η) := by
        refine integral_congr_ae (Eventually.of_forall fun η => ?_)
        simp only [hGf]
        rw [Real.fourier_eq' (⇑v) (ξ - η)]
        simp only [smul_eq_mul]
        rw [← hU, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        ring

/-- the pointwise product of two Schwartz functions -/
def prodS (u v : SchwartzMap 𝔼 ℂ) : SchwartzMap 𝔼 ℂ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (g := ⇑v) v.hasTemperateGrowth u

lemma prodS_apply (u v : SchwartzMap 𝔼 ℂ) (x : 𝔼) : prodS u v x = u x * v x := rfl

/-- Fourier support of products: if no `ξ` in the support of `τ` can be written as `η + (ξ - η)` with
`η ∈ supp 𝓕u`, `ξ - η ∈ supp 𝓕v`, then the multiplier `τ` kills `u v`. -/
lemma mulS_prodS_eq_zero (τ : 𝔼 → ℂ) (hτ : τ.HasTemperateGrowth) (u v : SchwartzMap 𝔼 ℂ)
    (hsupp : ∀ ξ η : 𝔼, τ ξ ≠ 0 → 𝓕 (⇑u) η ≠ 0 → 𝓕 (⇑v) (ξ - η) ≠ 0 → False) (x : 𝔼) :
    mulS τ hτ (prodS u v) x = 0 := by
  rw [mulS_apply]
  have : (fun ξ => τ ξ * 𝓕 (⇑(prodS u v)) ξ) = fun _ => 0 := by
    funext ξ
    by_cases h : τ ξ = 0
    · rw [h, zero_mul]
    · have : 𝓕 (⇑(prodS u v)) ξ = 0 := by
        have e : (⇑(prodS u v)) = fun x => u x * v x := funext fun x => prodS_apply u v x
        rw [e, fourier_mul_eq]
        refine integral_eq_zero_of_ae (Eventually.of_forall fun η => ?_)
        by_contra hne
        exact hsupp ξ η h (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne)
      rw [this, mul_zero]
  rw [this, Real.fourierInv_eq']
  simp

end HRS.Commutator.Whole.XLI
