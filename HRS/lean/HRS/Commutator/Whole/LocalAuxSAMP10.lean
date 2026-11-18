import HRS.Commutator.Whole.LocalAuxSAMP9
import HRS.Commutator.Whole.LocalAuxSAMP4

/-!
# The test function `S = K * θ` and `|∇|^α S = θ - ψ * θ` (packet CMX-SAMP, helper file 10)
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff Convolution

noncomputable section

namespace HRS.Commutator.Whole.SAMP1

open HRS HRS.Whole HRS.Commutator.Whole

variable {d : ℕ}

lemma conv_psi_eq (θ : SchwartzMap (Euc d) ℂ) (x : Euc d) :
    ∫ t, (Om d t) * θ (x - t) = 𝓕⁻ (fun ξ : Euc d => ((chi ξ : ℝ) : ℂ) * 𝓕 (⇑θ) ξ) x := by
  have h1 := conv_kernel_apply (Om d) θ x
  have h2 : 𝓕 (⇑(SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (Om d) θ)) =
      fun ξ => ((chi ξ : ℝ) : ℂ) * 𝓕 (⇑θ) ξ := by
    funext ξ
    rw [fourier_conv_kernel]
    have hO : 𝓕 (⇑(Om d)) = ⇑(cmxFB_G (d := d) 1 one_pos) := by
      rw [← SchwartzMap.fourier_coe]
      exact congrArg (⇑) (cmxFB_fourier_Om (d := d) one_pos)
    rw [hO]
    simp [cmxFB_G_apply, cmxFB_gL]
  have h3 : (𝓕⁻ (𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (Om d) θ) :
      SchwartzMap (Euc d) ℂ) : SchwartzMap (Euc d) ℂ) =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (Om d) θ :=
    FourierTransform.fourierInv_fourier_eq _
  have h4 := congrArg (fun F : SchwartzMap (Euc d) ℂ => F x) h3
  simp only [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe, h2] at h4
  rw [← h1, ← h4]

lemma integrable_inv_phase {g : Euc d → ℂ} (hg : Integrable g) (x : Euc d) :
    Integrable (fun ξ : Euc d => Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) • g ξ) := by
  refine hg.norm.mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · have hc : Continuous fun ξ : Euc d =>
        Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) := by fun_prop
    exact hc.aestronglyMeasurable.smul hg.1
  · rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

lemma sym_ident {α : ℝ} (ξ : Euc d) (z : ℂ) :
    (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) *
      ((((1 - chi ξ) * (2 * Real.pi * ‖ξ‖) ^ (-α) : ℝ)) : ℂ) * z =
      (((1 - chi ξ : ℝ)) : ℂ) * z := by
  by_cases hξ : ξ = 0
  · subst hξ
    have : chi (0 : Euc d) = 1 := cmxFB_chi_one (by simp)
    simp [this]
  · have hn : 0 < 2 * Real.pi * ‖ξ‖ := by
      have : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
      positivity
    have h1 : (2 * Real.pi * ‖ξ‖) ^ α * (2 * Real.pi * ‖ξ‖) ^ (-α) = 1 := by
      rw [← Real.rpow_add hn]; simp
    have h2 : (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) *
        ((((1 - chi ξ) * (2 * Real.pi * ‖ξ‖) ^ (-α) : ℝ)) : ℂ) = (((1 - chi ξ : ℝ)) : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      calc (2 * Real.pi * ‖ξ‖) ^ α * ((1 - chi ξ) * (2 * Real.pi * ‖ξ‖) ^ (-α))
          = (1 - chi ξ) * ((2 * Real.pi * ‖ξ‖) ^ α * (2 * Real.pi * ‖ξ‖) ^ (-α)) := by ring
        _ = 1 - chi ξ := by rw [h1, mul_one]
    rw [h2]

theorem exists_test_S {α : ℝ} {K : Euc d → ℝ} (hK : Integrable K)
    (hKF : ∀ ξ : Euc d, 𝓕 (fun x : Euc d => ((K x : ℝ) : ℂ)) ξ =
      (((1 - chi ξ) * (2 * Real.pi * ‖ξ‖) ^ (-α) : ℝ) : ℂ))
    (θ : SchwartzMap (Euc d) ℂ) :
    ∃ S : SchwartzMap (Euc d) ℂ, (∀ x, S x = ∫ y, ((K y : ℝ) : ℂ) * θ (x - y)) ∧
      ∀ x, Tfrac α S x = θ x - ∫ y, (Om d y) * θ (x - y) := by
  have hFθ : (⇑(𝓕 θ : SchwartzMap (Euc d) ℂ) : Euc d → ℂ) = 𝓕 ⇑θ := SchwartzMap.fourier_coe θ
  obtain ⟨S₁, hS₁⟩ := schwartz_riesz_cut (chiBump d) rfl α (𝓕 θ : SchwartzMap (Euc d) ℂ)
  have hS₁' : ∀ ξ, S₁ ξ = (((1 - chi ξ) * (2 * Real.pi * ‖ξ‖) ^ (-α) : ℝ) : ℂ) * 𝓕 ⇑θ ξ := by
    intro ξ; rw [hS₁ ξ, hFθ]; rfl
  set S : SchwartzMap (Euc d) ℂ := 𝓕⁻ S₁ with hS
  have hFS : 𝓕 ⇑S = ⇑S₁ := by
    rw [← SchwartzMap.fourier_coe]
    exact congrArg (⇑) (FourierInvPair.fourier_fourierInv_eq (E := SchwartzMap (Euc d) ℂ)
      (F := SchwartzMap (Euc d) ℂ) S₁)
  have hSx : ∀ x, S x = 𝓕⁻ ⇑S₁ x := fun x => by rw [hS, SchwartzMap.fourierInv_coe]
  refine ⟨S, fun x => ?_, fun x => ?_⟩
  · -- `S = K * θ`
    set Kc : Euc d → ℂ := fun x => ((K x : ℝ) : ℂ) with hKc
    have hKci : Integrable Kc := hK.ofReal
    have hconvi : Integrable (Kc ⋆[ContinuousLinearMap.mul ℂ ℂ] ⇑θ) :=
      hKci.integrable_convolution _ θ.integrable
    have hbdd : BddAbove (Set.range fun x => ‖θ x‖) := by
      refine ⟨‖θ.toBoundedContinuousFunction‖, ?_⟩
      rintro _ ⟨y, rfl⟩
      exact θ.toBoundedContinuousFunction.norm_coe_le_norm y
    have hcont : Continuous (Kc ⋆[ContinuousLinearMap.mul ℂ ℂ] ⇑θ) :=
      hbdd.continuous_convolution_right_of_integrable _ hKci θ.continuous
    have hF : 𝓕 (Kc ⋆[ContinuousLinearMap.mul ℂ ℂ] ⇑θ) = ⇑S₁ := by
      funext ξ
      rw [Real.fourier_mul_convolution_eq hKci θ.integrable, hS₁' ξ, hKF ξ]
    have hSi : Integrable (𝓕 (Kc ⋆[ContinuousLinearMap.mul ℂ ℂ] ⇑θ)) := by
      rw [hF]; exact S₁.integrable
    have := hconvi.fourierInv_fourier_eq hSi (v := x) hcont.continuousAt
    rw [hF] at this
    rw [hSx x, this, convolution_def]
    rfl
  · -- `|∇|^α S = θ - ψ * θ`
    unfold Tfrac
    simp_rw [hFS]
    have e1 : ∀ ξ : Euc d, (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * S₁ ξ =
        (((1 - chi ξ : ℝ)) : ℂ) * 𝓕 ⇑θ ξ := by
      intro ξ; rw [hS₁' ξ, ← mul_assoc]; exact sym_ident ξ _
    simp_rw [e1]
    have hΦ : Integrable (𝓕 ⇑θ) := by
      have := (𝓕 θ : SchwartzMap (Euc d) ℂ).integrable (μ := (volume : Measure (Euc d)))
      rwa [hFθ] at this
    have hχΦ : Integrable (fun ξ : Euc d => ((chi ξ : ℝ) : ℂ) * 𝓕 ⇑θ ξ) := by
      refine hΦ.norm.mono' ?_ (Eventually.of_forall fun ξ => ?_)
      · refine AEStronglyMeasurable.mul ?_ hΦ.1
        exact (Complex.continuous_ofReal.comp
          (cmxFB_chi_contDiff.continuous)).aestronglyMeasurable
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (cmxFB_chi_nonneg ξ)]
        exact mul_le_of_le_one_left (norm_nonneg _) (cmxFB_chi_le_one ξ)
    have e2 : 𝓕⁻ (fun ξ : Euc d => (((1 - chi ξ : ℝ)) : ℂ) * 𝓕 ⇑θ ξ) x =
        𝓕⁻ (𝓕 ⇑θ) x - 𝓕⁻ (fun ξ : Euc d => ((chi ξ : ℝ) : ℂ) * 𝓕 ⇑θ ξ) x := by
      rw [Real.fourierInv_eq', Real.fourierInv_eq', Real.fourierInv_eq',
        ← integral_sub (integrable_inv_phase hΦ x) (integrable_inv_phase hχΦ x)]
      refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
      simp only [smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    have e3 : 𝓕⁻ (𝓕 ⇑θ) x = θ x := by
      have h : (𝓕⁻ (𝓕 θ : SchwartzMap (Euc d) ℂ) : SchwartzMap (Euc d) ℂ) = θ :=
        FourierTransform.fourierInv_fourier_eq θ
      have h2 := congrArg (fun F : SchwartzMap (Euc d) ℂ => F x) h
      simpa only [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe] using h2
    rw [e2, e3, ← conv_psi_eq]

end HRS.Commutator.Whole.SAMP1
