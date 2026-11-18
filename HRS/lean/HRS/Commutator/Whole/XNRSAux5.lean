import HRS.Commutator.Whole.XNRSAux4
import HRS.PDE.ToolboxRd.Fourier

/-!
# Packet X-NRS, part 5: Fourier representation of the regularised Gagliardo form

For Schwartz `h, ψ` and `δ > 0`:
`∫ N_δ(z) ∫ (h(x)-h(x-z)) ψ(x) dx dz = ∫ m_δ(ξ) 𝓕h(ξ) 𝓕ψ(-ξ) dξ` and the Gagliardo energy
`∫ N_δ(z) ∫ |h(x)-h(x-z)|² dx dz = 2 ∫ m_δ |𝓕h|²`.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

lemma xparseval (g ψ : 𝓢(Euc d, ℂ)) : ∫ x, g x * ψ x = ∫ ξ, 𝓕 g ξ * 𝓕 ψ (-ξ) := by
  have h1 : ∫ x, 𝓕⁻ (𝓕 g) x * ψ x = ∫ x, 𝓕 g x * 𝓕⁻ ψ x :=
    SchwartzMap.integral_fourierInv_mul_eq (𝓕 g) ψ
  rw [FourierTransform.fourierInv_fourier_eq] at h1
  rw [h1]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  have : (𝓕⁻ ψ : 𝓢(Euc d, ℂ)) ξ = 𝓕 ψ (-ξ) := by
    rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe, Real.fourierInv_eq_fourier_neg]
  rw [this]

/-- `x ↦ h x - h (x - z)` as a Schwartz function. -/
def xdiff (z : Euc d) (h : 𝓢(Euc d, ℂ)) : 𝓢(Euc d, ℂ) := h - HRS.PDE.ToolboxRd.FourierAux.translSchwartz z h

lemma xdiff_apply (z : Euc d) (h : 𝓢(Euc d, ℂ)) (x : Euc d) : xdiff z h x = h x - h (x - z) := rfl

lemma fourier_xdiff (z : Euc d) (h : 𝓢(Euc d, ℂ)) (ξ : Euc d) :
    𝓕 (xdiff z h) ξ = (1 - HRS.PDE.ToolboxRd.FourierAux.phase z ξ) * 𝓕 h ξ := by
  have hF : 𝓕 (xdiff z h) = 𝓕 h - 𝓕 (HRS.PDE.ToolboxRd.FourierAux.translSchwartz z h) := by
    have := map_sub (SchwartzMap.fourierTransformCLM ℂ (E := ℂ) (V := Euc d)) h
      (HRS.PDE.ToolboxRd.FourierAux.translSchwartz z h)
    simpa [xdiff] using this
  rw [hF, SchwartzMap.sub_apply, HRS.PDE.ToolboxRd.FourierAux.fourier_translSchwartz]
  ring

lemma norm_one_sub_phase_sq' (z ξ : Euc d) :
    ‖1 - HRS.PDE.ToolboxRd.FourierAux.phase z ξ‖ ^ 2 = 2 * xph ξ z := by
  unfold HRS.PDE.ToolboxRd.FourierAux.phase xph
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hc : Real.cos (-2 * Real.pi * inner ℝ z ξ) = Real.cos (2 * Real.pi * inner ℝ z ξ) := by
    rw [show -2 * Real.pi * inner ℝ z ξ = -(2 * Real.pi * inner ℝ z ξ) by ring, Real.cos_neg]
  rw [hc]
  nlinarith [Real.sin_sq_add_cos_sq (-2 * Real.pi * inner ℝ z ξ), Real.sin_sq_add_cos_sq (2 * Real.pi * inner ℝ z ξ),
    Real.sin_sq_add_cos_sq (-2 * Real.pi * inner ℝ z ξ), hc]

lemma xdiff_plancherel (z : Euc d) (h : 𝓢(Euc d, ℂ)) :
    ∫ x, ‖h x - h (x - z)‖ ^ 2 = ∫ ξ, 2 * xph ξ z * ‖𝓕 h ξ‖ ^ 2 := by
  have h1 := SchwartzMap.integral_norm_sq_fourier (xdiff z h)
  have h2 : ∀ ξ, ‖𝓕 (xdiff z h) ξ‖ ^ 2 = 2 * xph ξ z * ‖𝓕 h ξ‖ ^ 2 := by
    intro ξ
    rw [fourier_xdiff, norm_mul, mul_pow, norm_one_sub_phase_sq']
  simp only [xdiff_apply] at h1
  rw [← h1]
  exact integral_congr_ae (Eventually.of_forall h2)


lemma continuous_phase_prod : Continuous (fun p : Euc d × Euc d =>
    HRS.PDE.ToolboxRd.FourierAux.phase p.1 p.2) := by
  unfold HRS.PDE.ToolboxRd.FourierAux.phase; fun_prop

lemma xint_phase {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (ξ : Euc d) :
    ∫ z, ((xN d σ δ z : ℝ) : ℂ) * (1 - HRS.PDE.ToolboxRd.FourierAux.phase z ξ) =
      ((xm d σ δ ξ : ℝ) : ℂ) := by
  have hsplit : ∀ z : Euc d, ((xN d σ δ z : ℝ) : ℂ) * (1 - HRS.PDE.ToolboxRd.FourierAux.phase z ξ) =
      ((xN d σ δ z * xph ξ z : ℝ) : ℂ) +
        Complex.I * ((xN d σ δ z * Real.sin (2 * Real.pi * inner ℝ z ξ) : ℝ) : ℂ) := by
    intro z
    unfold HRS.PDE.ToolboxRd.FourierAux.phase xph
    rw [Complex.exp_mul_I]
    have hc : Real.cos (-2 * Real.pi * inner ℝ z ξ) = Real.cos (2 * Real.pi * inner ℝ z ξ) := by
      rw [show -2 * Real.pi * inner ℝ z ξ = -(2 * Real.pi * inner ℝ z ξ) by ring, Real.cos_neg]
    have hs : Real.sin (-2 * Real.pi * inner ℝ z ξ) = -Real.sin (2 * Real.pi * inner ℝ z ξ) := by
      rw [show -2 * Real.pi * inner ℝ z ξ = -(2 * Real.pi * inner ℝ z ξ) by ring, Real.sin_neg]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hs]
    push_cast
    ring
  simp_rw [hsplit]
  have hi1 : Integrable (fun z : Euc d => ((xN d σ δ z * xph ξ z : ℝ) : ℂ)) :=
    (integrable_xm_integrand hσ hδ ξ).ofReal
  have hi2 : Integrable (fun z : Euc d => Complex.I *
      ((xN d σ δ z * Real.sin (2 * Real.pi * inner ℝ z ξ) : ℝ) : ℂ)) := by
    refine Integrable.const_mul ?_ _
    refine Integrable.ofReal ?_
    refine (integrable_xN hσ hδ).mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact ((continuous_xN σ δ hδ).mul (by fun_prop)).aestronglyMeasurable
    · show ‖xN d σ δ z * Real.sin (2 * Real.pi * inner ℝ z ξ)‖ ≤ xN d σ δ z
      rw [norm_mul, Real.norm_of_nonneg (xN_pos hδ z).le, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (xN_pos hδ z).le (Real.abs_sin_le_one _)
  rw [integral_add hi1 hi2, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]
  have hz : ∫ z : Euc d, xN d σ δ z * Real.sin (2 * Real.pi * inner ℝ z ξ) = 0 := by
    have h := integral_neg_eq_self (fun z : Euc d => xN d σ δ z * Real.sin (2 * Real.pi * inner ℝ z ξ))
      volume
    simp only [xN_neg, inner_neg_left, mul_neg, Real.sin_neg, integral_neg] at h
    linarith
  rw [hz]
  simp [xm]


lemma xfourierInv_apply (ψ : 𝓢(Euc d, ℂ)) (ξ : Euc d) : (𝓕⁻ ψ : 𝓢(Euc d, ℂ)) ξ = 𝓕 ψ (-ξ) := by
  rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe, Real.fourierInv_eq_fourier_neg]

lemma xFpair_int (h ψ : 𝓢(Euc d, ℂ)) :
    Integrable (fun ξ : Euc d => 𝓕 h ξ * 𝓕 ψ (-ξ)) := by
  have := xint_mul (𝓕 h : 𝓢(Euc d, ℂ)) (𝓕⁻ ψ : 𝓢(Euc d, ℂ))
  simpa only [xfourierInv_apply] using this

theorem xJ_fourier {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (h ψ : 𝓢(Euc d, ℂ)) :
    ∫ z, ((xN d σ δ z : ℝ) : ℂ) * (∫ x, (h x - h (x - z)) * ψ x) =
      ∫ ξ, ((xm d σ δ ξ : ℝ) : ℂ) * 𝓕 h ξ * 𝓕 ψ (-ξ) := by
  have step1 : ∀ z : Euc d, ∫ x, (h x - h (x - z)) * ψ x =
      ∫ ξ, (1 - HRS.PDE.ToolboxRd.FourierAux.phase z ξ) * 𝓕 h ξ * 𝓕 ψ (-ξ) := by
    intro z
    have := xparseval (xdiff z h) ψ
    simp only [xdiff_apply] at this
    rw [this]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [fourier_xdiff, mul_assoc]
  simp_rw [step1]
  simp_rw [← integral_const_mul]
  have hint : Integrable (Function.uncurry fun (z ξ : Euc d) =>
      ((xN d σ δ z : ℝ) : ℂ) * ((1 - HRS.PDE.ToolboxRd.FourierAux.phase z ξ) * 𝓕 h ξ * 𝓕 ψ (-ξ)))
      (volume.prod volume) := by
    have hg : Integrable (fun p : Euc d × Euc d => xN d σ δ p.1 * (2 * ‖𝓕 h p.2 * 𝓕 ψ (-p.2)‖))
        (volume.prod volume) :=
      Integrable.mul_prod (f := xN d σ δ) (g := fun ξ : Euc d => 2 * ‖𝓕 h ξ * 𝓕 ψ (-ξ)‖)
        (integrable_xN hσ hδ) ((xFpair_int h ψ).norm.const_mul 2)
    refine hg.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hc : Continuous (fun p : Euc d × Euc d =>
          ((xN d σ δ p.1 : ℝ) : ℂ) * ((1 - HRS.PDE.ToolboxRd.FourierAux.phase p.1 p.2) *
            𝓕 h p.2 * 𝓕 ψ (-p.2))) := by
        refine (Complex.continuous_ofReal.comp ((continuous_xN σ δ hδ).comp continuous_fst)).mul ?_
        refine ((continuous_const.sub continuous_phase_prod).mul
          ((𝓕 h : 𝓢(Euc d, ℂ)).continuous.comp continuous_snd)).mul
          ((𝓕 ψ : 𝓢(Euc d, ℂ)).continuous.comp (continuous_neg.comp continuous_snd))
      exact hc.aestronglyMeasurable
    · show ‖((xN d σ δ p.1 : ℝ) : ℂ) * ((1 - HRS.PDE.ToolboxRd.FourierAux.phase p.1 p.2) *
          𝓕 h p.2 * 𝓕 ψ (-p.2))‖ ≤ xN d σ δ p.1 * (2 * ‖𝓕 h p.2 * 𝓕 ψ (-p.2)‖)
      have hn1 : ‖((xN d σ δ p.1 : ℝ) : ℂ) * ((1 - HRS.PDE.ToolboxRd.FourierAux.phase p.1 p.2) *
          𝓕 h p.2 * 𝓕 ψ (-p.2))‖ = xN d σ δ p.1 * (‖1 - HRS.PDE.ToolboxRd.FourierAux.phase p.1 p.2‖ *
          ‖𝓕 h p.2‖ * ‖𝓕 ψ (-p.2)‖) := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (xN_pos hδ p.1).le, norm_mul, norm_mul]
      rw [hn1, norm_mul (𝓕 h p.2)]
      have h1 : ‖1 - HRS.PDE.ToolboxRd.FourierAux.phase p.1 p.2‖ ≤ 2 := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_one, HRS.PDE.ToolboxRd.FourierAux.norm_phase]; norm_num
      apply mul_le_mul_of_nonneg_left _ (xN_pos hδ p.1).le
      have := mul_nonneg (norm_nonneg (𝓕 h p.2)) (norm_nonneg (𝓕 ψ (-p.2)))
      nlinarith [norm_nonneg (𝓕 h p.2), norm_nonneg (𝓕 ψ (-p.2))]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  have : ∀ z : Euc d, ((xN d σ δ z : ℝ) : ℂ) *
      ((1 - HRS.PDE.ToolboxRd.FourierAux.phase z ξ) * 𝓕 h ξ * 𝓕 ψ (-ξ)) =
      (((xN d σ δ z : ℝ) : ℂ) * (1 - HRS.PDE.ToolboxRd.FourierAux.phase z ξ)) * (𝓕 h ξ * 𝓕 ψ (-ξ)) := by
    intro z; ring
  simp_rw [this]
  rw [integral_mul_const, xint_phase hσ hδ ξ]
  ring


lemma integrable_fourier_norm_sq (h : 𝓢(Euc d, ℂ)) : Integrable (fun ξ : Euc d => ‖𝓕 h ξ‖ ^ 2) := by
  have := integrable_xhom (d := d) (β := 0) le_rfl h
  simpa using this

theorem xenergy {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (h : 𝓢(Euc d, ℂ)) :
    ∫ z, xN d σ δ z * (∫ x, ‖h x - h (x - z)‖ ^ 2) = ∫ ξ, 2 * xm d σ δ ξ * ‖𝓕 h ξ‖ ^ 2 := by
  simp_rw [xdiff_plancherel, ← integral_const_mul]
  have hint : Integrable (Function.uncurry fun (z ξ : Euc d) =>
      xN d σ δ z * (2 * xph ξ z * ‖𝓕 h ξ‖ ^ 2)) (volume.prod volume) := by
    have hg : Integrable (fun p : Euc d × Euc d => xN d σ δ p.1 * (4 * ‖𝓕 h p.2‖ ^ 2))
        (volume.prod volume) :=
      Integrable.mul_prod (f := xN d σ δ) (g := fun ξ : Euc d => 4 * ‖𝓕 h ξ‖ ^ 2)
        (integrable_xN hσ hδ) ((integrable_fourier_norm_sq h).const_mul 4)
    refine hg.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hc : Continuous (fun p : Euc d × Euc d =>
          xN d σ δ p.1 * (2 * xph p.2 p.1 * ‖𝓕 h p.2‖ ^ 2)) := by
        refine ((continuous_xN σ δ hδ).comp continuous_fst).mul ?_
        have : Continuous (fun p : Euc d × Euc d => xph p.2 p.1) := by
          unfold xph; fun_prop
        exact (continuous_const.mul this).mul
          (((𝓕 h : 𝓢(Euc d, ℂ)).continuous.comp continuous_snd).norm.pow 2)
      exact hc.aestronglyMeasurable
    · show ‖xN d σ δ p.1 * (2 * xph p.2 p.1 * ‖𝓕 h p.2‖ ^ 2)‖ ≤ xN d σ δ p.1 * (4 * ‖𝓕 h p.2‖ ^ 2)
      have h0 : 0 < xN d σ δ p.1 := xN_pos hδ p.1
      have h1 := xph_nonneg p.2 p.1
      have h2 := xph_le_two p.2 p.1
      rw [Real.norm_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_left _ h0.le
      nlinarith [sq_nonneg ‖𝓕 h p.2‖]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  have : ∀ z : Euc d, xN d σ δ z * (2 * xph ξ z * ‖𝓕 h ξ‖ ^ 2) =
      (xN d σ δ z * xph ξ z) * (2 * ‖𝓕 h ξ‖ ^ 2) := by intro z; ring
  simp_rw [this]
  rw [integral_mul_const]
  unfold xm
  ring

end HRS.Commutator.Whole.XNRS
