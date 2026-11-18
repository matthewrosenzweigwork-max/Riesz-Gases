import HRS.MS.R2PolyTie
import HRS.PDE.ToolboxRd.Fourier

/-!
# HRS.MS.R2WfmAux1 -- `round2_weighted_field_moments` (S9.7), part 1: Fourier synthesis

Packet S97, namespace `HRS.MS.R2Wfm`, helper prefix `s97_`.  PLAN (see also the other `R2Wfm*` files).

Statement S9.7 (`HRS.Whole.round2_weighted_field_moments`) is TRUE and non-vacuous as frozen (audit: no junk-value trap;
`∫⁻` is monotone so the supremum defining `r2NegSobNorm` is majorised pathwise by a measurable function; the centred
clause uses `‖∫ f‖ₑ ≤ ∫⁻ ‖f‖ₑ`, valid also for the junk value `0`; `pairEnergy` is linear in the kernel for every
configuration because commutator kernels vanish on the diagonal; the quench clause uses `s92_quench_density`).

Route (simpler than the TeX: no Hermite basis, no Gaussian series, no Sobolev embedding).  Fourier *frame* instead of an ONB.
For a real Schwartz `ψ`, `A + iB = 𝓕ψ` and
`ψ(x) = ∫ (A cos(2π⟨x,ξ⟩) - B sin(2π⟨x,ξ⟩)) dξ`, `dψ(x)g = ∫ -2π⟨g,ξ⟩ (A sin + B cos) dξ`,
`∫ wt^m (A²+B²) = ‖ψ‖²_{H^m}` with `wt = 1 + 4π²|ξ|²`.  Pathwise, for a functional `T` built from evaluations of `φ`, `∇φ` at the
particles and `μ`-integrals, `T(⟨x⟩^P ψ) = ∫ (A u - B v)`, `u(ξ) = T(⟨x⟩^P cos_ξ)`, `v(ξ) = T(⟨x⟩^P sin_ξ)`; Cauchy–Schwarz gives
`‖T‖²_{-m,P} ≤ ∫ wt^{-m}(u²+v²)`; Hölder in `ξ` with weight `wt^{-γ}` and Tonelli reduce `E‖T‖^r` to `E|u(ξ)|^r`, controlled by
S9.5 (`round2_polynomial_moments_proof`) with `B(ξ) ≲ wt(ξ)`.  Needs `m ≥ d/2 + 5/2` (true: `m > k + d/2 > d + 2`).

Files: Aux1 (this: synthesis of `ψ`), Aux2 (weights, plane waves, polynomial envelope of the commutator kernel), Aux3
(pathwise synthesis of the two functionals), Aux4 (abstract frame lemma, centring), Aux5 (core theorem), Tie.
-/

open MeasureTheory
open scoped FourierTransform ComplexConjugate

noncomputable section
namespace HRS.MS.R2Wfm
open HRS.Whole
open HRS.PDE.ToolboxRd.FourierAux (wt wt_pos one_le_wt fourierL2_schwartz)

variable {d : ℕ}

/-- complexified Schwartz function -/
def s97_cpl (ψ : SchwartzMap (Euc d) ℝ) : SchwartzMap (Euc d) ℂ :=
  ψ.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM

theorem s97_cpl_apply (ψ : SchwartzMap (Euc d) ℝ) (x : Euc d) : s97_cpl ψ x = (ψ x : ℂ) := rfl

/-- Fourier inversion for real Schwartz functions: real form. -/
theorem s97_inv (ψ : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    ψ x = ∫ ξ, ((𝓕 (⇑(s97_cpl ψ)) ξ).re * Real.cos (2 * Real.pi * inner ℝ x ξ) -
      (𝓕 (⇑(s97_cpl ψ)) ξ).im * Real.sin (2 * Real.pi * inner ℝ x ξ)) := by
  have h := (s97_cpl ψ).continuous.fourierInv_fourier_eq (s97_cpl ψ).integrable
    (𝓕 (s97_cpl ψ)).integrable
  have h2 := congrFun h x
  rw [Real.fourierInv_eq'] at h2
  set F := 𝓕 (⇑(s97_cpl ψ)) with hF
  have hFc : Continuous F := (𝓕 (s97_cpl ψ)).continuous
  have hFi : Integrable F := (𝓕 (s97_cpl ψ)).integrable
  have hi : Integrable (fun v : Euc d => Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) • F v) := by
    refine hFi.norm.mono' (by fun_prop) (Filter.Eventually.of_forall fun v => ?_)
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have h3 := congrArg Complex.re h2
  have h4 := integral_re hi
  simp only [RCLike.re_to_complex] at h4
  rw [← h4] at h3
  rw [s97_cpl_apply, Complex.ofReal_re] at h3
  rw [← h3]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, real_inner_comm x v]
  ring


/-- cosine coefficient -/
def s97_A (ψ : SchwartzMap (Euc d) ℝ) (ξ : Euc d) : ℝ := (𝓕 (⇑(s97_cpl ψ)) ξ).re
/-- sine coefficient -/
def s97_B (ψ : SchwartzMap (Euc d) ℝ) (ξ : Euc d) : ℝ := (𝓕 (⇑(s97_cpl ψ)) ξ).im

theorem s97_inv' (ψ : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    ψ x = ∫ ξ, (s97_A ψ ξ * Real.cos (2 * Real.pi * inner ℝ x ξ) -
      s97_B ψ ξ * Real.sin (2 * Real.pi * inner ℝ x ξ)) := s97_inv ψ x

theorem s97_A_abs_le (ψ : SchwartzMap (Euc d) ℝ) (ξ : Euc d) : |s97_A ψ ξ| ≤ ‖𝓕 (⇑(s97_cpl ψ)) ξ‖ :=
  Complex.abs_re_le_norm _
theorem s97_B_abs_le (ψ : SchwartzMap (Euc d) ℝ) (ξ : Euc d) : |s97_B ψ ξ| ≤ ‖𝓕 (⇑(s97_cpl ψ)) ξ‖ :=
  Complex.abs_im_le_norm _

theorem s97_A_cont (ψ : SchwartzMap (Euc d) ℝ) : Continuous (s97_A ψ) :=
  Complex.continuous_re.comp (𝓕 (s97_cpl ψ)).continuous
theorem s97_B_cont (ψ : SchwartzMap (Euc d) ℝ) : Continuous (s97_B ψ) :=
  Complex.continuous_im.comp (𝓕 (s97_cpl ψ)).continuous

theorem s97_fderiv (ψ : SchwartzMap (Euc d) ℝ) (x g : Euc d) :
    fderiv ℝ ψ x g = ∫ ξ, (-(2 * Real.pi * inner ℝ g ξ)) *
      (s97_A ψ ξ * Real.sin (2 * Real.pi * inner ℝ x ξ) + s97_B ψ ξ * Real.cos (2 * Real.pi * inner ℝ x ξ)) := by
  let F : Euc d → Euc d → ℝ := fun y ξ => s97_A ψ ξ * Real.cos (2 * Real.pi * inner ℝ y ξ) -
      s97_B ψ ξ * Real.sin (2 * Real.pi * inner ℝ y ξ)
  let F' : Euc d → Euc d → Euc d →L[ℝ] ℝ := fun y ξ =>
    (-(2 * Real.pi) * (s97_A ψ ξ * Real.sin (2 * Real.pi * inner ℝ y ξ) +
      s97_B ψ ξ * Real.cos (2 * Real.pi * inner ℝ y ξ))) • innerSL ℝ ξ
  have hFi : Integrable (fun ξ : Euc d => ‖ξ‖ ^ 1 * ‖𝓕 (⇑(s97_cpl ψ)) ξ‖) :=
    (𝓕 (s97_cpl ψ)).integrable_pow_mul volume 1
  have hF0 : Integrable (fun ξ : Euc d => ‖𝓕 (⇑(s97_cpl ψ)) ξ‖) := (𝓕 (s97_cpl ψ)).integrable.norm
  have hAc := s97_A_cont ψ
  have hBc := s97_B_cont ψ
  have hFd : ∀ ξ, ∀ y : Euc d, HasFDerivAt (fun y => F y ξ) (F' y ξ) y := by
    intro ξ y
    have h1 : HasFDerivAt (fun y : Euc d => 2 * Real.pi * inner ℝ y ξ) (((2 * Real.pi : ℝ)) • innerSL ℝ ξ) y := by
      have : (fun y : Euc d => 2 * Real.pi * inner ℝ y ξ) = fun y => ((2 * Real.pi : ℝ)) • innerSL ℝ ξ y := by
        funext y; simp [real_inner_comm]
      rw [this]
      exact ((innerSL ℝ ξ).hasFDerivAt).const_smul ((2 * Real.pi : ℝ))
    have h2 := (h1.cos.const_mul (s97_A ψ ξ)).sub (h1.sin.const_mul (s97_B ψ ξ))
    convert h2 using 1
    ext v
    simp only [F', innerSL_apply_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    ring
  have hbd : ∀ y ξ, ‖F' y ξ‖ ≤ 4 * Real.pi * (‖ξ‖ ^ 1 * ‖𝓕 (⇑(s97_cpl ψ)) ξ‖) := by
    intro y ξ
    have h1 := s97_A_abs_le ψ ξ
    have h2 := s97_B_abs_le ψ ξ
    have h3 := Real.abs_cos_le_one (2 * Real.pi * inner ℝ y ξ)
    have h4 := Real.abs_sin_le_one (2 * Real.pi * inner ℝ y ξ)
    simp only [F', norm_smul, innerSL_apply_norm, Real.norm_eq_abs]
    have hc : |-(2 * Real.pi) * (s97_A ψ ξ * Real.sin (2 * Real.pi * inner ℝ y ξ) +
        s97_B ψ ξ * Real.cos (2 * Real.pi * inner ℝ y ξ))| ≤ 4 * Real.pi * ‖𝓕 (⇑(s97_cpl ψ)) ξ‖ := by
      rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
      have : |s97_A ψ ξ * Real.sin (2 * Real.pi * inner ℝ y ξ) + s97_B ψ ξ * Real.cos (2 * Real.pi * inner ℝ y ξ)| ≤
          2 * ‖𝓕 (⇑(s97_cpl ψ)) ξ‖ := by
        calc _ ≤ |s97_A ψ ξ * Real.sin (2 * Real.pi * inner ℝ y ξ)| + |s97_B ψ ξ * Real.cos (2 * Real.pi * inner ℝ y ξ)| :=
              abs_add_le _ _
          _ = |s97_A ψ ξ| * |Real.sin (2 * Real.pi * inner ℝ y ξ)| + |s97_B ψ ξ| * |Real.cos (2 * Real.pi * inner ℝ y ξ)| := by
              rw [abs_mul, abs_mul]
          _ ≤ |s97_A ψ ξ| + |s97_B ψ ξ| := by
              have := abs_nonneg (s97_A ψ ξ); have := abs_nonneg (s97_B ψ ξ)
              nlinarith
          _ ≤ 2 * ‖𝓕 (⇑(s97_cpl ψ)) ξ‖ := by linarith
      nlinarith [Real.pi_pos]
    calc _ ≤ 4 * Real.pi * ‖𝓕 (⇑(s97_cpl ψ)) ξ‖ * ‖ξ‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ = _ := by ring
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := (volume : Measure (Euc d)))
    (F := F) (F' := F') (x₀ := x) (bound := fun ξ => 4 * Real.pi * (‖ξ‖ ^ 1 * ‖𝓕 (⇑(s97_cpl ψ)) ξ‖))
    (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun y => by
      refine Continuous.aestronglyMeasurable ?_
      fun_prop)
    (by
      refine (hF0.const_mul 2).mono' (Continuous.aestronglyMeasurable (by fun_prop)) (Filter.Eventually.of_forall fun ξ => ?_)
      have h1 := s97_A_abs_le ψ ξ
      have h2 := s97_B_abs_le ψ ξ
      have h3 := Real.abs_cos_le_one (2 * Real.pi * inner ℝ x ξ)
      have h4 := Real.abs_sin_le_one (2 * Real.pi * inner ℝ x ξ)
      rw [Real.norm_eq_abs]
      calc |F x ξ| ≤ |s97_A ψ ξ * Real.cos (2 * Real.pi * inner ℝ x ξ)| + |s97_B ψ ξ * Real.sin (2 * Real.pi * inner ℝ x ξ)| :=
            abs_sub _ _
        _ = |s97_A ψ ξ| * |Real.cos (2 * Real.pi * inner ℝ x ξ)| + |s97_B ψ ξ| * |Real.sin (2 * Real.pi * inner ℝ x ξ)| := by
            rw [abs_mul, abs_mul]
        _ ≤ |s97_A ψ ξ| + |s97_B ψ ξ| := by
            have := abs_nonneg (s97_A ψ ξ); have := abs_nonneg (s97_B ψ ξ)
            nlinarith
        _ ≤ 2 * ‖𝓕 (⇑(s97_cpl ψ)) ξ‖ := by linarith)
    (by
      refine Continuous.aestronglyMeasurable ?_
      fun_prop)
    (Filter.Eventually.of_forall fun ξ y _ => hbd y ξ)
    (hFi.const_mul _)
    (Filter.Eventually.of_forall fun ξ y _ => hFd ξ y)
  have hψ : (⇑ψ) = fun y => ∫ ξ, F y ξ := by
    funext y; exact s97_inv' ψ y
  have hder : fderiv ℝ ψ x = ∫ ξ, F' x ξ := by
    rw [hψ]; exact hmain.fderiv
  have hint : Integrable (F' x) := by
    refine (hFi.const_mul (4 * Real.pi)).mono' (Continuous.aestronglyMeasurable ?_) (Filter.Eventually.of_forall fun ξ => ?_)
    · have hc : Continuous fun ξ : Euc d => (-(2 * Real.pi) * (s97_A ψ ξ * Real.sin (2 * Real.pi * inner ℝ x ξ) +
          s97_B ψ ξ * Real.cos (2 * Real.pi * inner ℝ x ξ))) := by fun_prop
      exact Continuous.smul hc (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).continuous
    · exact hbd x ξ
  rw [hder, ContinuousLinearMap.integral_apply hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [F', innerSL_apply_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [real_inner_comm g ξ]
  ring


theorem s97_AB_int (ψ : SchwartzMap (Euc d) ℝ) :
    Integrable (fun ξ : Euc d => (1 + ‖ξ‖) ^ 2 * (|s97_A ψ ξ| + |s97_B ψ ξ|)) := by
  have h0 := (𝓕 (s97_cpl ψ)).integrable_pow_mul (volume : Measure (Euc d)) 0
  have h1 := (𝓕 (s97_cpl ψ)).integrable_pow_mul (volume : Measure (Euc d)) 1
  have h2 := (𝓕 (s97_cpl ψ)).integrable_pow_mul (volume : Measure (Euc d)) 2
  have hs : Integrable (fun ξ : Euc d => 2 * (‖ξ‖ ^ 0 * ‖𝓕 (⇑(s97_cpl ψ)) ξ‖ + 2 * (‖ξ‖ ^ 1 * ‖𝓕 (⇑(s97_cpl ψ)) ξ‖) +
      ‖ξ‖ ^ 2 * ‖𝓕 (⇑(s97_cpl ψ)) ξ‖)) := ((h0.add (h1.const_mul 2)).add h2).const_mul 2
  refine hs.mono' ?_ (Filter.Eventually.of_forall fun ξ => ?_)
  · have := s97_A_cont ψ; have := s97_B_cont ψ
    exact Continuous.aestronglyMeasurable (by fun_prop)
  · have h1 := s97_A_abs_le ψ ξ
    have h2 := s97_B_abs_le ψ ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : 0 ≤ ‖𝓕 (⇑(s97_cpl ψ)) ξ‖ := norm_nonneg _
    nlinarith [sq_nonneg ‖ξ‖, norm_nonneg ξ, mul_nonneg (norm_nonneg ξ) this, mul_nonneg (sq_nonneg ‖ξ‖) this]

theorem s97_sq_eq (ψ : SchwartzMap (Euc d) ℝ) (ξ : Euc d) :
    s97_A ψ ξ ^ 2 + s97_B ψ ξ ^ 2 = ‖𝓕 (⇑(s97_cpl ψ)) ξ‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; unfold s97_A s97_B; ring

theorem s97_sobolev_eq (ψ : SchwartzMap (Euc d) ℝ) (m : ℝ) :
    HRS.PDE.ToolboxRd.sobolevNormSq m (fun x => ψ x) =
      ∫ ξ, wt ξ ^ m * (s97_A ψ ξ ^ 2 + s97_B ψ ξ ^ 2) := by
  unfold HRS.PDE.ToolboxRd.sobolevNormSq
  refine integral_congr_ae ?_
  filter_upwards [fourierL2_schwartz ψ] with ξ hξ
  rw [s97_sq_eq]
  have : HRS.PDE.ToolboxRd.fourierL2 (fun x => ψ x) ξ = 𝓕 (⇑(s97_cpl ψ)) ξ := hξ
  rw [this]; rfl

theorem s97_synth (ψ : SchwartzMap (Euc d) ℝ) (m : ℝ)
    (hψ : HRS.Whole.sobolevNormE m (fun x => ψ x) ≤ 1) :
    Continuous (s97_A ψ) ∧ Continuous (s97_B ψ) ∧
    Integrable (fun ξ : Euc d => (1 + ‖ξ‖) ^ 2 * (|s97_A ψ ξ| + |s97_B ψ ξ|)) ∧
    (∀ x, ψ x = ∫ ξ, (s97_A ψ ξ * Real.cos (2 * Real.pi * inner ℝ x ξ) -
      s97_B ψ ξ * Real.sin (2 * Real.pi * inner ℝ x ξ))) ∧
    (∀ x g, fderiv ℝ ψ x g = ∫ ξ, (-(2 * Real.pi * inner ℝ g ξ)) *
      (s97_A ψ ξ * Real.sin (2 * Real.pi * inner ℝ x ξ) + s97_B ψ ξ * Real.cos (2 * Real.pi * inner ℝ x ξ))) ∧
    ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ m * (s97_A ψ ξ ^ 2 + s97_B ψ ξ ^ 2)) ≤ 1 := by
  refine ⟨s97_A_cont ψ, s97_B_cont ψ, s97_AB_int ψ, s97_inv' ψ, s97_fderiv ψ, ?_⟩
  unfold HRS.Whole.sobolevNormE at hψ
  by_cases hM : HRS.PDE.ToolboxRd.MemSobolev m (fun x => ψ x)
  · rw [if_pos hM] at hψ
    have hsq : HRS.PDE.ToolboxRd.sobolevNormSq m (fun x => ψ x) ≤ 1 := by
      have h1 := (ENNReal.ofReal_le_one).1 hψ
      have h2 := (Real.sqrt_le_iff.1 h1).2
      simpa using h2
    have hint : Integrable (fun ξ : Euc d => wt ξ ^ m * (s97_A ψ ξ ^ 2 + s97_B ψ ξ ^ 2)) := by
      refine hM.2.congr ?_
      filter_upwards [fourierL2_schwartz ψ] with ξ hξ
      rw [s97_sq_eq]
      have : HRS.PDE.ToolboxRd.fourierL2 (fun x => ψ x) ξ = 𝓕 (⇑(s97_cpl ψ)) ξ := hξ
      rw [this]; rfl
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun ξ =>
      mul_nonneg (Real.rpow_nonneg (wt_pos ξ).le _) (by positivity)), ← s97_sobolev_eq]
    exact ENNReal.ofReal_le_one.2 hsq
  · rw [if_neg hM] at hψ
    simp at hψ

end HRS.MS.R2Wfm
end
