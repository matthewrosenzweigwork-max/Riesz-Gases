import HRS.Commutator.Whole.Defs
import HRS.Commutator.Whole.RieszAux

/-!
# CMX-KR auxiliary (1): the Fourier transform of `∇g` against test functions vanishing near `0`

For a Schwartz function `Φ` vanishing on `B̄(0,1)`:
`∫ ∇g_i · 𝓕Φ = c ∫ ξ_i |ξ|^{-(d-s)} Φ(ξ) dξ`, from `riesz_potential_aux` with `γ = s + 2`
applied to `∂_i Φ`, and one integration by parts (Mathlib, `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`).
Names prefixed `cmxMY_`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

/-- Fourier transform of a coordinate derivative of a Schwartz function. -/
lemma cmxMY_fourier_partial (Φ : SchwartzMap (Euc d) ℂ) (i : Fin d) (x : Euc d) :
    𝓕 (fun ξ : Euc d => fderiv ℝ Φ ξ (EuclideanSpace.single i (1 : ℝ))) x =
      (2 * Real.pi * Complex.I * (x i : ℂ)) * 𝓕 (⇑Φ) x := by
  set m : Euc d := EuclideanSpace.single i (1 : ℝ) with hm
  have h := congrArg (fun T : SchwartzMap (Euc d) ℂ => T x)
    (SchwartzMap.fourier_lineDerivOp_eq Φ m)
  have hL : (⇑(LineDeriv.lineDerivOp m Φ) : Euc d → ℂ) = fun ξ => fderiv ℝ Φ ξ m :=
    funext (SchwartzMap.lineDerivOp_apply_eq_fderiv m Φ)
  have hg : (fun x : Euc d => inner ℝ x m).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  simp only [SchwartzMap.smulLeftCLM_apply_apply hg, smul_apply, SchwartzMap.fourier_coe] at h
  rw [hL] at h
  rw [h]
  simp [hm, smul_eq_mul, EuclideanSpace.inner_single_right]
  ring

lemma cmxMY_hasFDerivAt_norm_rpow (p : ℝ) (x : Euc d) (hx : x ≠ 0) :
    HasFDerivAt (fun ξ : Euc d => ‖ξ‖ ^ p) ((p * ‖x‖ ^ (p - 2)) • innerSL ℝ x) x := by
  have h1 : HasFDerivAt (fun ξ : Euc d => ‖ξ‖ ^ 2) ((2 : ℕ) • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have h2 := h1.rpow_const (p := p / 2) (Or.inl (by positivity))
  have e : (fun ξ : Euc d => (‖ξ‖ ^ 2) ^ (p / 2)) = fun ξ : Euc d => ‖ξ‖ ^ p := by
    funext ξ
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg ξ)]
    norm_num
    congr 1; ring
  rw [e] at h2
  convert h2 using 1
  have : (‖x‖ ^ 2) ^ (p / 2 - 1) = ‖x‖ ^ (p - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg x)]
    congr 1; push_cast; ring
  rw [this]
  ext y
  simp
  ring

lemma cmxMY_fderiv_norm_rpow_complex (p : ℝ) (x : Euc d) (hx : x ≠ 0) (i : Fin d) :
    HasFDerivAt (fun ξ : Euc d => ((‖ξ‖ ^ p : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((p * ‖x‖ ^ (p - 2)) • innerSL ℝ x)) x ∧
    fderiv ℝ (fun ξ : Euc d => ((‖ξ‖ ^ p : ℝ) : ℂ)) x (EuclideanSpace.single i (1 : ℝ)) =
      ((p * ‖x‖ ^ (p - 2) * x i : ℝ) : ℂ) := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp x (cmxMY_hasFDerivAt_norm_rpow p x hx)
  refine ⟨h, ?_⟩
  have h' : HasFDerivAt (fun ξ : Euc d => ((‖ξ‖ ^ p : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((p * ‖x‖ ^ (p - 2)) • innerSL ℝ x)) x := h
  rw [h'.fderiv]
  simp [EuclideanSpace.inner_single_right]

lemma cmxMY_ibp (Φ : SchwartzMap (Euc d) ℂ) (hΦ : ∀ ξ : Euc d, ‖ξ‖ ≤ 1 → Φ ξ = 0) {p : ℝ}
    (hp : p ≤ 0) (i : Fin d) :
    ∫ ξ : Euc d, ((‖ξ‖ ^ p : ℝ) : ℂ) * fderiv ℝ Φ ξ (EuclideanSpace.single i (1 : ℝ)) =
      -∫ ξ : Euc d, ((p * ‖ξ‖ ^ (p - 2) * ξ i : ℝ) : ℂ) * Φ ξ := by
  set m : Euc d := EuclideanSpace.single i (1 : ℝ) with hm
  set f : Euc d → ℂ := fun ξ => ((‖ξ‖ ^ p : ℝ) : ℂ) with hf
  have hΦ0 : ∀ ξ : Euc d, ‖ξ‖ < 1 → fderiv ℝ Φ ξ = 0 := by
    intro ξ hξ
    have : (⇑Φ : Euc d → ℂ) =ᶠ[𝓝 ξ] fun _ => (0 : ℂ) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (show ξ ∈ Metric.ball (0 : Euc d) 1 by simpa using hξ)]
        with y hy
      exact hΦ y (by have := mem_ball_zero_iff.1 hy; linarith)
    rw [this.fderiv_eq]; simp
  have hfb : ∀ ξ : Euc d, 1 ≤ ‖ξ‖ → ‖f ξ‖ ≤ 1 := by
    intro ξ hξ
    simp only [hf, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hξ hp
  have hfm : Measurable f := Complex.measurable_ofReal.comp (measurable_norm.pow_const p)
  have hsupp : ∀ ξ ∈ tsupport (⇑Φ : Euc d → ℂ), 1 ≤ ‖ξ‖ := by
    intro ξ hξ
    have : tsupport (⇑Φ : Euc d → ℂ) ⊆ {ξ : Euc d | 1 ≤ ‖ξ‖} := by
      refine closure_minimal ?_ (isClosed_le continuous_const continuous_norm)
      intro η hη
      by_contra h
      exact hη (hΦ η (by simpa using (not_le.1 h).le))
    exact this hξ
  have hΦd : Differentiable ℝ Φ := (Φ.smooth 1).differentiable (by simp)
  -- explicit derivative on the support
  have hEq : ∀ ξ : Euc d, fderiv ℝ f ξ m * Φ ξ = ((p * ‖ξ‖ ^ (p - 2) * ξ i : ℝ) : ℂ) * Φ ξ := by
    intro ξ
    by_cases h0 : Φ ξ = 0
    · simp [h0]
    · have h1 : 1 ≤ ‖ξ‖ := hsupp ξ (subset_closure (Function.mem_support.2 h0))
      have hξ0 : ξ ≠ 0 := norm_ne_zero_iff.1 (by linarith)
      rw [(cmxMY_fderiv_norm_rpow_complex p ξ hξ0 i).2]
  have hbd1 : ∀ ξ : Euc d, ‖((p * ‖ξ‖ ^ (p - 2) * ξ i : ℝ) : ℂ) * Φ ξ‖ ≤ |p| * ‖Φ ξ‖ := by
    intro ξ
    by_cases h0 : Φ ξ = 0
    · simp [h0]
    · have h1 : 1 ≤ ‖ξ‖ := hsupp ξ (subset_closure (Function.mem_support.2 h0))
      have hξ0 : 0 < ‖ξ‖ := by linarith
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul]
      have hxi : |ξ i| ≤ ‖ξ‖ := by
        simpa using PiLp.norm_apply_le ξ i
      have h2 : |‖ξ‖ ^ (p - 2)| * |ξ i| ≤ 1 := by
        rw [abs_of_nonneg (by positivity)]
        calc ‖ξ‖ ^ (p - 2) * |ξ i| ≤ ‖ξ‖ ^ (p - 2) * ‖ξ‖ := by gcongr
          _ = ‖ξ‖ ^ (p - 2 + 1) := by rw [Real.rpow_add hξ0, Real.rpow_one]
          _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
      calc |p| * |‖ξ‖ ^ (p - 2)| * |ξ i| * ‖Φ ξ‖ = |p| * (|‖ξ‖ ^ (p - 2)| * |ξ i|) * ‖Φ ξ‖ := by ring
        _ ≤ |p| * 1 * ‖Φ ξ‖ := by gcongr
        _ = _ := by ring
  have hΦi : Integrable (fun ξ : Euc d => ‖Φ ξ‖) := Φ.integrable.norm
  have hI3 : Integrable (fun ξ : Euc d => f ξ * Φ ξ) := by
    refine hΦi.mono' (hfm.aestronglyMeasurable.mul Φ.continuous.aestronglyMeasurable) ?_
    refine Eventually.of_forall fun ξ => ?_
    by_cases h0 : Φ ξ = 0
    · simp [h0]
    · have h1 : 1 ≤ ‖ξ‖ := hsupp ξ (subset_closure (Function.mem_support.2 h0))
      rw [norm_mul]
      calc ‖f ξ‖ * ‖Φ ξ‖ ≤ 1 * ‖Φ ξ‖ := by gcongr; exact hfb ξ h1
        _ = _ := one_mul _
  have hdΦ : Integrable (fun ξ : Euc d => fderiv ℝ Φ ξ m) := by
    have := SchwartzMap.integrable (μ := (volume : Measure (Euc d)))
      (LineDeriv.lineDerivOp m Φ : SchwartzMap (Euc d) ℂ)
    have hL : (⇑(LineDeriv.lineDerivOp m Φ) : Euc d → ℂ) = fun ξ => fderiv ℝ Φ ξ m :=
      funext (SchwartzMap.lineDerivOp_apply_eq_fderiv m Φ)
    rwa [hL] at this
  have hI2 : Integrable (fun ξ : Euc d => f ξ * fderiv ℝ Φ ξ m) := by
    refine hdΦ.norm.mono' (hfm.aestronglyMeasurable.mul
      (hdΦ.aestronglyMeasurable)) ?_
    refine Eventually.of_forall fun ξ => ?_
    by_cases h1 : ‖ξ‖ < 1
    · simp [hΦ0 ξ h1]
    · rw [norm_mul]
      calc ‖f ξ‖ * ‖fderiv ℝ Φ ξ m‖ ≤ 1 * ‖fderiv ℝ Φ ξ m‖ := by
            gcongr; exact hfb ξ (not_lt.1 h1)
        _ = _ := one_mul _
  have hI1 : Integrable (fun ξ : Euc d => fderiv ℝ f ξ m * Φ ξ) := by
    simp_rw [hEq]
    refine (hΦi.const_mul |p|).mono' ?_ (Eventually.of_forall hbd1)
    refine ((Complex.measurable_ofReal.comp ?_).aestronglyMeasurable).mul Φ.continuous.aestronglyMeasurable
    exact ((measurable_const.mul (measurable_norm.pow_const (p - 2))).mul
      (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.measurable)
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Euc d)))
    (f := f) (g := ⇑Φ) (v := m) hI1 hI2 hI3
    (fun x hx => (cmxMY_fderiv_norm_rpow_complex p x (norm_ne_zero_iff.1
      (by linarith [hsupp x hx])) i).1.differentiableAt) (fun x _ => hΦd x)
  rw [key]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  exact hEq ξ

theorem cmxMY_kernGrad_fourier (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ c : ℂ, ∀ (i : Fin d) (Φ : SchwartzMap (Euc d) ℂ), (∀ ξ : Euc d, ‖ξ‖ ≤ 1 → Φ ξ = 0) →
      ∫ x : Euc d, ((kernGrad s x i : ℝ) : ℂ) * 𝓕 (⇑Φ) x =
        c * ∫ ξ : Euc d, (((ξ i) * ‖ξ‖ ^ (-((d : ℝ) - s)) : ℝ) : ℂ) * Φ ξ := by
  have hd1 : 1 ≤ d := by omega
  set γ : ℝ := s + 2 with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  have hγd : γ < d := by rw [hγ]; linarith
  set P : ℝ := Real.pi ^ (-γ / 2) * Real.Gamma (γ / 2) with hP
  set Q : ℝ := Real.pi ^ (-((d : ℝ) - γ) / 2) * Real.Gamma (((d : ℝ) - γ) / 2) with hQ
  have hPpos : 0 < P := by
    rw [hP]; exact mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by linarith))
  set p : ℝ := γ - d with hp
  have hp0 : p ≤ 0 := by rw [hp]; linarith
  refine ⟨((Q * p : ℝ) : ℂ) / (2 * Real.pi * Complex.I * (P : ℂ)), fun i Φ hΦ => ?_⟩
  set m : Euc d := EuclideanSpace.single i (1 : ℝ) with hm
  set Ψ : SchwartzMap (Euc d) ℂ := LineDeriv.lineDerivOp m Φ with hΨ
  have hΨf : (⇑Ψ : Euc d → ℂ) = fun ξ => fderiv ℝ Φ ξ m :=
    funext (SchwartzMap.lineDerivOp_apply_eq_fderiv m Φ)
  have hR := riesz_potential_aux hd1 γ hγ0 hγd Ψ
  rw [hΨf] at hR
  have hF : ∀ x : Euc d, 𝓕 (fun ξ : Euc d => fderiv ℝ Φ ξ m) x =
      (2 * Real.pi * Complex.I * (x i : ℂ)) * 𝓕 (⇑Φ) x :=
    fun x => cmxMY_fourier_partial Φ i x
  simp_rw [hF] at hR
  have hibp := cmxMY_ibp Φ hΦ hp0 i
  have e1 : ∫ x : Euc d, ((‖x‖ ^ (-γ) : ℝ) : ℂ) * ((2 * Real.pi * Complex.I * (x i : ℂ)) * 𝓕 (⇑Φ) x) =
      (2 * Real.pi * Complex.I) * ∫ x : Euc d, (((‖x‖ ^ (-γ) * x i : ℝ)) : ℂ) * 𝓕 (⇑Φ) x := by
    rw [← integral_const_mul]
    congr 1; ext x; push_cast; ring
  have e2 : ∫ x : Euc d, ((kernGrad s x i : ℝ) : ℂ) * 𝓕 (⇑Φ) x =
      -∫ x : Euc d, (((‖x‖ ^ (-γ) * x i : ℝ)) : ℂ) * 𝓕 (⇑Φ) x := by
    rw [← integral_neg]
    congr 1; ext x
    have : kernGrad s x i = -(‖x‖ ^ (-γ) * x i) := by
      simp [kernGrad, hγ]
    rw [this]; push_cast; ring
  have e3 : ∫ ξ : Euc d, ((p * ‖ξ‖ ^ (p - 2) * ξ i : ℝ) : ℂ) * Φ ξ =
      (p : ℂ) * ∫ ξ : Euc d, (((ξ i) * ‖ξ‖ ^ (-((d : ℝ) - s)) : ℝ) : ℂ) * Φ ξ := by
    rw [← integral_const_mul]
    congr 1; ext ξ
    have : p - 2 = -((d : ℝ) - s) := by rw [hp, hγ]; ring
    rw [this]; push_cast; ring
  rw [e1, hibp, e3] at hR
  rw [e2]
  have hPc : (P : ℂ) ≠ 0 := by exact_mod_cast hPpos.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : (2 * Real.pi * Complex.I * (P : ℂ)) ≠ 0 := by
    simp [hPc, hpi, Complex.I_ne_zero]
  set I₁ : ℂ := ∫ x : Euc d, (((‖x‖ ^ (-γ) * x i : ℝ)) : ℂ) * 𝓕 (⇑Φ) x
  set J : ℂ := ∫ ξ : Euc d, (((ξ i) * ‖ξ‖ ^ (-((d : ℝ) - s)) : ℝ) : ℂ) * Φ ξ
  rw [div_mul_eq_mul_div, eq_div_iff h2]
  push_cast
  linear_combination (-1 : ℂ) * hR

end HRS.Commutator.Whole
