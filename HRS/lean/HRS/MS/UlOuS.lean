import HRS.MS.UlOuSAux2

/-!
# UL-3 (S5.1, infrastructure packet): the Ornstein-Uhlenbeck semigroup on the uniformly local spaces

Not a manuscript row.  Notation: `ouSg Q ν τ h x = ∫ h(e^{-τQ} x + y) dN(0,Σ_τ)(y)` (`UlOuAux1`),
`ulocNormE m χ` the continuum uniformly local norm, `χ` an `IsUlocCutoff`.

Statements (all constants depend only on `d, Q, ν, T, m, χ`, uniformly for `τ` in the stated range):

* `ouSg_ulocNormE_le` (U4(a)): `‖ouSg τ h‖_{H^m_uloc} ≤ C ‖h‖_{H^m_uloc}`, `τ ∈ [0,T]`, `h` bounded and
  measurable (hypothesis added to the sketch to exclude the junk value `0` of non-integrable Bochner
  integrals; it is the hypothesis of the merged `ulocNormE_avg_le`).  The pullback by `e^{-τQ}` is the
  uniform version `ul3_comp_unif` of the merged `ulocNormE_comp_linear` (whose constant is not
  uniform in the matrix), proved here with explicit constants (`ul3_sobE_comp`, `ul3_key`).
* `ouSg_ulocNormE_gain` (U4(b)): `‖ouSg τ h‖_{H^{n+1}_uloc} ≤ C (1 + τ^{-1/2}) ‖h‖_{H^n_uloc}` for
  `τ ∈ (0,T]`, `ν > 0` and `h ∈ C_b^1` (`h` is `C¹` with `h`, `Dh` bounded).  Adjustment of the sketch:
  the data class is `C_b^1` instead of the abstract `H^n_uloc`, because the proof differentiates the
  Gaussian average through Stein's identity for the standard Gaussian,
  `∂_j E h(x+SW) = E[h(x+SW) ⟪S^{-1}e_j, W⟫]`, `S = Σ_τ^{1/2}` (no density of `ouLaw` is used);
  `‖S^{-1}e_j‖ ≤ (λτ)^{-1/2}` by `ouCov_bounds`.  The index is `n+1` instead of `m, m-1`.

* `ouSg_sobolevNormE_gain` (U4(c)): for `0 < α ≤ 2`, `t ≥ 0`, `τ ∈ (0,T]`, `ν > 0`:
  `‖ouSg τ h‖_{H^{t+α}} ≤ C τ^{-α/2} ‖h‖_{H^t}`.  Adjustments of the sketch (documented): `h` is bounded,
  measurable and integrable (so that `h`, `ouSg τ h` are in `L¹ ∩ L²` and no junk value occurs), and
  `t ≥ 0`.  No density of `ouLaw` and no use of `tc3_sobolevNormE_gain` is needed: the Fourier transform
  of the translation average is `charFun (ouLaw τ) (2πξ) · ĥ` (`ul3_avg_fourier`), and
  `|charFun|² = exp(-4π² ⟪ξ,Σ_τ ξ⟫) ≤ exp(-λτ (4π²|ξ|²))` against `⟨ξ⟩^{α}` gives `A τ^{-α}`
  (`ul3_gauss_sup`); the pullback by `e^{-τQ}` is `ul3_sobE_comp` (real order, explicit constant).

Not proved (the packet stopped at the size limit): U4(d), strong continuity of `τ ↦ ouSg τ f` in
`ulNormE k θ` on `UlClosure k θ` and `ouSg τ (UlClosure k θ) ⊆ UlClosure k θ` (see the report).

Helper lemmas carry the prefix `ul3_` (files `UlOuSAux1`, `UlOuSAux2`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff ComplexConjugate FourierTransform RealInnerProductSpace Matrix MatrixOrder

namespace HRS.MS.Ul
open HRS HRS.Whole HRS.Whole.AppendixA HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UlocMW

variable {d : ℕ}


/-- **UL-3 (a)**: `ulocNormE m χ (ouSg τ h) ≤ C ulocNormE m χ h`, uniformly in `τ ∈ [0,T]`
(`h` bounded measurable). -/
theorem ouSg_ulocNormE_le (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (Q : Matrix (Fin d) (Fin d) ℝ) (ν T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ h : Euc d → ℝ, Measurable h →
      (∃ B : ℝ, ∀ x, |h x| ≤ B) →
      ulocNormE m χ (ouSg Q ν τ h) ≤ ENNReal.ofReal C * ulocNormE m χ h := by
  obtain ⟨K, hK1, hK⟩ := ul3_exp_unif Q T
  obtain ⟨C, hC, hcomp⟩ := ul3_comp_unif m χ hχ K hK1
  refine ⟨C, hC, fun τ hτ h hm ⟨B, hB⟩ => ?_⟩
  obtain ⟨e, he, hes⟩ := ul3_equiv_exp Q τ
  obtain ⟨h1, h2, h3⟩ := hK τ hτ
  have h4 : ‖LinearMap.toContinuousLinearMap (e : Euc d →ₗ[ℝ] Euc d)‖ ≤ K := by
    rw [ul3_toCLM_exp Q τ e he]; exact h1
  have h5 : ‖LinearMap.toContinuousLinearMap (e.symm : Euc d →ₗ[ℝ] Euc d)‖ ≤ K := by
    rw [ul3_toCLM_exp Q (-τ) e.symm hes]; exact h2
  have h6 : K⁻¹ ≤ |LinearMap.det (e : Euc d →ₗ[ℝ] Euc d)| := by
    have : (e : Euc d →ₗ[ℝ] Euc d) = ((ouExp Q τ : Euc d →L[ℝ] Euc d) : Euc d →ₗ[ℝ] Euc d) :=
      LinearMap.ext he
    rw [this]; exact h3
  have key := hcomp e h4 h5 h6 (fun x => ∫ y, h (x + y) ∂(ouLaw Q ν τ))
  have hsg : ouSg Q ν τ h = fun x => (fun x => ∫ y, h (x + y) ∂(ouLaw Q ν τ)) (e x) := by
    funext x; simp only [ouSg, he]
  rw [hsg]
  exact key.trans (by gcongr; exact ulocNormE_avg_le m χ hχ (ouLaw Q ν τ) h hm B hB)


/-- **UL-3 (b)**, integer gain: for `τ ∈ (0,T]`, `h ∈ C_b^1`,
`‖ouSg τ h‖_{H^{n+1}_uloc} ≤ C (1 + τ^{-1/2}) ‖h‖_{H^n_uloc}`. -/
theorem ouSg_ulocNormE_gain (n : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) (T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ Set.Ioc (0 : ℝ) T, ∀ h : Euc d → ℝ, ContDiff ℝ 1 h → ∀ B M : ℝ,
      (∀ y, |h y| ≤ B) → (∀ y, ‖fderiv ℝ h y‖ ≤ M) →
      ulocNormE (n + 1) χ (ouSg Q ν τ h) ≤
        ENNReal.ofReal (C * (1 + 1 / Real.sqrt τ)) * ulocNormE n χ h := by
  obtain ⟨K, hK1, hK⟩ := ul3_exp_unif Q T
  obtain ⟨Ccomp, hCcomp, hcomp⟩ := ul3_comp_unif (n + 1) χ hχ K hK1
  obtain ⟨Cg, hCg, hgain⟩ := ul3_avg_gain n χ hχ
  obtain ⟨lam, Lam, hlam, -, hcov⟩ := ouCov_bounds Q hν T
  refine ⟨Ccomp * Cg * (1 + 1 / Real.sqrt lam), by positivity, fun τ hτ h hh B M hB hM => ?_⟩
  have hτ0 : 0 < τ := hτ.1
  have hτT : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ0.le, hτ.2⟩
  have hPSD := ouCov_posSemidef Q hν.le hτ0.le
  have hbd : ∀ ξ : Euc d, lam * τ * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ ouCov Q ν τ *ᵥ ξ := fun ξ => (hcov τ hτT ξ).1
  set S : Euc d →L[ℝ] Euc d := Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (ouCov Q ν τ)) with hS
  set κ : ℝ := 1 / Real.sqrt (lam * τ) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hpre : ∀ j : Fin d, ∃ c : Euc d, S c = EuclideanSpace.single j 1 ∧ ‖c‖ ≤ κ := by
    intro j
    obtain ⟨c, hc1, hc2⟩ := ul3_S_preimage hPSD (mul_pos hlam hτ0) hbd (EuclideanSpace.single j (1 : ℝ))
    exact ⟨c, hc1, by simpa [hκ] using hc2⟩
  have hg := hgain S κ hκ0 hpre h hh B M hB hM
  -- the semigroup is the Gaussian average composed with `e^{-τQ}`
  obtain ⟨e, he, hes⟩ := ul3_equiv_exp Q τ
  obtain ⟨h1, h2, h3⟩ := hK τ hτT
  have h4 : ‖LinearMap.toContinuousLinearMap (e : Euc d →ₗ[ℝ] Euc d)‖ ≤ K := by
    rw [ul3_toCLM_exp Q τ e he]; exact h1
  have h5 : ‖LinearMap.toContinuousLinearMap (e.symm : Euc d →ₗ[ℝ] Euc d)‖ ≤ K := by
    rw [ul3_toCLM_exp Q (-τ) e.symm hes]; exact h2
  have h6 : K⁻¹ ≤ |LinearMap.det (e : Euc d →ₗ[ℝ] Euc d)| := by
    have : (e : Euc d →ₗ[ℝ] Euc d) = ((ouExp Q τ : Euc d →L[ℝ] Euc d) : Euc d →ₗ[ℝ] Euc d) :=
      LinearMap.ext he
    rw [this]; exact h3
  have hsg : ouSg Q ν τ h = fun x => (fun x => ∫ w, h (x + S w) ∂(stdGaussian (Euc d))) (e x) := by
    funext x
    simp only [ouSg, he, ouLaw_eq_map]
    exact integral_map (f := fun y : Euc d => h (ouExp Q τ x + y)) S.continuous.measurable.aemeasurable
      (hh.continuous.measurable.comp (measurable_const.add measurable_id)).aestronglyMeasurable
  rw [hsg]
  have hsq : 1 / Real.sqrt (lam * τ) = 1 / Real.sqrt lam * (1 / Real.sqrt τ) := by
    rw [Real.sqrt_mul hlam.le]; field_simp
  have hp1 : 0 ≤ 1 / Real.sqrt lam := by positivity
  have hp2 : 0 ≤ 1 / Real.sqrt τ := by positivity
  have hreal : Ccomp * (Cg * (1 + κ)) ≤
      Ccomp * Cg * (1 + 1 / Real.sqrt lam) * (1 + 1 / Real.sqrt τ) := by
    rw [hκ, hsq]
    have := mul_nonneg hCcomp.le hCg.le
    nlinarith [mul_nonneg this hp1, mul_nonneg this hp2, mul_nonneg this (mul_nonneg hp1 hp2)]
  have key := hcomp e h4 h5 h6 (fun x => ∫ w, h (x + S w) ∂(stdGaussian (Euc d)))
  calc _ ≤ ENNReal.ofReal Ccomp * ulocNormE (n + 1) χ (fun x => ∫ w, h (x + S w) ∂(stdGaussian (Euc d))) := key
    _ ≤ ENNReal.ofReal Ccomp * (ENNReal.ofReal (Cg * (1 + κ)) * ulocNormE n χ h) := mul_le_mul' le_rfl hg
    _ = ENNReal.ofReal (Ccomp * (Cg * (1 + κ))) * ulocNormE n χ h := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hCcomp.le]
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) le_rfl


/-- **UL-3 (c)**, global fractional gain: for `0 < α ≤ 2`, `t ≥ 0`, `τ ∈ (0,T]`,
`‖ouSg τ h‖_{H^{t+α}} ≤ C τ^{-α/2} ‖h‖_{H^t}` (`h` bounded, measurable and integrable). -/
theorem ouSg_sobolevNormE_gain (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) (T : ℝ)
    {t α : ℝ} (ht : 0 ≤ t) (hα : 0 < α) (hα2 : α ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ Set.Ioc (0 : ℝ) T, ∀ h : Euc d → ℝ, Measurable h →
      (∃ B : ℝ, ∀ x, |h x| ≤ B) → Integrable h volume →
      sobolevNormE (t + α) (ouSg Q ν τ h) ≤
        ENNReal.ofReal (C * τ ^ (-α / 2)) * sobolevNormE t h := by
  obtain ⟨K, hK1, hK⟩ := ul3_exp_unif Q T
  obtain ⟨lam, Lam, hlam, -, hcov⟩ := ouCov_bounds Q hν T
  obtain ⟨A, hA, hAsup⟩ := ul3_gauss_sup hlam T hα hα2
  have hK0 : 0 < K := by linarith
  set Kc : ℝ := Real.sqrt (K * (1 + K ^ 2) ^ (t + α)) with hKc
  have hKcpos : 0 < Kc := Real.sqrt_pos.2 (by positivity)
  refine ⟨Kc * Real.sqrt A, by positivity, fun τ hτ h hm ⟨B, hB⟩ hi => ?_⟩
  have hτ0 : 0 < τ := hτ.1
  have hτT : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ0.le, hτ.2⟩
  set μ := ouLaw Q ν τ with hμ
  obtain ⟨haint, hafour⟩ := ul3_avg_fourier μ h hm hi
  set a : Euc d → ℝ := fun x => ∫ y, h (x + y) ∂μ with ha
  have ham : Measurable a :=
    (StronglyMeasurable.integral_prod_right (f := fun (x y : Euc d) => h (x + y)) (ν := μ)
      (hm.comp (measurable_fst.add measurable_snd)).stronglyMeasurable).measurable
  have haB : ∀ x, |a x| ≤ B := fun x => by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun y => h (x + y)) (C := B)
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hB (x + y))
    simpa [ha, Real.norm_eq_abs] using this
  have L2 : ∀ f : Euc d → ℝ, Measurable f → Integrable f volume → (∀ x, |f x| ≤ B) → MemLp f 2 volume := by
    intro f hf hfi hfB
    refine (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 ?_
    refine (hfi.norm.const_mul B).mono' (hf.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
    nlinarith [mul_nonneg (abs_nonneg (f x)) (sub_nonneg.2 (hfB x))]
  have hh2 : MemLp h 2 volume := L2 h hm hi hB
  have ha2 : MemLp a 2 volume := L2 a ham haint haB
  -- the Fourier multiplier bound
  have hbd : ∀ ξ : Euc d, lam * τ * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ ouCov Q ν τ *ᵥ ξ := fun ξ => (hcov τ hτT ξ).1
  set Fh : Euc d → ℂ := fun x => ((h x : ℝ) : ℂ) with hFh
  set Fa : Euc d → ℂ := fun x => ((a x : ℝ) : ℂ) with hFa
  have hchar : ∀ ξ : Euc d, (∫ y, Complex.exp (↑(2 * Real.pi * ⟪y, ξ⟫) * Complex.I) ∂μ) =
      charFun μ ((2 * Real.pi) • ξ) := by
    intro ξ
    rw [charFun_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [real_inner_smul_right]
  have hpt : ∀ ξ : Euc d, ENNReal.ofReal (wt ξ ^ (t + α) * ‖𝓕 Fa ξ‖ ^ 2) ≤
      ENNReal.ofReal (A * τ ^ (-α)) * ENNReal.ofReal (wt ξ ^ t * ‖𝓕 Fh ξ‖ ^ 2) := by
    intro ξ
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : ‖𝓕 Fa ξ‖ = ‖charFun μ ((2 * Real.pi) • ξ)‖ * ‖𝓕 Fh ξ‖ := by
      rw [hafour ξ, hchar ξ, norm_mul]
    have h2 := ul3_ou_charFun_sq Q hν.le hτ0.le hbd ξ
    have h3 := hAsup τ hτ (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) (by positivity)
    have hwt1 : 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 = wt ξ := rfl
    rw [hwt1] at h3
    have h4 : wt ξ ^ (t + α) = wt ξ ^ t * wt ξ ^ α := Real.rpow_add (wt_pos ξ) t α
    rw [h1, h4, mul_pow]
    have hF : 0 ≤ wt ξ ^ t * ‖𝓕 Fh ξ‖ ^ 2 := mul_nonneg (Real.rpow_nonneg (wt_pos ξ).le _) (sq_nonneg _)
    have h5 : wt ξ ^ α * ‖charFun μ ((2 * Real.pi) • ξ)‖ ^ 2 ≤ A * τ ^ (-α) :=
      (mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (wt_pos ξ).le _)).trans h3
    calc wt ξ ^ t * wt ξ ^ α * (‖charFun μ ((2 * Real.pi) • ξ)‖ ^ 2 * ‖𝓕 Fh ξ‖ ^ 2)
        = (wt ξ ^ t * ‖𝓕 Fh ξ‖ ^ 2) * (wt ξ ^ α * ‖charFun μ ((2 * Real.pi) • ξ)‖ ^ 2) := by ring
      _ ≤ (wt ξ ^ t * ‖𝓕 Fh ξ‖ ^ 2) * (A * τ ^ (-α)) := mul_le_mul_of_nonneg_left h5 hF
      _ = A * τ ^ (-α) * (wt ξ ^ t * ‖𝓕 Fh ξ‖ ^ 2) := by ring
  have hsq : sobolevNormE (t + α) a ^ 2 ≤ ENNReal.ofReal (A * τ ^ (-α)) * sobolevNormE t h ^ 2 := by
    rw [um_sobE_sq ha2, um_sobE_sq hh2]
    have e1 : ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ (t + α) * ‖fourierL2 a ξ‖ ^ 2) =
        ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ (t + α) * ‖𝓕 Fa ξ‖ ^ 2) := by
      refine lintegral_congr_ae ?_
      filter_upwards [um_L1L2 haint ha2] with ξ hξ
      rw [hξ]
    have e2 : ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ t * ‖fourierL2 h ξ‖ ^ 2) =
        ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ t * ‖𝓕 Fh ξ‖ ^ 2) := by
      refine lintegral_congr_ae ?_
      filter_upwards [um_L1L2 hi hh2] with ξ hξ
      rw [hξ]
    rw [e1, e2, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono hpt
  have hsq' : sobolevNormE (t + α) a ≤
      ENNReal.ofReal (Real.sqrt A * τ ^ (-α / 2)) * sobolevNormE t h := by
    have e : Real.sqrt A * τ ^ (-α / 2) = Real.sqrt (A * τ ^ (-α)) := by
      rw [Real.sqrt_mul hA.le, Real.sqrt_eq_rpow (τ ^ (-α)), ← Real.rpow_mul hτ0.le]
      congr 2; ring
    rw [e]
    refine (ENNReal.pow_le_pow_left_iff (n := 2) two_ne_zero).1 ?_
    rw [mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
    exact hsq
  -- pullback by `e^{-τQ}`
  obtain ⟨e, he, hes⟩ := ul3_equiv_exp Q τ
  obtain ⟨h1, h2, h3⟩ := hK τ hτT
  have hsg : ouSg Q ν τ h = fun x => a (e x) := by
    funext x; simp only [ouSg, he]; rfl
  have hcomp := ul3_sobE_comp (t + α) (by linarith) e a ha2 haint
  have h4 : ‖LinearMap.toContinuousLinearMap (e : Euc d →ₗ[ℝ] Euc d)‖ ≤ K := by
    rw [ul3_toCLM_exp Q τ e he]; exact h1
  have h6 : K⁻¹ ≤ |LinearMap.det (e : Euc d →ₗ[ℝ] Euc d)| := by
    have : (e : Euc d →ₗ[ℝ] Euc d) = ((ouExp Q τ : Euc d →L[ℝ] Euc d) : Euc d →ₗ[ℝ] Euc d) :=
      LinearMap.ext he
    rw [this]; exact h3
  have hKdet : ENNReal.ofReal (Real.sqrt (|LinearMap.det (e : Euc d →ₗ[ℝ] Euc d)|⁻¹ *
      (1 + ‖LinearMap.toContinuousLinearMap (e : Euc d →ₗ[ℝ] Euc d)‖ ^ 2) ^ (t + α))) ≤
      ENNReal.ofReal Kc := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.sqrt_le_sqrt
    have h7 : |LinearMap.det (e : Euc d →ₗ[ℝ] Euc d)|⁻¹ ≤ K := by
      have := inv_anti₀ (inv_pos.2 hK0) h6
      simpa using this
    have h8 : (1 + ‖LinearMap.toContinuousLinearMap (e : Euc d →ₗ[ℝ] Euc d)‖ ^ 2) ^ (t + α) ≤
        (1 + K ^ 2) ^ (t + α) :=
      Real.rpow_le_rpow (by positivity) (by gcongr) (by linarith)
    exact mul_le_mul h7 h8 (by positivity) hK0.le
  rw [hsg]
  calc _ ≤ ENNReal.ofReal Kc * sobolevNormE (t + α) a := hcomp.trans (by gcongr)
    _ ≤ ENNReal.ofReal Kc * (ENNReal.ofReal (Real.sqrt A * τ ^ (-α / 2)) * sobolevNormE t h) :=
        mul_le_mul' le_rfl hsq'
    _ = ENNReal.ofReal (Kc * Real.sqrt A * τ ^ (-α / 2)) * sobolevNormE t h := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hKcpos.le, mul_assoc]

end HRS.MS.Ul
