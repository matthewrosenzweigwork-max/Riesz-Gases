import HRS.MS.UlNormAux2

/-!
# UL-0, part 3: averaging of translates (`ulocNormE_avg_le`) and linear pullback (`ulocNormE_comp_linear`)

* `ulocNormE_avg_le`: for a probability measure `μ` on `ℝ^d` and a bounded measurable `h`,
  `‖x ↦ ∫ h(x+y) dμ(y)‖_{H^m_uloc} ≤ ‖h‖_{H^m_uloc}`.  Route: all pieces `χ(·-z) h(·+y)` have compact
  support and are bounded, so `fourierL2` is the `L¹` Fourier integral; Fubini gives
  `𝓕(χ(·-z) a)(ξ) = ∫ 𝓕(χ(·-z) h(·+y))(ξ) dμ(y)`, then Cauchy-Schwarz for the probability measure
  `μ` (`‖∫ F dμ‖² ≤ ∫ ‖F‖² dμ`, in `ℝ≥0∞` through `sobmul_cs`), Tonelli, and translation invariance of
  `sobolevNormE`.  The sketch assumed integrability of `h(x+·)` only; we assume `h` measurable and bounded
  (harmless: all consumers apply it to `C_b` data), which also excludes the junk value `0` of non-integrable
  Bochner integrals.
* `ulocNormE_comp_linear`: for an invertible matrix `A` there is `C` with `‖h ∘ A‖_{ul} ≤ C ‖h‖_{ul}`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff ComplexConjugate FourierTransform RealInnerProductSpace

namespace HRS.MS.Ul
open HRS.Whole HRS.Whole.AppendixA HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UlocMW

variable {d : ℕ}

/-! ### A compactly supported continuous function times a bounded measurable one -/

theorem ul0_memLp_integrable_mul {cz : Euc d → ℝ} (hc : Continuous cz) (hcs : HasCompactSupport cz)
    {w : Euc d → ℝ} (hw : AEStronglyMeasurable w volume) (B : ℝ) (hB : ∀ x, |w x| ≤ B) :
    MemLp (fun x => cz x * w x) 2 volume ∧ Integrable (fun x => cz x * w x) volume := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hbd : ∀ x, ‖cz x * w x‖ ≤ ‖B * cz x‖ := fun x => by
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hB0]
    nlinarith [abs_nonneg (cz x), hB x]
  refine ⟨?_, ?_⟩
  · exact MemLp.of_le ((hc.memLp_of_hasCompactSupport hcs).const_mul B) (hc.aestronglyMeasurable.mul hw)
      (Filter.Eventually.of_forall hbd)
  · exact Integrable.mono' ((hc.integrable_of_hasCompactSupport hcs).const_mul B).norm
      (hc.aestronglyMeasurable.mul hw) (Filter.Eventually.of_forall fun x => by
        have := hbd x
        rw [norm_mul, norm_mul] at this ⊢
        simpa [norm_mul] using this)


/-- Fubini: the Fourier transform of the average is the average of the Fourier transforms -/
theorem ul0_fourier_avg (cz : Euc d → ℝ) (hc : Continuous cz) (hcs : HasCompactSupport cz)
    (h : Euc d → ℝ) (hm : Measurable h) (B : ℝ) (hB : ∀ x, |h x| ≤ B)
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (ξ : Euc d) :
    𝓕 (fun x : Euc d => (((cz x * ∫ y, h (x + y) ∂μ : ℝ)) : ℂ)) ξ =
      ∫ y, 𝓕 (fun x : Euc d => (((cz x * h (x + y) : ℝ)) : ℂ)) ξ ∂μ := by
  simp only [Real.fourier_eq']
  set E : Euc d → ℂ := fun x => Complex.exp ((↑(-2 * Real.pi * ⟪x, ξ⟫) * Complex.I)) with hE
  have hEc : Continuous E := by
    rw [hE]; fun_prop
  have hEn : ∀ x, ‖E x‖ = 1 := fun x => by
    rw [hE]; exact Complex.norm_exp_ofReal_mul_I _
  have step1 : ∀ x : Euc d, E x • (((cz x * ∫ y, h (x + y) ∂μ : ℝ) : ℂ)) =
      ∫ y, E x • (((cz x * h (x + y) : ℝ) : ℂ)) ∂μ := by
    intro x
    rw [integral_smul]
    congr 1
    rw [integral_complex_ofReal, integral_const_mul]
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hint : Integrable (Function.uncurry fun (x y : Euc d) => E x • (((cz x * h (x + y) : ℝ) : ℂ)))
      (volume.prod μ) := by
    have hbd : Integrable (fun p : Euc d × Euc d => B * ‖cz p.1‖) (volume.prod μ) :=
      (((hc.integrable_of_hasCompactSupport hcs).norm).const_mul B).comp_fst μ
    refine Integrable.mono' hbd ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine Measurable.aestronglyMeasurable ?_
      exact (hEc.comp continuous_fst).measurable.smul (Complex.measurable_ofReal.comp
        ((hc.measurable.comp measurable_fst).mul (hm.comp (measurable_fst.add measurable_snd))))
    · have h1 := hB (p.1 + p.2)
      show ‖E p.1 • (((cz p.1 * h (p.1 + p.2) : ℝ) : ℂ))‖ ≤ B * ‖cz p.1‖
      calc ‖E p.1 • (((cz p.1 * h (p.1 + p.2) : ℝ) : ℂ))‖ = |cz p.1| * |h (p.1 + p.2)| := by
            rw [norm_smul, hEn, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        _ ≤ B * ‖cz p.1‖ := by
            rw [Real.norm_eq_abs]; nlinarith [abs_nonneg (cz p.1)]
  refine (integral_congr_ae (Filter.Eventually.of_forall step1)).trans ?_
  exact integral_integral_swap hint


/-- **UL-0 `ulocNormE_avg_le`**: averaging over translates does not increase `ulocNormE`
(`μ` a probability measure, `h` bounded measurable). -/
theorem ulocNormE_avg_le (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] (h : Euc d → ℝ) (hm : Measurable h) (B : ℝ) (hB : ∀ x, |h x| ≤ B) :
    ulocNormE m χ (fun x => ∫ y, h (x + y) ∂μ) ≤ ulocNormE m χ h := by
  refine iSup_le fun z => ?_
  set U : ℝ≥0∞ := ulocNormE m χ h with hU
  set cz : Euc d → ℝ := fun x => χ (x - z) with hcz
  have hcc : Continuous cz := hχ.1.continuous.comp (continuous_id.sub continuous_const)
  have hcs : HasCompactSupport cz := hχ.2.1.comp_homeomorph (Homeomorph.subRight z)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set a : Euc d → ℝ := fun x => ∫ y, h (x + y) ∂μ with ha
  have ha_meas : Measurable a :=
    (StronglyMeasurable.integral_prod_right (f := fun (x y : Euc d) => h (x + y)) (ν := μ)
      (hm.comp (measurable_fst.add measurable_snd)).stronglyMeasurable).measurable
  have haB : ∀ x, |a x| ≤ B := fun x => by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun y => h (x + y)) (C := B)
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hB (x + y))
    simpa [ha, Real.norm_eq_abs] using this
  obtain ⟨hgL2, hgL1⟩ := ul0_memLp_integrable_mul hcc hcs ha_meas.aestronglyMeasurable B haB
  have hφ : ∀ y, MemLp (fun x => cz x * h (x + y)) 2 volume ∧ Integrable (fun x => cz x * h (x + y)) volume :=
    fun y => ul0_memLp_integrable_mul hcc hcs (hm.comp (measurable_id.add_const y)).aestronglyMeasurable B
      (fun x => hB _)
  set Φ : Euc d → Euc d → ℂ := fun ξ y => 𝓕 (fun x : Euc d => (((cz x * h (x + y) : ℝ)) : ℂ)) ξ with hΦ
  -- joint measurability of `Φ`
  have hΦm : Measurable (fun p : Euc d × Euc d => Φ p.1 p.2) := by
    have : (fun p : Euc d × Euc d => Φ p.1 p.2) = fun p => ∫ x : Euc d,
        Complex.exp ((↑(-2 * Real.pi * ⟪x, p.1⟫) * Complex.I)) • (((cz x * h (x + p.2) : ℝ)) : ℂ) := by
      funext p; simp only [hΦ, Real.fourier_eq']
    rw [this]
    refine StronglyMeasurable.measurable ?_
    refine StronglyMeasurable.integral_prod_right (f := fun (p : Euc d × Euc d) (x : Euc d) =>
      Complex.exp ((↑(-2 * Real.pi * ⟪x, p.1⟫) * Complex.I)) • (((cz x * h (x + p.2) : ℝ)) : ℂ)) ?_
    refine Measurable.stronglyMeasurable ?_
    have h1 : Continuous (fun q : (Euc d × Euc d) × Euc d =>
        Complex.exp ((↑(-2 * Real.pi * ⟪q.2, q.1.1⟫) * Complex.I))) := by fun_prop
    exact h1.measurable.smul (Complex.measurable_ofReal.comp
      ((hcc.measurable.comp measurable_snd).mul (hm.comp (measurable_snd.add (measurable_snd.comp measurable_fst)))))
  have hΦe : Measurable (fun p : Euc d × Euc d => ‖Φ p.1 p.2‖ₑ) := hΦm.enorm
  -- Claim 2: Cauchy-Schwarz
  have hCS : ∀ ξ : Euc d, ‖𝓕 (fun x : Euc d => (((cz x * a x : ℝ)) : ℂ)) ξ‖ₑ ^ 2 ≤
      ∫⁻ y, ‖Φ ξ y‖ₑ ^ 2 ∂μ := by
    intro ξ
    rw [ul0_fourier_avg cz hcc hcs h hm B hB μ ξ]
    have h1 := enorm_integral_le_lintegral_enorm (μ := μ) (fun y => Φ ξ y)
    have hmeas : Measurable (fun y => ‖Φ ξ y‖ₑ) :=
      (hΦe.comp (measurable_prodMk_left (x := ξ)) : Measurable ((fun p : Euc d × Euc d => ‖Φ p.1 p.2‖ₑ) ∘ Prod.mk ξ))
    have h2 := HRS.MS.SobMul.sobmul_cs μ (fun y => ‖Φ ξ y‖ₑ) hmeas.aemeasurable
    simp only [measure_univ, one_mul] at h2
    exact (pow_le_pow_left' h1 2).trans h2
  -- Claim 3 and 4: each piece
  have hpiece : ∀ y, ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ (m : ℝ)) * ‖Φ ξ y‖ₑ ^ 2 =
      sobolevNormE (m : ℝ) (fun x => cz x * h (x + y)) ^ 2 := by
    intro y
    rw [um_sobE_sq (hφ y).1]
    refine lintegral_congr_ae ?_
    filter_upwards [um_L1L2 (hφ y).2 (hφ y).1] with ξ hξ
    rw [hξ, ENNReal.ofReal_mul (Real.rpow_nonneg (wt_pos ξ).le _), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm_eq_enorm]
  have hbound : ∀ y, sobolevNormE (m : ℝ) (fun x => cz x * h (x + y)) ≤ U := by
    intro y
    have e : (fun x => cz x * h (x + y)) = fun x => (fun t => χ (t - (z + y)) * h t) (x + y) := by
      funext x; simp only [hcz]; congr 2; abel
    rw [e]
    have := HRS.MS.SobMul.sobolevNormE_translate (m : ℝ) (fun t => χ (t - (z + y)) * h t) (-y)
    simp only [sub_neg_eq_add] at this
    rw [this]
    exact le_iSup (fun z : Euc d => sobolevNormE (m : ℝ) fun x => χ (x - z) * h x) (z + y)
  -- assemble
  have hmeasW : Measurable (fun p : Euc d × Euc d => ENNReal.ofReal (wt p.1 ^ (m : ℝ)) * ‖Φ p.1 p.2‖ₑ ^ 2) :=
    (ENNReal.measurable_ofReal.comp ((continuous_wt_rpow (m : ℝ)).measurable.comp measurable_fst)).mul
      (hΦe.pow_const 2)
  have hga : (fun x => χ (x - z) * a x) = fun x => cz x * a x := rfl
  rw [hga]
  have hmain : sobolevNormE (m : ℝ) (fun x => cz x * a x) ^ 2 ≤ U ^ 2 := by
    rw [um_sobE_sq hgL2]
    calc ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ (m : ℝ) * ‖fourierL2 (fun x => cz x * a x) ξ‖ ^ 2)
        = ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ (m : ℝ)) * ‖𝓕 (fun x : Euc d => (((cz x * a x : ℝ)) : ℂ)) ξ‖ₑ ^ 2 := by
          refine lintegral_congr_ae ?_
          filter_upwards [um_L1L2 hgL1 hgL2] with ξ hξ
          rw [hξ, ENNReal.ofReal_mul (Real.rpow_nonneg (wt_pos ξ).le _),
            ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
      _ ≤ ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ (m : ℝ)) * ∫⁻ y, ‖Φ ξ y‖ₑ ^ 2 ∂μ := by
          refine lintegral_mono fun ξ => ?_
          gcongr
          exact hCS ξ
      _ = ∫⁻ ξ, ∫⁻ y, ENNReal.ofReal (wt ξ ^ (m : ℝ)) * ‖Φ ξ y‖ₑ ^ 2 ∂μ := by
          refine lintegral_congr fun ξ => ?_
          rw [lintegral_const_mul]
          exact (hΦe.comp (measurable_prodMk_left (x := ξ))).pow_const 2
      _ = ∫⁻ y, ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ (m : ℝ)) * ‖Φ ξ y‖ₑ ^ 2 ∂volume ∂μ :=
          lintegral_lintegral_swap hmeasW.aemeasurable
      _ = ∫⁻ y, sobolevNormE (m : ℝ) (fun x => cz x * h (x + y)) ^ 2 ∂μ :=
          lintegral_congr fun y => hpiece y
      _ ≤ ∫⁻ y, U ^ 2 ∂μ := lintegral_mono fun y => pow_le_pow_left' (hbound y) 2
      _ = U ^ 2 := by simp
  exact (ENNReal.pow_le_pow_left_iff (n := 2) two_ne_zero).1 hmain


/-! ### Linear change of variables -/

theorem ul0_integral_comp_equiv (T : Euc d ≃ₗ[ℝ] Euc d) (G : Euc d → ℂ) :
    ∫ x, G (T x) = (|(LinearMap.det (T : Euc d →ₗ[ℝ] Euc d))|⁻¹ : ℝ) • ∫ w, G w := by
  have hme : MeasurableEmbedding T := T.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have hdet : LinearMap.det (T : Euc d →ₗ[ℝ] Euc d) ≠ 0 := (LinearEquiv.isUnit_det' T).ne_zero
  rw [← hme.integral_map G]
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Euc d))
    (f := (T : Euc d →ₗ[ℝ] Euc d)) hdet
  have e1 : Measure.map T (volume : Measure (Euc d)) = ENNReal.ofReal |(LinearMap.det (T : Euc d →ₗ[ℝ] Euc d))⁻¹| •
      (volume : Measure (Euc d)) := this
  rw [e1, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]

theorem ul0_lintegral_comp_equiv (T : Euc d ≃ₗ[ℝ] Euc d) (Ψ : Euc d → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ x, Ψ (T x) = ENNReal.ofReal |(LinearMap.det (T : Euc d →ₗ[ℝ] Euc d))⁻¹| * ∫⁻ w, Ψ w := by
  have hdet : LinearMap.det (T : Euc d →ₗ[ℝ] Euc d) ≠ 0 := (LinearEquiv.isUnit_det' T).ne_zero
  have hTm : Measurable (fun x => T x) := (LinearMap.continuous_of_finiteDimensional (T : Euc d →ₗ[ℝ] Euc d)).measurable
  rw [← lintegral_map hΨ hTm]
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Euc d))
    (f := (T : Euc d →ₗ[ℝ] Euc d)) hdet
  have e1 : Measure.map T (volume : Measure (Euc d)) = ENNReal.ofReal |(LinearMap.det (T : Euc d →ₗ[ℝ] Euc d))⁻¹| •
      (volume : Measure (Euc d)) := this
  rw [e1, lintegral_smul_measure, smul_eq_mul]

theorem ul0_fourier_comp_equiv (e : Euc d ≃ₗ[ℝ] Euc d) (F : Euc d → ℂ) (ξ : Euc d) :
    𝓕 (fun x => F (e x)) ξ = (|(LinearMap.det (e : Euc d →ₗ[ℝ] Euc d))|⁻¹ : ℝ) •
      𝓕 F ((LinearMap.adjoint (e.symm : Euc d →ₗ[ℝ] Euc d)) ξ) := by
  simp only [Real.fourier_eq']
  rw [← ul0_integral_comp_equiv e (fun w => Complex.exp ((↑(-2 * Real.pi *
    ⟪w, (LinearMap.adjoint (e.symm : Euc d →ₗ[ℝ] Euc d)) ξ⟫) * Complex.I)) • F w)]
  congr 1
  funext x
  have h1 : ⟪e x, (LinearMap.adjoint (e.symm : Euc d →ₗ[ℝ] Euc d)) ξ⟫ = ⟪x, ξ⟫ := by
    rw [LinearMap.adjoint_inner_right]
    simp
  rw [h1]


/-- composition with a linear equivalence is bounded on `H^m` (for `L¹ ∩ L²` functions) -/
theorem ul0_sobE_comp_equiv (m : ℕ) (e : Euc d ≃ₗ[ℝ] Euc d) :
    ∃ K : ℝ, 0 < K ∧ ∀ v : Euc d → ℝ, MemLp v 2 volume → Integrable v volume →
      sobolevNormE (m : ℝ) (fun x => v (e x)) ≤ ENNReal.ofReal K * sobolevNormE (m : ℝ) v := by
  classical
  set T0 : Euc d →ₗ[ℝ] Euc d := LinearMap.adjoint (e.symm : Euc d →ₗ[ℝ] Euc d) with hT0
  set S0 : Euc d →ₗ[ℝ] Euc d := LinearMap.adjoint (e : Euc d →ₗ[ℝ] Euc d) with hS0
  have hST : ∀ ξ, S0 (T0 ξ) = ξ := by
    intro ξ
    apply ext_inner_left ℝ
    intro w
    rw [hS0, LinearMap.adjoint_inner_right, hT0, LinearMap.adjoint_inner_right]
    simp
  have hTS : ∀ ξ, T0 (S0 ξ) = ξ := by
    intro ξ
    apply ext_inner_left ℝ
    intro w
    rw [hT0, LinearMap.adjoint_inner_right, hS0, LinearMap.adjoint_inner_right]
    simp
  set T' : Euc d ≃ₗ[ℝ] Euc d := LinearEquiv.ofLinear T0 S0 (LinearMap.ext hTS) (LinearMap.ext hST) with hT'
  have hdete : LinearMap.det (e : Euc d →ₗ[ℝ] Euc d) ≠ 0 := (LinearEquiv.isUnit_det' e).ne_zero
  have hdetT : LinearMap.det (T' : Euc d →ₗ[ℝ] Euc d) ≠ 0 := (LinearEquiv.isUnit_det' T').ne_zero
  set c1 : ℝ := |LinearMap.det (e : Euc d →ₗ[ℝ] Euc d)|⁻¹ with hc1
  set c2 : ℝ := |(LinearMap.det (T' : Euc d →ₗ[ℝ] Euc d))⁻¹| with hc2
  have hc1pos : 0 < c1 := inv_pos.2 (abs_pos.2 hdete)
  have hc2pos : 0 < c2 := abs_pos.2 (inv_ne_zero hdetT)
  set Sc : Euc d →L[ℝ] Euc d := LinearMap.toContinuousLinearMap S0 with hSc
  set Kw : ℝ := 1 + ‖Sc‖ ^ 2 with hKw
  have hKw1 : 1 ≤ Kw := by rw [hKw]; nlinarith [sq_nonneg ‖Sc‖]
  have hwtle : ∀ ξ : Euc d, wt ξ ≤ Kw * wt (T0 ξ) := by
    intro ξ
    have h1 : ‖ξ‖ ≤ ‖Sc‖ * ‖T0 ξ‖ := by
      have := Sc.le_opNorm (T0 ξ)
      rw [show Sc (T0 ξ) = ξ from hST ξ] at this
      exact this
    unfold wt
    have h2 : ‖ξ‖ ^ 2 ≤ ‖Sc‖ ^ 2 * ‖T0 ξ‖ ^ 2 := by
      calc ‖ξ‖ ^ 2 ≤ (‖Sc‖ * ‖T0 ξ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = _ := by ring
    have h3 : 0 ≤ ‖Sc‖ ^ 2 * (4 * Real.pi ^ 2 * ‖T0 ξ‖ ^ 2) := by positivity
    rw [hKw]
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * Real.pi ^ 2)]
  refine ⟨Real.sqrt (c1 ^ 2 * Kw ^ m * c2), Real.sqrt_pos.2 (by positivity), fun v hv2 hv1 => ?_⟩
  -- the composed function
  have hdet' : LinearMap.det (e : Euc d →ₗ[ℝ] Euc d) ≠ 0 := hdete
  have hmap : Measure.map e (volume : Measure (Euc d)) = ENNReal.ofReal |(LinearMap.det (e : Euc d →ₗ[ℝ] Euc d))⁻¹| •
      (volume : Measure (Euc d)) :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Euc d)) (f := (e : Euc d →ₗ[ℝ] Euc d)) hdet'
  have heme : Measurable (fun x => e x) := (LinearMap.continuous_of_finiteDimensional (e : Euc d →ₗ[ℝ] Euc d)).measurable
  have hve2 : MemLp (fun x => v (e x)) 2 volume := by
    have h1 : MemLp v 2 (Measure.map e (volume : Measure (Euc d))) := by
      rw [hmap]; exact hv2.smul_measure ENNReal.ofReal_ne_top
    exact (memLp_map_measure_iff (by rw [hmap]; exact hv2.aestronglyMeasurable.smul_measure _) heme.aemeasurable).1 h1
  have hve1 : Integrable (fun x => v (e x)) volume := by
    have h1 : Integrable v (Measure.map e (volume : Measure (Euc d))) := by
      rw [hmap]; exact hv1.smul_measure ENNReal.ofReal_ne_top
    exact (integrable_map_measure (by rw [hmap]; exact hv1.aestronglyMeasurable.smul_measure _) heme.aemeasurable).1 h1
  set Fv : Euc d → ℂ := fun w => ((v w : ℝ) : ℂ) with hFv
  have hFc : Continuous (𝓕 Fv) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).continuous₂ hv1.ofReal
  set Ψ : Euc d → ℝ≥0∞ := fun η => ENNReal.ofReal (wt η ^ (m : ℝ) * ‖𝓕 Fv η‖ ^ 2) with hΨ
  have hΨm : Measurable Ψ :=
    ENNReal.measurable_ofReal.comp (((continuous_wt_rpow (m : ℝ)).mul (hFc.norm.pow 2)).measurable)
  have hΨint : ∫⁻ η, Ψ η = sobolevNormE (m : ℝ) v ^ 2 := by
    rw [um_sobE_sq hv2]
    refine lintegral_congr_ae ?_
    filter_upwards [um_L1L2 hv1 hv2] with η hη
    simp only [hΨ, hη, hFv]
  have hlhs : sobolevNormE (m : ℝ) (fun x => v (e x)) ^ 2 =
      ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ (m : ℝ) * ‖c1 • 𝓕 Fv (T0 ξ)‖ ^ 2) := by
    rw [um_sobE_sq hve2]
    refine lintegral_congr_ae ?_
    filter_upwards [um_L1L2 hve1 hve2] with ξ hξ
    rw [hξ]
    congr 3
    exact congrArg norm (ul0_fourier_comp_equiv e Fv ξ)
  have hpt : ∀ ξ, ENNReal.ofReal (wt ξ ^ (m : ℝ) * ‖c1 • 𝓕 Fv (T0 ξ)‖ ^ 2) ≤
      ENNReal.ofReal (c1 ^ 2 * Kw ^ m) * Ψ (T' ξ) := by
    intro ξ
    have hT'ξ : T' ξ = T0 ξ := rfl
    rw [hT'ξ, hΨ]
    simp only
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc1pos]
    have h1 : wt ξ ^ (m : ℝ) ≤ Kw ^ m * wt (T0 ξ) ^ (m : ℝ) := by
      rw [Real.rpow_natCast, Real.rpow_natCast, ← mul_pow]
      exact pow_le_pow_left₀ (wt_pos ξ).le (hwtle ξ) m
    have h2 : 0 ≤ ‖𝓕 Fv (T0 ξ)‖ ^ 2 := sq_nonneg _
    calc wt ξ ^ (m : ℝ) * (c1 * ‖𝓕 Fv (T0 ξ)‖) ^ 2
        = c1 ^ 2 * (wt ξ ^ (m : ℝ) * ‖𝓕 Fv (T0 ξ)‖ ^ 2) := by ring
      _ ≤ c1 ^ 2 * ((Kw ^ m * wt (T0 ξ) ^ (m : ℝ)) * ‖𝓕 Fv (T0 ξ)‖ ^ 2) := by gcongr
      _ = _ := by ring
  have hmain : sobolevNormE (m : ℝ) (fun x => v (e x)) ^ 2 ≤
      ENNReal.ofReal (Real.sqrt (c1 ^ 2 * Kw ^ m * c2)) ^ 2 * sobolevNormE (m : ℝ) v ^ 2 := by
    rw [hlhs]
    calc ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ (m : ℝ) * ‖c1 • 𝓕 Fv (T0 ξ)‖ ^ 2)
        ≤ ∫⁻ ξ, ENNReal.ofReal (c1 ^ 2 * Kw ^ m) * Ψ (T' ξ) := lintegral_mono hpt
      _ = ENNReal.ofReal (c1 ^ 2 * Kw ^ m) * ∫⁻ ξ, Ψ (T' ξ) := by
          have hΨT : Measurable (fun ξ => Ψ (T' ξ)) := hΨm.comp T'.toContinuousLinearEquiv.continuous.measurable
          rw [lintegral_const_mul _ hΨT]
      _ = ENNReal.ofReal (c1 ^ 2 * Kw ^ m) * (ENNReal.ofReal c2 * ∫⁻ η, Ψ η) := by
          rw [ul0_lintegral_comp_equiv T' Ψ hΨm]
      _ = ENNReal.ofReal (Real.sqrt (c1 ^ 2 * Kw ^ m * c2)) ^ 2 * sobolevNormE (m : ℝ) v ^ 2 := by
          rw [hΨint, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity),
            ENNReal.ofReal_mul (p := c1 ^ 2 * Kw ^ m) (q := c2) (by positivity), mul_assoc]
  rw [← mul_pow] at hmain
  exact (ENNReal.pow_le_pow_left_iff (n := 2) two_ne_zero).1 hmain


theorem ul0_integrable_of_support (v : Euc d → ℝ) (hv : MemLp v 2 volume) (R : ℝ)
    (hs : ∀ w : Euc d, R < ‖w‖ → v w = 0) : Integrable v volume := by
  have hfin : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Euc d) R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
  have h1 : IntegrableOn v (Metric.closedBall (0 : Euc d) R) volume :=
    (hv.restrict (Metric.closedBall (0 : Euc d) R)).integrable (by norm_num)
  refine (integrableOn_iff_integrable_of_support_subset (s := Metric.closedBall (0 : Euc d) R) ?_).1 h1
  intro w hw
  by_contra hn
  exact hw (hs w (not_le.1 (by simpa using hn)))

theorem ul0_exists_equiv_of_matrix (A : Matrix (Fin d) (Fin d) ℝ) (hA : IsUnit A.det) :
    ∃ e : Euc d ≃ₗ[ℝ] Euc d, ∀ x, e x = HRS.Torus.matVec A x := by
  refine ⟨LinearEquiv.ofLinear (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin A⁻¹) ?_ ?_, fun x => rfl⟩
  · have h1 := Matrix.toLpLin_mul_same (p := (2 : ℝ≥0∞)) (R := ℝ) A A⁻¹
    rw [Matrix.mul_nonsing_inv A hA, Matrix.toLpLin_one 2] at h1
    exact h1.symm
  · have h1 := Matrix.toLpLin_mul_same (p := (2 : ℝ≥0∞)) (R := ℝ) A⁻¹ A
    rw [Matrix.nonsing_inv_mul A hA, Matrix.toLpLin_one 2] at h1
    exact h1.symm

/-- **UL-0 `ulocNormE_comp_linear`**: pullback by an invertible matrix is bounded on `H^m_uloc`. -/
theorem ulocNormE_comp_linear (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : IsUnit A.det) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : Euc d → ℝ,
      ulocNormE m χ (fun x => h (HRS.Torus.matVec A x)) ≤ ENNReal.ofReal C * ulocNormE m χ h := by
  obtain ⟨e, he⟩ := ul0_exists_equiv_of_matrix A hA
  obtain ⟨K, hK, hcomp⟩ := ul0_sobE_comp_equiv m e
  set ec : Euc d →L[ℝ] Euc d := LinearMap.toContinuousLinearMap (e : Euc d →ₗ[ℝ] Euc d) with hec
  set es : Euc d →L[ℝ] Euc d := LinearMap.toContinuousLinearMap (e.symm : Euc d →ₗ[ℝ] Euc d) with hes
  set χe : Euc d → ℝ := fun w => χ (e.symm w) with hχe
  have hχes : ContDiff ℝ ∞ χe := hχ.1.comp es.contDiff
  have hχec : HasCompactSupport χe :=
    hχ.2.1.comp_homeomorph (e.symm.toContinuousLinearEquiv.toHomeomorph)
  set R0 : ℝ := ‖ec‖ * 2 + 1 with hR0
  have hR0pos : 0 < R0 := by positivity
  have hsup : ∀ p : Euc d, χe p ≠ 0 → ‖p‖ ≤ R0 := by
    intro p hp
    have h1 : e.symm p ∈ tsupport χ := subset_tsupport _ hp
    have h2 : ‖e.symm p‖ < 2 := by simpa using hχ.2.2.1 h1
    have h3 : ‖p‖ ≤ ‖ec‖ * ‖e.symm p‖ := by
      have := ec.le_opNorm (e.symm p)
      rw [show ec (e.symm p) = p by simp [hec]] at this
      exact this
    have h4 : 0 ≤ ‖ec‖ := norm_nonneg _
    nlinarith
  obtain ⟨Y, hY⟩ := HRS.MS.UlocCut.uc_cover (fun y : Euc d => y)
    (fun p => ⟨p, by simpa using one_pos⟩) R0
  obtain ⟨C, hC, hkey⟩ := ul0_key m χe χ hχes hχec hχ.1 hχ.2.1 Y R0 0 R0 hR0pos (by linarith) hsup
    (fun p hp => by
      obtain ⟨y, hy, hpy⟩ := hY p hp
      exact ⟨y, hy, hχ.2.2.2.2 _ (by simpa using hpy.le)⟩)
  refine ⟨K * (C * Y.card) + 1, by positivity, fun h => ?_⟩
  refine iSup_le fun z0 => ?_
  set U : ℝ≥0∞ := ulocNormE m χ h with hU
  set v : Euc d → ℝ := fun w => χe (w - e z0) * h w with hv
  have hfun : (fun x => χ (x - z0) * (fun x => h (HRS.Torus.matVec A x)) x) = fun x => v (e x) := by
    funext x
    show χ (x - z0) * h (HRS.Torus.matVec A x) = χ (e.symm (e x - e z0)) * h (e x)
    rw [← map_sub, LinearEquiv.symm_apply_apply, he x]
  rw [hfun]
  by_cases hvS : HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) v
  swap
  · have : sobolevNormE (m : ℝ) v = ⊤ := by unfold sobolevNormE; rw [if_neg hvS]
    have h2 : ENNReal.ofReal K * sobolevNormE (m : ℝ) v = ⊤ := by
      rw [this, ENNReal.mul_top (by simp; exact hK)]
    -- then the bound `ofReal K * ‖v‖ ≤ ...` would force `U = ⊤`; handle by cases on `U`
    by_cases hUtop : U = ⊤
    · rw [hUtop, ENNReal.mul_top (by simp; positivity)]; exact le_top
    · exfalso
      have hbd := hkey (e z0) (e z0) (by simp) h
      have hsum : ∑ y ∈ Y, sobolevNormE (m : ℝ) (fun x => χ (x - (e z0 + y)) * h x) ≤ Y.card • U :=
        Finset.sum_le_card_nsmul _ _ _ fun y _ => le_iSup (fun z : Euc d =>
          sobolevNormE (m : ℝ) fun x => χ (x - z) * h x) (e z0 + y)
      have hv_le : sobolevNormE (m : ℝ) v ≤ ENNReal.ofReal C * (Y.card • U) :=
        hbd.trans (by gcongr)
      have hlt : ENNReal.ofReal C * (Y.card • U) < ⊤ :=
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by
          rw [nsmul_eq_mul]; exact ENNReal.mul_lt_top (by simp) (lt_top_iff_ne_top.2 hUtop))
      exact (lt_top_iff_ne_top.1 (lt_of_le_of_lt hv_le hlt)) this
  · have hv1 : Integrable v volume := by
      refine ul0_integrable_of_support v hvS.1 (R0 + ‖e z0‖) fun w hw => ?_
      by_contra hne
      have : χe (w - e z0) ≠ 0 := fun h0 => hne (by simp [hv, h0])
      have := hsup _ this
      have h5 : ‖w‖ ≤ ‖w - e z0‖ + ‖e z0‖ := by simpa using norm_add_le (w - e z0) (e z0)
      linarith
    refine (hcomp v hvS.1 hv1).trans ?_
    have hbd := hkey (e z0) (e z0) (by simp) h
    have hsum : ∑ y ∈ Y, sobolevNormE (m : ℝ) (fun x => χ (x - (e z0 + y)) * h x) ≤ Y.card • U :=
      Finset.sum_le_card_nsmul _ _ _ fun y _ => le_iSup (fun z : Euc d =>
        sobolevNormE (m : ℝ) fun x => χ (x - z) * h x) (e z0 + y)
    calc ENNReal.ofReal K * sobolevNormE (m : ℝ) v
        ≤ ENNReal.ofReal K * (ENNReal.ofReal C * (Y.card • U)) := by
          gcongr
          exact hbd.trans (by gcongr)
      _ = ENNReal.ofReal (K * (C * Y.card)) * U := by
          rw [nsmul_eq_mul, ENNReal.ofReal_mul hK.le, ENNReal.ofReal_mul hC.le,
            ENNReal.ofReal_natCast]
          ring
      _ ≤ ENNReal.ofReal (K * (C * Y.card) + 1) * U := by
          gcongr
          linarith

end HRS.MS.Ul
