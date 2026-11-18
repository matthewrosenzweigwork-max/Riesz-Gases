import HRS.Commutator.Whole.Defs

/-!
# CMX-FC auxiliary: the Fourier cutoff kernel `ψ_L`

Helper lemmas for `chi_psi_props` (all names prefixed `cmxFB_`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

/-- The rescaled cutoff `ξ ↦ χ(ξ/L)` as a complex function. -/
def cmxFB_gL (d : ℕ) (L : ℝ) (ξ : Euc d) : ℂ := ((chi (L⁻¹ • ξ) : ℝ) : ℂ)

theorem cmxFB_chi_contDiff : ContDiff ℝ ∞ (chi : Euc d → ℝ) := (chiBump d).contDiff

theorem cmxFB_chi_neg (ξ : Euc d) : chi (-ξ) = chi ξ := (chiBump d).neg ξ

theorem cmxFB_chi_zero {ξ : Euc d} (h : 2 ≤ ‖ξ‖) : chi ξ = 0 := by
  apply (chiBump d).zero_of_le_dist
  simpa [chiBump, dist_zero_right] using h

theorem cmxFB_chi_one {ξ : Euc d} (h : ‖ξ‖ ≤ 1) : chi ξ = 1 := by
  apply (chiBump d).one_of_mem_closedBall
  simpa [chiBump] using h

theorem cmxFB_chi_nonneg (ξ : Euc d) : 0 ≤ chi ξ := (chiBump d).nonneg

theorem cmxFB_chi_le_one (ξ : Euc d) : chi ξ ≤ 1 := (chiBump d).le_one

theorem cmxFB_gL_contDiff (L : ℝ) : ContDiff ℝ ∞ (cmxFB_gL d L) := by
  unfold cmxFB_gL
  exact Complex.ofRealCLM.contDiff.comp (cmxFB_chi_contDiff.comp (contDiff_const_smul _))

theorem cmxFB_gL_compact {L : ℝ} (hL : 0 < L) : HasCompactSupport (cmxFB_gL d L) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) (2 * L)) fun ξ hξ => ?_
  have h1 : 2 * L < ‖ξ‖ := by simpa using hξ
  have h2 : 2 ≤ ‖L⁻¹ • ξ‖ := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hL.le, inv_mul_eq_div, le_div_iff₀ hL]
    linarith
  simp [cmxFB_gL, cmxFB_chi_zero h2]

/-- `ξ ↦ χ(ξ/L)` as a Schwartz function. -/
def cmxFB_G (L : ℝ) (hL : 0 < L) : SchwartzMap (Euc d) ℂ :=
  (cmxFB_gL_compact (d := d) hL).toSchwartzMap (cmxFB_gL_contDiff L)

theorem cmxFB_G_apply {L : ℝ} (hL : 0 < L) (ξ : Euc d) : cmxFB_G (d := d) L hL ξ = cmxFB_gL d L ξ :=
  rfl

theorem cmxFB_gL_neg (L : ℝ) (ξ : Euc d) : cmxFB_gL d L (-ξ) = cmxFB_gL d L ξ := by
  unfold cmxFB_gL
  rw [smul_neg, cmxFB_chi_neg]

theorem cmxFB_gL_conj (L : ℝ) (ξ : Euc d) :
    (starRingEnd ℂ) (cmxFB_gL d L ξ) = cmxFB_gL d L ξ := by
  simp [cmxFB_gL]

theorem cmxFB_finv_conj (L : ℝ) (x : Euc d) :
    (starRingEnd ℂ) (𝓕⁻ (cmxFB_gL d L) x) = 𝓕⁻ (cmxFB_gL d L) x := by
  rw [Real.fourierInv_eq', ← integral_conj]
  have h : ∀ v : Euc d, (starRingEnd ℂ) (Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) •
      cmxFB_gL d L v) =
      (fun w : Euc d => Complex.exp (↑(2 * Real.pi * inner ℝ (-w) x) * Complex.I) •
        cmxFB_gL d L (-w)) v := by
    intro v
    simp only [smul_eq_mul, map_mul, cmxFB_gL_conj, cmxFB_gL_neg, inner_neg_left]
    congr 1
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  simp_rw [h]
  exact integral_neg_eq_self (fun w : Euc d => Complex.exp (↑(2 * Real.pi * inner ℝ w x) * Complex.I) • cmxFB_gL d L w) volume

theorem cmxFB_finv_eq (L : ℝ) (x : Euc d) :
    𝓕⁻ (cmxFB_gL d L) x = ((psiL L x : ℝ) : ℂ) := by
  have h := cmxFB_finv_conj L x
  have him : (𝓕⁻ (cmxFB_gL d L) x).im = 0 := by
    have := congrArg Complex.im h
    simp at this
    linarith
  apply Complex.ext
  · rfl
  · simpa using him

/-- `ψ_L` as a Schwartz function: `𝓕⁻` of the Schwartz cutoff. -/
def cmxFB_Om (L : ℝ) (hL : 0 < L) : SchwartzMap (Euc d) ℂ := 𝓕⁻ (cmxFB_G (d := d) L hL)

theorem cmxFB_Om_apply {L : ℝ} (hL : 0 < L) (x : Euc d) :
    cmxFB_Om (d := d) L hL x = ((psiL L x : ℝ) : ℂ) := by
  unfold cmxFB_Om
  rw [SchwartzMap.fourierInv_coe]
  exact cmxFB_finv_eq L x

theorem cmxFB_fourier_Om {L : ℝ} (hL : 0 < L) :
    𝓕 (cmxFB_Om (d := d) L hL) = cmxFB_G (d := d) L hL := by
  unfold cmxFB_Om
  exact FourierTransform.fourier_fourierInv_eq _

theorem cmxFB_psiL_neg (L : ℝ) (x : Euc d) : psiL L (-x) = psiL L x := by
  have h1 : 𝓕⁻ (cmxFB_gL d L) (-x) = 𝓕⁻ (cmxFB_gL d L) x := by
    rw [Real.fourierInv_eq', Real.fourierInv_eq']
    have := integral_neg_eq_self (fun w : Euc d =>
      Complex.exp (↑(2 * Real.pi * inner ℝ w x) * Complex.I) • cmxFB_gL d L w) volume
    rw [← this]
    congr 1
    ext w
    simp only [cmxFB_gL_neg, inner_neg_left, inner_neg_right, smul_eq_mul]
  have := congrArg Complex.re ((cmxFB_finv_eq L (-x)).symm.trans (h1.trans (cmxFB_finv_eq L x)))
  simpa using this

theorem cmxFB_integral_psiL {L : ℝ} (hL : 0 < L) : ∫ x : Euc d, psiL L x = 1 := by
  have h1 : 𝓕 (cmxFB_Om (d := d) L hL) 0 = ∫ x : Euc d, cmxFB_Om (d := d) L hL x := by
    rw [SchwartzMap.fourier_coe, Real.fourier_eq]
    simp
  rw [cmxFB_fourier_Om] at h1
  have h2 : cmxFB_G (d := d) L hL 0 = 1 := by
    rw [cmxFB_G_apply]
    simp [cmxFB_gL, cmxFB_chi_one (d := d) (ξ := 0) (by simp)]
  rw [h2] at h1
  simp_rw [cmxFB_Om_apply] at h1
  rw [integral_complex_ofReal] at h1
  exact_mod_cast h1.symm

/-! ### Band-limited functions: `P_{≤L}f` has Fourier support in `B̄(0,2L)` -/

/-- Schwartz functions with a vanishing Fourier transform on `B̄(0,2L)` are annihilated by `ψ_L`-convolution. -/
theorem cmxFB_conv_zero {L : ℝ} (hL : 0 < L) (φ : SchwartzMap (Euc d) ℂ)
    (hφ : ∀ ξ : Euc d, ‖ξ‖ ≤ 2 * L → 𝓕 (⇑φ) ξ = 0) (y : Euc d) :
    ∫ x, φ x * cmxFB_Om (d := d) L hL (y - x) = 0 := by
  have hB := SchwartzMap.convolution_apply (ContinuousLinearMap.mul ℂ ℂ) φ (cmxFB_Om (d := d) L hL) y
  have hF : 𝓕 (SchwartzMap.convolution (𝕜 := ℂ) (ContinuousLinearMap.mul ℂ ℂ) φ
      (cmxFB_Om (d := d) L hL)) = 0 := by
    rw [SchwartzMap.fourier_convolution, cmxFB_fourier_Om]
    ext ξ
    simp only [SchwartzMap.pairing_apply_apply, ContinuousLinearMap.mul_apply']
    by_cases hξ : ‖ξ‖ ≤ 2 * L
    · have := hφ ξ hξ
      have h3 : (𝓕 φ) ξ = 0 := by
        rw [SchwartzMap.fourier_coe]
        exact this
      simp [h3]
    · have h2 : 2 ≤ ‖L⁻¹ • ξ‖ := by
        rw [norm_smul, norm_inv, Real.norm_of_nonneg hL.le, inv_mul_eq_div, le_div_iff₀ hL]
        linarith [not_le.1 hξ]
      simp [cmxFB_G_apply, cmxFB_gL, cmxFB_chi_zero h2]
  have h0 : SchwartzMap.convolution (𝕜 := ℂ) (ContinuousLinearMap.mul ℂ ℂ) φ
      (cmxFB_Om (d := d) L hL) = 0 := by
    set c := SchwartzMap.convolution (𝕜 := ℂ) (ContinuousLinearMap.mul ℂ ℂ) φ
      (cmxFB_Om (d := d) L hL) with hc
    have h1 : 𝓕⁻ (𝓕 c) = c := FourierTransform.fourierInv_fourier_eq _
    rw [hF] at h1
    rw [← h1]
    simp
  rw [h0] at hB
  simp only [zero_apply] at hB
  rw [MeasureTheory.convolution_def] at hB
  simpa using hB.symm

theorem cmxFB_decay (φ : SchwartzMap (Euc d) ℂ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Euc d, (1 + ‖x‖) ^ N * ‖φ x‖ ≤ C := by
  refine ⟨2 ^ N * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) φ,
    mul_nonneg (by positivity) (apply_nonneg _ _), fun x => ?_⟩
  have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0)) (k := N) (n := 0)
    le_rfl le_rfl φ x
  simpa using this

theorem cmxFB_integrable_inv_pow (k : ℕ) (hk : d < k) :
    Integrable (fun x : Euc d => ((1 + ‖x‖) ^ k)⁻¹) := by
  have h := integrable_one_add_norm (E := Euc d) (μ := volume) (r := (k : ℝ))
    (by simpa using (by exact_mod_cast hk : (d : ℝ) < k))
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

theorem cmxFB_integrable_pow_mul (φ : SchwartzMap (Euc d) ℂ) (k : ℕ) :
    Integrable (fun x : Euc d => (1 + ‖x‖) ^ k * ‖φ x‖) := by
  obtain ⟨C, hC0, hC⟩ := cmxFB_decay φ (k + (d + 1))
  refine ((cmxFB_integrable_inv_pow (d := d) (d + 1) (by omega)).const_mul C).mono' ?_ ?_
  · exact ((by fun_prop : Continuous fun x : Euc d => (1 + ‖x‖) ^ k).mul
      φ.continuous.norm).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    have hpos : 0 < (1 + ‖x‖) ^ (d + 1) := by positivity
    rw [Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv, le_div_iff₀ hpos]
    calc (1 + ‖x‖) ^ k * ‖φ x‖ * (1 + ‖x‖) ^ (d + 1)
        = (1 + ‖x‖) ^ (k + (d + 1)) * ‖φ x‖ := by ring
      _ ≤ C := hC x

/-- Integrability of `(x,y) ↦ Ψ(x-y) f(y) φ(x)` for `f` of linear growth. -/
theorem cmxFB_integrable_prod (Ψ φ : SchwartzMap (Euc d) ℂ) (f : Euc d → ℝ) (C : ℝ)
    (hf : ∀ x, |f x| ≤ C * (1 + ‖x‖)) (hm : Measurable f) :
    Integrable (fun p : Euc d × Euc d => Ψ (p.1 - p.2) * ((f p.2 : ℝ) : ℂ) * φ p.1)
      (volume.prod volume) := by
  obtain ⟨Cφ, hCφ0, hCφ⟩ := cmxFB_decay φ (d + 2)
  have hC0 : 0 ≤ C := by
    have := hf 0
    simp at this
    exact le_trans (abs_nonneg _) this
  have hconv := Integrable.convolution_integrand (μ := (volume : Measure (Euc d)))
    (ν := (volume : Measure (Euc d))) (ContinuousLinearMap.mul ℝ ℝ)
    (cmxFB_integrable_inv_pow (d := d) (d + 1) (by omega))
    (cmxFB_integrable_pow_mul Ψ (d + 2))
  refine (hconv.const_mul (C * Cφ)).mono' ?_ ?_
  · have h1 : Measurable fun p : Euc d × Euc d => Ψ (p.1 - p.2) * ((f p.2 : ℝ) : ℂ) * φ p.1 := by
      have := Ψ.continuous
      have := φ.continuous
      fun_prop
    exact h1.aestronglyMeasurable
  · refine Eventually.of_forall fun p => ?_
    obtain ⟨x, y⟩ := p
    simp only [ContinuousLinearMap.mul_apply', norm_mul, Complex.norm_real, Real.norm_eq_abs]
    set u := 1 + ‖x‖ with hu
    set v := 1 + ‖x - y‖ with hv
    set w := 1 + ‖y‖ with hw
    have hu1 : 1 ≤ u := by rw [hu]; linarith [norm_nonneg x]
    have hv1 : 1 ≤ v := by rw [hv]; linarith [norm_nonneg (x - y)]
    have hw1 : 1 ≤ w := by rw [hw]; linarith [norm_nonneg y]
    have hwuv : w ≤ u * v := by
      have : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
        calc ‖y‖ = ‖x - (x - y)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le _ _
      rw [hu, hv, hw]
      nlinarith [norm_nonneg x, norm_nonneg (x - y)]
    have key : w ^ (d + 1) * (w * ‖φ x‖) ≤ Cφ * v ^ (d + 2) := by
      calc w ^ (d + 1) * (w * ‖φ x‖) = w ^ (d + 2) * ‖φ x‖ := by ring
        _ ≤ (u * v) ^ (d + 2) * ‖φ x‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hwuv _) (norm_nonneg _)
        _ = (u ^ (d + 2) * ‖φ x‖) * v ^ (d + 2) := by rw [mul_pow]; ring
        _ ≤ Cφ * v ^ (d + 2) :=
          mul_le_mul_of_nonneg_right (hCφ x) (by positivity)
    have hwpos : 0 < w ^ (d + 1) := by positivity
    have key2 : w * ‖φ x‖ ≤ Cφ * v ^ (d + 2) * (w ^ (d + 1))⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hwpos]
      linarith
    have hf' := hf y
    calc ‖Ψ (x - y)‖ * |f y| * ‖φ x‖ ≤ ‖Ψ (x - y)‖ * (C * w) * ‖φ x‖ := by
          gcongr
      _ = C * ‖Ψ (x - y)‖ * (w * ‖φ x‖) := by ring
      _ ≤ C * ‖Ψ (x - y)‖ * (Cφ * v ^ (d + 2) * (w ^ (d + 1))⁻¹) := by gcongr
      _ = C * Cφ * ((w ^ (d + 1))⁻¹ * (v ^ (d + 2) * ‖Ψ (x - y)‖)) := by ring_nf

theorem cmxFB_Pleq_supp (L : ℝ) (hL : 0 < L) (f : Euc d → ℝ) (C : ℝ)
    (hf : ∀ x, |f x| ≤ C * (1 + ‖x‖)) (hm : Measurable f) (φ : SchwartzMap (Euc d) ℂ)
    (hφ : Disjoint (tsupport (𝓕 (⇑φ))) (closedBall (0 : Euc d) (2 * L))) :
    ∫ x, ((Pleq L f x : ℝ) : ℂ) * φ x = 0 := by
  set Ψ := cmxFB_Om (d := d) L hL with hΨdef
  have hΨ : ∀ z, Ψ z = ((psiL L z : ℝ) : ℂ) := cmxFB_Om_apply hL
  have hΨeven : ∀ z, Ψ (-z) = Ψ z := fun z => by rw [hΨ, hΨ, cmxFB_psiL_neg]
  have h1 : ∀ x, ((Pleq L f x : ℝ) : ℂ) = ∫ y, Ψ (x - y) * ((f y : ℝ) : ℂ) := by
    intro x
    unfold Pleq
    have := integral_sub_left_eq_self (fun y => psiL L y • f (x - y)) volume x
    simp only [sub_sub_cancel, smul_eq_mul] at this
    simp only [smul_eq_mul]
    rw [← this, ← integral_complex_ofReal]
    simp [hΨ]
  have hint := cmxFB_integrable_prod Ψ φ f C hf hm
  have h2 : ∫ x, ((Pleq L f x : ℝ) : ℂ) * φ x =
      ∫ x, ∫ y, Ψ (x - y) * ((f y : ℝ) : ℂ) * φ x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [h1 x, ← integral_mul_const]
  rw [h2, integral_integral_swap hint]
  have h3 : ∀ y, ∫ x, Ψ (x - y) * ((f y : ℝ) : ℂ) * φ x = 0 := by
    intro y
    have h4 : ∫ x, φ x * Ψ (y - x) = 0 := by
      refine cmxFB_conv_zero hL φ (fun ξ hξ => ?_) y
      have : ξ ∉ tsupport (𝓕 (⇑φ)) := fun h =>
        (Set.disjoint_left.1 hφ h) (by simpa using hξ)
      exact image_eq_zero_of_notMem_tsupport this
    have h5 : ∀ x, Ψ (x - y) * ((f y : ℝ) : ℂ) * φ x = ((f y : ℝ) : ℂ) * (φ x * Ψ (y - x)) := by
      intro x
      rw [← hΨeven (x - y), neg_sub]
      ring
    simp_rw [h5]
    rw [integral_const_mul, h4, mul_zero]
  simp [h3]

end HRS.Commutator.Whole
