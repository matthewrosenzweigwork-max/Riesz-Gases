import HRS.Commutator.Whole.LocalAuxFC2

/-!
# CMX-LOWV auxiliary 1: Fourier support calculus

Helper lemmas (all prefixed `lowv_`) for `low_velocity`: a strict-margin reformulation of
`FourierSuppIn`, translation invariance, and the product lemma
`supp (f g)^ ⊂ B(0,R₁+R₂)` for `f` of Fourier support in `B̄(0,R₁)` and `g` smooth temperate with
Fourier support in `B̄(0,R₂)`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

theorem lowv_margin {f : Euc d → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (h : Disjoint (tsupport f) (closedBall (0 : Euc d) R)) :
    ∃ δ > 0, ∀ ξ : Euc d, ‖ξ‖ < R + δ → f ξ = 0 := by
  have hc : IsCompact (closedBall (0 : Euc d) R) := isCompact_closedBall _ _
  have ho : IsOpen (tsupport f)ᶜ := (isClosed_tsupport f).isOpen_compl
  have hsub : closedBall (0 : Euc d) R ⊆ (tsupport f)ᶜ := fun x hx => Set.disjoint_right.1 h hx
  obtain ⟨δ, hδ, hth⟩ := hc.exists_thickening_subset_open ho hsub
  refine ⟨δ, hδ, fun ξ hξ => ?_⟩
  rw [thickening_closedBall hδ hR] at hth
  have hmem : ξ ∈ (tsupport f)ᶜ := hth (by simpa [add_comm] using hξ)
  exact image_eq_zero_of_notMem_tsupport hmem

theorem lowv_disjoint {f : Euc d → ℂ} {r R : ℝ} (hr : R < r)
    (hz : ∀ ξ : Euc d, ‖ξ‖ < r → f ξ = 0) :
    Disjoint (tsupport f) (closedBall (0 : Euc d) R) := by
  have hsub : tsupport f ⊆ (ball (0 : Euc d) r)ᶜ := by
    refine closure_minimal ?_ (isOpen_ball.isClosed_compl)
    intro ξ hξ hb
    exact hξ (hz ξ (by simpa using hb))
  refine Set.disjoint_left.2 fun ξ h1 h2 => ?_
  apply hsub h1
  simp only [mem_ball_zero_iff]
  exact lt_of_le_of_lt (by simpa using h2) hr

theorem lowv_fs_apply {R : ℝ} {u : Euc d → ℝ} (h : FourierSuppIn R u)
    (φ : SchwartzMap (Euc d) ℂ) {r : ℝ} (hr : R < r)
    (hz : ∀ ξ : Euc d, ‖ξ‖ < r → 𝓕 (⇑φ) ξ = 0) :
    ∫ x, ((u x : ℝ) : ℂ) * φ x = 0 := h φ (lowv_disjoint hr hz)

theorem lowv_fs_of {R : ℝ} (hR : 0 ≤ R) {u : Euc d → ℝ}
    (h : ∀ φ : SchwartzMap (Euc d) ℂ, ∀ r : ℝ, R < r →
      (∀ ξ : Euc d, ‖ξ‖ < r → 𝓕 (⇑φ) ξ = 0) → ∫ x, ((u x : ℝ) : ℂ) * φ x = 0) :
    FourierSuppIn R u := by
  intro φ hφ
  obtain ⟨δ, hδ, hz⟩ := lowv_margin hR hφ
  exact h φ (R + δ) (by linarith) hz

theorem lowv_fs_mono {R R' : ℝ} {u : Euc d → ℝ} (h : FourierSuppIn R u) (hR : R ≤ R') :
    FourierSuppIn R' u :=
  fun φ hφ => h φ (hφ.mono_right (closedBall_subset_closedBall hR))

theorem lowv_fs_smul {R : ℝ} {u : Euc d → ℝ} (h : FourierSuppIn R u) (c : ℝ) :
    FourierSuppIn R (fun x => c * u x) := by
  intro φ hφ
  have := h φ hφ
  have e : ∀ x, ((c * u x : ℝ) : ℂ) * φ x = (c : ℂ) * (((u x : ℝ) : ℂ) * φ x) := fun x => by
    push_cast; ring
  simp_rw [e]
  rw [integral_const_mul, this, mul_zero]


theorem lowv_translate_schwartz (φ : SchwartzMap (Euc d) ℂ) (y : Euc d) :
    ∃ φy : SchwartzMap (Euc d) ℂ, (∀ x, φy x = φ (x + y)) ∧
      ∀ ξ : Euc d, 𝓕 (⇑φy) ξ =
        Complex.exp (((2 * Real.pi * inner ℝ y ξ : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑φ) ξ := by
  have hg : Function.HasTemperateGrowth (fun x : Euc d => x + y) := by fun_prop
  have hup : ∃ (k : ℕ) (C : ℝ), ∀ x : Euc d, ‖x‖ ≤ C * (1 + ‖x + y‖) ^ k := by
    refine ⟨1, 1 + ‖y‖, fun x => ?_⟩
    have h1 : ‖x‖ ≤ ‖x + y‖ + ‖y‖ := by
      calc ‖x‖ = ‖(x + y) - y‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖x + y‖ + ‖y‖ := norm_sub_le _ _
    nlinarith [norm_nonneg (x + y), norm_nonneg y]
  refine ⟨SchwartzMap.compCLM ℂ hg hup φ, fun x => rfl, fun ξ => ?_⟩
  have hcoe : (⇑(SchwartzMap.compCLM ℂ hg hup φ) : Euc d → ℂ) = fun x => φ (x + y) := rfl
  rw [hcoe, Real.fourier_eq', Real.fourier_eq']
  have h := integral_add_right_eq_self (μ := (volume : Measure (Euc d)))
    (fun v : Euc d => Complex.exp (((-2 * Real.pi * inner ℝ (v - y) ξ : ℝ) : ℂ) * Complex.I) • φ v) y
  simp only [add_sub_cancel_right] at h
  rw [h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  rw [inner_sub_left]
  push_cast
  ring

theorem lowv_fs_translate {R : ℝ} {u : Euc d → ℝ} (h : FourierSuppIn R u) (y : Euc d) :
    FourierSuppIn R (fun x => u (x - y)) := by
  intro φ hφ
  obtain ⟨φy, hφy, hF⟩ := lowv_translate_schwartz φ y
  have hz : Disjoint (tsupport (𝓕 (⇑φy))) (closedBall (0 : Euc d) R) := by
    have hsub : tsupport (𝓕 (⇑φy)) ⊆ tsupport (𝓕 (⇑φ)) := by
      refine closure_mono fun ξ hξ => ?_
      simp only [Function.mem_support] at hξ ⊢
      intro h0
      apply hξ
      rw [hF, h0, mul_zero]
    exact hφ.mono_left hsub
  have := h φy hz
  have e := integral_add_right_eq_self (μ := (volume : Measure (Euc d)))
    (fun x : Euc d => ((u (x - y) : ℝ) : ℂ) * φ x) y
  simp only [add_sub_cancel_right] at e
  rw [← e]
  simpa [hφy] using this

theorem lowv_modulate_fourier (φ : SchwartzMap (Euc d) ℂ) (η : Euc d) :
    ∃ φη : SchwartzMap (Euc d) ℂ, (∀ x, φη x =
        Complex.exp (((-2 * Real.pi * inner ℝ x η : ℝ) : ℂ) * Complex.I) * φ x) ∧
      ∀ ξ : Euc d, 𝓕 (⇑φη) ξ = 𝓕 (⇑φ) (ξ + η) := by
  have he : Function.HasTemperateGrowth
      (fun x : Euc d => Complex.exp (((-2 * Real.pi * inner ℝ x η : ℝ) : ℂ) * Complex.I)) := by
    have h1 : Function.HasTemperateGrowth (fun x : Euc d => (-2 * Real.pi) * inner ℝ x η) := by
      fun_prop
    exact Complex.hasTemperateGrowth_exp_mul_I.comp h1
  refine ⟨SchwartzMap.smulLeftCLM ℂ
    (fun x : Euc d => Complex.exp (((-2 * Real.pi * inner ℝ x η : ℝ) : ℂ) * Complex.I)) φ,
    fun x => ?_, fun ξ => ?_⟩
  · rw [SchwartzMap.smulLeftCLM_apply_apply he]; rfl
  · have hcoe : (⇑(SchwartzMap.smulLeftCLM ℂ
        (fun x : Euc d => Complex.exp (((-2 * Real.pi * inner ℝ x η : ℝ) : ℂ) * Complex.I)) φ) :
        Euc d → ℂ) = fun x => Complex.exp (((-2 * Real.pi * inner ℝ x η : ℝ) : ℂ) * Complex.I) * φ x := by
      funext x
      rw [SchwartzMap.smulLeftCLM_apply_apply he]; rfl
    rw [hcoe, Real.fourier_eq', Real.fourier_eq']
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    rw [inner_add_right]
    push_cast
    ring

theorem lowv_prod_fsupp {R1 R2 : ℝ} (hR1 : 0 ≤ R1) (hR2 : 0 ≤ R2) {f g : Euc d → ℝ}
    (hg : Function.HasTemperateGrowth g) (hf1 : FourierSuppIn R1 f) (hg1 : FourierSuppIn R2 g) :
    FourierSuppIn (R1 + R2) (fun x => f x * g x) := by
  refine lowv_fs_of (by linarith) fun φ r hr hz => ?_
  set r1 := (R1 + (r - R2)) / 2 with hr1def
  set r2 := r - r1 with hr2def
  have hr1 : R1 < r1 := by rw [hr1def]; linarith
  have hr2 : R2 < r2 := by rw [hr2def, hr1def]; linarith
  have hgC : Function.HasTemperateGrowth (fun x => ((g x : ℝ) : ℂ)) :=
    Complex.hasTemperateGrowth_ofReal.comp hg
  set ψ : SchwartzMap (Euc d) ℂ := SchwartzMap.smulLeftCLM ℂ (fun x => ((g x : ℝ) : ℂ)) φ with hψ
  have hψx : ∀ x, ψ x = ((g x : ℝ) : ℂ) * φ x := fun x => by
    rw [hψ, SchwartzMap.smulLeftCLM_apply_apply hgC]; rfl
  have key : ∫ x, ((f x : ℝ) : ℂ) * ψ x = 0 := by
    refine lowv_fs_apply hf1 ψ hr1 fun η hη => ?_
    obtain ⟨φη, hφη, hFη⟩ := lowv_modulate_fourier φ η
    have h1 : 𝓕 (⇑ψ) η = ∫ x, ((g x : ℝ) : ℂ) * φη x := by
      rw [Real.fourier_eq']
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      simp only [smul_eq_mul, hψx, hφη v]
      ring
    rw [h1]
    refine lowv_fs_apply hg1 φη hr2 fun ξ hξ => ?_
    rw [hFη]
    refine hz _ ?_
    calc ‖ξ + η‖ ≤ ‖ξ‖ + ‖η‖ := norm_add_le _ _
      _ < r2 + r1 := add_lt_add hξ hη
      _ = r := by rw [hr2def]; ring
  have e : ∀ x, ((f x * g x : ℝ) : ℂ) * φ x = ((f x : ℝ) : ℂ) * ψ x := fun x => by
    rw [hψx]; push_cast; ring
  simp_rw [e]
  exact key


theorem lowv_norm_Om {L : ℝ} (hL : 0 < L) (y : Euc d) :
    ‖cmxFB_Om (d := d) L hL y‖ = |psiL L y| := by
  rw [cmxFB_Om_apply hL, Complex.norm_real, Real.norm_eq_abs]

theorem lowv_psiL_integrable_mul {L : ℝ} (hL : 0 < L) (k : ℕ) :
    Integrable (fun y : Euc d => (1 + ‖y‖) ^ k * |psiL L y|) := by
  have := cmxFB_integrable_pow_mul (cmxFB_Om (d := d) L hL) k
  simpa [lowv_norm_Om hL] using this

theorem lowv_psiL_continuous {L : ℝ} (hL : 0 < L) : Continuous (psiL L : Euc d → ℝ) := by
  have h := (cmxFB_Om (d := d) L hL).continuous
  have h2 : Continuous fun y : Euc d => (cmxFB_Om (d := d) L hL y).re := Complex.continuous_re.comp h
  convert h2 using 1
  funext y
  rw [cmxFB_Om_apply hL]; simp

theorem lowv_Pleq_continuous {L : ℝ} (hL : 0 < L) {k : Euc d → ℝ} (hk : Continuous k) (C : ℝ)
    (hC : ∀ x, |k x| ≤ C * (1 + ‖x‖)) : Continuous (Pleq L k) := by
  rw [continuous_iff_continuousAt]
  intro z0
  have hint := lowv_psiL_integrable_mul (d := d) hL 1
  show ContinuousAt (fun z => ∫ y, psiL L y • k (z - y)) z0
  refine continuousAt_of_dominated
    (bound := fun y => (|C| * (2 + ‖z0‖)) * ((1 + ‖y‖) ^ 1 * |psiL L y|)) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun z => ?_
    exact ((lowv_psiL_continuous hL).smul (hk.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · have : ∀ᶠ z in 𝓝 z0, ‖z - z0‖ < 1 := by
      have := Metric.ball_mem_nhds z0 one_pos
      filter_upwards [this] with z hz
      simpa [dist_eq_norm] using hz
    filter_upwards [this] with z hz
    refine Eventually.of_forall fun y => ?_
    rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : 1 + ‖z - y‖ ≤ (2 + ‖z0‖) * (1 + ‖y‖) := by
      have : ‖z - y‖ ≤ ‖z - z0‖ + ‖z0‖ + ‖y‖ := by
        calc ‖z - y‖ = ‖(z - z0) + z0 - y‖ := by rw [sub_add_cancel]
          _ ≤ ‖(z - z0) + z0‖ + ‖y‖ := norm_sub_le _ _
          _ ≤ ‖z - z0‖ + ‖z0‖ + ‖y‖ := by gcongr; exact norm_add_le _ _
      nlinarith [norm_nonneg z0, norm_nonneg y, norm_nonneg (z - z0)]
    calc |psiL L y| * |k (z - y)| ≤ |psiL L y| * (C * (1 + ‖z - y‖)) := by
          gcongr; exact hC _
      _ ≤ |psiL L y| * (|C| * ((2 + ‖z0‖) * (1 + ‖y‖))) := by
          gcongr
          exact (le_abs_self C)
      _ = _ := by ring
  · exact hint.const_mul _
  · exact Eventually.of_forall fun y =>
      (by fun_prop : Continuous fun z : Euc d => psiL L y • k (z - y)).continuousAt


theorem lowv_pleq_pair {L : ℝ} (hL : 0 < L) (f : Euc d → ℝ) (C : ℝ)
    (hf : ∀ x, |f x| ≤ C * (1 + ‖x‖)) (hm : Measurable f) (φ : SchwartzMap (Euc d) ℂ) :
    Integrable (fun x => ((Pleq L f x : ℝ) : ℂ) * φ x) ∧
    ∫ x, ((Pleq L f x : ℝ) : ℂ) * φ x =
      ∫ y, ((f y : ℝ) : ℂ) * ∫ x, φ x * cmxFB_Om (d := d) L hL (y - x) := by
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
  have h2 : ∀ x, ((Pleq L f x : ℝ) : ℂ) * φ x = ∫ y, Ψ (x - y) * ((f y : ℝ) : ℂ) * φ x := by
    intro x
    rw [h1 x, ← integral_mul_const]
  refine ⟨?_, ?_⟩
  · have := hint.integral_prod_left
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [h2 x]
  · simp_rw [h2]
    rw [integral_integral_swap hint]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← hΨeven (x - y), neg_sub]
    ring

theorem lowv_bandlimited {R Λ : ℝ} (hR : 0 ≤ R) (hΛ : R < Λ) {k : Euc d → ℝ} (hk : Continuous k)
    (C : ℝ) (hC : ∀ x, |k x| ≤ C * (1 + ‖x‖)) (hs : FourierSuppIn R k) (z : Euc d) :
    Pleq Λ k z = k z := by
  have hΛ0 : 0 < Λ := by linarith
  set Ω := cmxFB_Om (d := d) Λ hΛ0 with hΩdef
  have hcont : Continuous (Pleq Λ k) := lowv_Pleq_continuous hΛ0 hk C hC
  have hae : ∀ᵐ x ∂(volume : Measure (Euc d)), Pleq Λ k x = k x := by
    have hloc : LocallyIntegrable (fun x => Pleq Λ k x - k x) volume :=
      (hcont.sub hk).locallyIntegrable
    have h0 := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
    · filter_upwards [h0] with x hx
      simpa [sub_eq_zero] using hx
    intro h hh hsupp
    have hhC : ContDiff ℝ ∞ (fun x => ((h x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hh
    have hsC : HasCompactSupport (fun x => ((h x : ℝ) : ℂ)) :=
      hsupp.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    set φ : SchwartzMap (Euc d) ℂ := hsC.toSchwartzMap hhC with hφdef
    have hφ : ∀ x, φ x = ((h x : ℝ) : ℂ) := fun x => rfl
    have hkm : Measurable k := hk.measurable
    obtain ⟨hPint, hPeq⟩ := lowv_pleq_pair hΛ0 k C hC hkm φ
    set Θ := SchwartzMap.convolution (𝕜 := ℂ) (ContinuousLinearMap.mul ℂ ℂ) φ Ω with hΘdef
    have hΘ : ∀ y, Θ y = ∫ x, φ x * Ω (y - x) := by
      intro y
      have := SchwartzMap.convolution_apply (ContinuousLinearMap.mul ℂ ℂ) φ Ω y
      rw [this, MeasureTheory.convolution_def]
      simp
    have hkint : ∀ ψ : SchwartzMap (Euc d) ℂ, Integrable (fun x => ((k x : ℝ) : ℂ) * ψ x) := by
      intro ψ
      have h1 := cmxFB_integrable_pow_mul ψ 1
      have h0 := (ψ.integrable (μ := (volume : Measure (Euc d)))).norm
      refine ((h1.add h0).const_mul (|C| + 1)).mono' ?_ (Eventually.of_forall fun x => ?_)
      · exact (Complex.continuous_ofReal.comp hk |>.mul ψ.continuous).aestronglyMeasurable
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have := hC x
        have h2 : |k x| ≤ (|C| + 1) * (1 + ‖x‖) := by
          calc |k x| ≤ C * (1 + ‖x‖) := this
            _ ≤ |C| * (1 + ‖x‖) := by gcongr; exact le_abs_self _
            _ ≤ (|C| + 1) * (1 + ‖x‖) := by gcongr; linarith
        calc |k x| * ‖ψ x‖ ≤ (|C| + 1) * (1 + ‖x‖) * ‖ψ x‖ := by gcongr
          _ = (|C| + 1) * ((1 + ‖x‖) ^ 1 * ‖ψ x‖ + ‖ψ x‖) - (|C| + 1) * ‖ψ x‖ + 0 := by ring
          _ ≤ (|C| + 1) * ((1 + ‖x‖) ^ 1 * ‖ψ x‖ + ‖ψ x‖) := by
              have : 0 ≤ (|C| + 1) * ‖ψ x‖ := by positivity
              linarith
    -- the test function φ' = φ - Θ has Fourier transform vanishing on B(0,Λ)
    have hz : ∀ ξ : Euc d, ‖ξ‖ < Λ → 𝓕 (⇑(φ - Θ)) ξ = 0 := by
      intro ξ hξ
      have h1 : 𝓕 (φ - Θ) = 𝓕 φ - 𝓕 Θ := map_sub (SchwartzMap.fourierTransformCLM ℂ) φ Θ
      have h2 : 𝓕 Θ = SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 φ) (𝓕 Ω) :=
        SchwartzMap.fourier_convolution _ _ _
      have h3 : 𝓕 Ω = cmxFB_G (d := d) Λ hΛ0 := cmxFB_fourier_Om hΛ0
      have h4 : cmxFB_gL d Λ ξ = 1 := by
        unfold cmxFB_gL
        have : chi (Λ⁻¹ • ξ) = 1 := by
          apply cmxFB_chi_one
          rw [norm_smul, norm_inv, Real.norm_of_nonneg hΛ0.le, inv_mul_le_iff₀ hΛ0, mul_one]
          exact hξ.le
        rw [this]; simp
      have h5 : (𝓕 (φ - Θ) : SchwartzMap (Euc d) ℂ) ξ = 0 := by
        rw [h1, h2, h3]
        simp only [SchwartzMap.sub_apply, SchwartzMap.pairing_apply_apply,
          ContinuousLinearMap.mul_apply', cmxFB_G_apply, h4, mul_one, sub_self]
      rwa [SchwartzMap.fourier_coe] at h5
    have h6 := lowv_fs_apply hs (φ - Θ) hΛ hz
    have h7 : ∫ x, ((k x : ℝ) : ℂ) * (φ - Θ) x =
        (∫ x, ((k x : ℝ) : ℂ) * φ x) - ∫ x, ((k x : ℝ) : ℂ) * Θ x := by
      simp_rw [SchwartzMap.sub_apply, mul_sub]
      exact integral_sub (hkint φ) (hkint Θ)
    have h8 : ∫ x, ((Pleq Λ k x : ℝ) : ℂ) * φ x = ∫ x, ((k x : ℝ) : ℂ) * Θ x := by
      rw [hPeq]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only
      rw [hΘ y]
    have key : ∫ x, (((Pleq Λ k x - k x : ℝ)) : ℂ) * φ x = 0 := by
      have : ∀ x, (((Pleq Λ k x - k x : ℝ)) : ℂ) * φ x =
          ((Pleq Λ k x : ℝ) : ℂ) * φ x - ((k x : ℝ) : ℂ) * φ x := fun x => by
        push_cast; ring
      simp_rw [this]
      rw [integral_sub hPint (hkint φ), h8]
      rw [h7] at h6
      linear_combination -h6
    have key2 : ((∫ x, h x • (Pleq Λ k x - k x) : ℝ) : ℂ) = 0 := by
      rw [← integral_complex_ofReal]
      rw [← key]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [smul_eq_mul, hφ]
      push_cast; ring
    exact_mod_cast key2
  exact congrFun ((Continuous.ae_eq_iff_eq (volume : Measure (Euc d)) hcont hk).1 hae) z

end HRS.Commutator.Whole
