import HRS.Sections.ScrnAux44

/-!
# Packet SCRN, part 45: the covariances at times `u_n + t_a` converge to the stationary covariance

`scrn_stat_entry_tendsto`: for `u_n → ∞`, each entry of `mesoCovMatrix b (u_n + t)` minus the entry of
`mesoStatCovMatrix b t` tends to `0` (dominated convergence: the difference of the kernels is
`(1 - S) e^{-(2u+t_a+t_c)a}`, which tends to `0` off `ξ = 0`).  `scrn_stat_gauss_tendsto`: hence
`smoothDist 3 N(0, mesoCov) N(0, statCov) → 0`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform ComplexConjugate

namespace HRS

variable {d : ℕ}

theorem scrn_stat_entry_tendsto (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {p : ℕ}
    (φ : Fin p → Euc d → ℝ) (hφ : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (φ a) ∧ HasCompactSupport (φ a))
    {b : ℝ} (hb : 0 < b) (t : Fin p → ℝ) (ht : ∀ a, 0 ≤ t a) {u : ℕ → ℝ} (hu0 : ∀ n, 0 ≤ u n)
    (hu : Tendsto u atTop atTop) (a c : Fin p) :
    Tendsto (fun n : ℕ => mesoCovMatrix d s b (fun a => u n + t a) φ a c -
      mesoStatCovMatrix d s b t φ a c) atTop (𝓝 0) := by
  have hcr : 0 < rieszConst d s := rieszConst_pos hd hs0 hsd
  obtain ⟨A, hA0, hG⟩ := scrn_G_hyp hd hs0 hsd φ hφ
  set Fa : Euc d → ℂ := 𝓕 (scrnPhiC (φ a)) with hFa
  set Fc : Euc d → ℂ := 𝓕 (scrnPhiC (φ c)) with hFc
  have hFac : Continuous Fa := (scrn_fourier_diff (hφ a).1 (hφ a).2).continuous
  have hFcc : Continuous Fc := (scrn_fourier_diff (hφ c).1 (hφ c).2).continuous
  set q : ℝ := (d : ℝ) - s with hq
  set Kn : ℕ → Euc d → ℝ := fun n ξ => (1 - scrnS (rieszConst d s) q b (2 * Real.pi * ‖ξ‖)) *
    Real.exp (-((u n + t a) + (u n + t c)) * scrnA (rieszConst d s) q b (2 * Real.pi * ‖ξ‖)) with hKn
  set H : ℕ → Euc d → ℂ := fun n ξ => (Fa ξ * (starRingEnd ℂ) (Fc ξ)) * ((Kn n ξ : ℝ) : ℂ) with hH
  have hKm : ∀ n, Measurable (Kn n) := by
    intro n; simp only [hKn, scrnS, scrnA]; fun_prop
  have hHm : ∀ n, Measurable (H n) := by
    intro n
    have : Measurable (fun ξ => Fa ξ * (starRingEnd ℂ) (Fc ξ)) :=
      (hFac.mul (Complex.continuous_conj.comp hFcc)).measurable
    exact this.mul (Complex.measurable_ofReal.comp (hKm n))
  have hbound : ∀ n, ∀ ξ, 0 ≤ Kn n ξ ∧ Kn n ξ ≤ 1 := by
    intro n ξ
    have hρ : 0 ≤ 2 * Real.pi * ‖ξ‖ := by positivity
    have h1 := scrnS_nonneg' (q := q) hcr hb hρ
    have h2 := scrnS_lt_one' (q := q) hcr hb hρ
    have h3 := scrnA_nonneg' (q := q) hcr hb hρ
    have h4 : Real.exp (-((u n + t a) + (u n + t c)) * scrnA (rieszConst d s) q b (2 * Real.pi * ‖ξ‖)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [hu0 n, ht a, ht c])
    have h5 := Real.exp_pos (-((u n + t a) + (u n + t c)) * scrnA (rieszConst d s) q b (2 * Real.pi * ‖ξ‖))
    refine ⟨mul_nonneg (by linarith) h5.le, ?_⟩
    simp only [hKn]
    nlinarith
  obtain ⟨-, -, hFF, -⟩ := hG b hb t ht a c
  have hLint : Integrable (fun ξ : Euc d => (1 + ‖ξ‖) ^ (-((d : ℝ) + 1))) := by
    refine integrable_one_add_norm (E := Euc d) ?_
    simp
  have hHbd : ∀ n ξ, ‖H n ξ‖ ≤ A * (1 + ‖ξ‖) ^ (-((d : ℝ) + 1)) := by
    intro n ξ
    show ‖(Fa ξ * (starRingEnd ℂ) (Fc ξ)) * ((Kn n ξ : ℝ) : ℂ)‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hbound n ξ).1]
    have := hFF ξ
    calc ‖Fa ξ * (starRingEnd ℂ) (Fc ξ)‖ * Kn n ξ ≤ ‖Fa ξ * (starRingEnd ℂ) (Fc ξ)‖ * 1 :=
          mul_le_mul_of_nonneg_left (hbound n ξ).2 (norm_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact this
  have hHint : ∀ n, Integrable (H n) := fun n =>
    Integrable.mono' (hLint.const_mul A) (hHm n).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => hHbd n ξ)
  -- the difference of the integrands
  have hdiff : ∀ n ξ, scrnGab d s b (fun a => u n + t a) φ a c ξ - scrnGstat d s b t φ a c ξ =
      H n ξ := by
    intro n ξ
    simp only [hH, hKn, scrnGab, scrnGstat, scrnKab, scrnKstat, scrnk]
    have e1 : (u n + t a) - (u n + t c) = t a - t c := by ring
    rw [e1]
    push_cast
    ring
  have hG' : ∀ n, Integrable (scrnGab d s b (fun a => u n + t a) φ a c) := fun n =>
    scrn_Gab_integrable hd hs0 hsd φ hφ hb (fun a => u n + t a) (fun a => by
      have := hu0 n; have := ht a; linarith) a c
  have hGs : ∀ n : ℕ, Integrable (scrnGstat d s b t φ a c) := by
    intro n
    have e : scrnGstat d s b t φ a c =
        fun ξ => scrnGab d s b (fun a => u n + t a) φ a c ξ - H n ξ := by
      funext ξ; rw [← hdiff n ξ]; ring
    rw [e]
    exact (hG' n).sub (hHint n)
  have hentry : ∀ n, mesoCovMatrix d s b (fun a => u n + t a) φ a c -
      mesoStatCovMatrix d s b t φ a c = (∫ ξ, H n ξ).re := by
    intro n
    rw [meso_entry_eq, meso_stat_entry_eq, ← Complex.sub_re]
    congr 1
    rw [← integral_sub (hG' n) (hGs n)]
    congr 1
    funext ξ
    exact hdiff n ξ
  simp_rw [hentry]
  -- dominated convergence
  have hlim : Tendsto (fun n => ∫ ξ, H n ξ) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := (volume : Measure (Euc d)))
      (F := H) (f := fun _ => (0 : ℂ)) (fun ξ => A * (1 + ‖ξ‖) ^ (-((d : ℝ) + 1)))
      (fun n => (hHm n).aestronglyMeasurable) (hLint.const_mul A)
      (fun n => Filter.Eventually.of_forall fun ξ => hHbd n ξ) ?_
    · simpa using this
    · haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
      have h0 : (volume : Measure (Euc d)) {0} = 0 := measure_singleton _
      have hae : ∀ᵐ ξ ∂(volume : Measure (Euc d)), ξ ∉ ({0} : Set (Euc d)) :=
        measure_eq_zero_iff_ae_notMem.1 h0
      filter_upwards [hae] with ξ hξ
      have hξ0 : ξ ≠ 0 := hξ
      have hρ : 0 < 2 * Real.pi * ‖ξ‖ := by
        have : 0 < ‖ξ‖ := norm_pos_iff.2 hξ0
        positivity
      have hApos := scrnA_pos (q := q) hcr hb hρ
      set A' := scrnA (rieszConst d s) q b (2 * Real.pi * ‖ξ‖) with hA'
      have h2u : Tendsto (fun n => 2 * u n + (t a + t c)) atTop atTop :=
        (hu.const_mul_atTop two_pos).atTop_add tendsto_const_nhds
      have h3 : Tendsto (fun n => (2 * u n + (t a + t c)) * A') atTop atTop :=
        h2u.atTop_mul_const hApos
      have h4 : Tendsto (fun n => Real.exp (-((2 * u n + (t a + t c)) * A'))) atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp h3
      have h5 : Tendsto (fun n => Kn n ξ) atTop (𝓝 0) := by
        have := h4.const_mul (1 - scrnS (rieszConst d s) q b (2 * Real.pi * ‖ξ‖))
        rw [mul_zero] at this
        refine this.congr fun n => ?_
        simp only [hKn, hA']
        congr 2
        ring
      have h6 : Tendsto (fun n => ((Kn n ξ : ℝ) : ℂ)) atTop (𝓝 0) := by
        have := (Complex.continuous_ofReal.tendsto 0).comp h5
        simpa [Function.comp_def] using this
      have := h6.const_mul (Fa ξ * (starRingEnd ℂ) (Fc ξ))
      rw [mul_zero] at this
      exact this
  have := (Complex.continuous_re.tendsto 0).comp hlim
  simpa [Function.comp_def] using this


theorem scrn_stat_gauss_tendsto (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {p : ℕ}
    (φ : Fin p → Euc d → ℝ) (hφ : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (φ a) ∧ HasCompactSupport (φ a))
    {b : ℝ} (hb : 0 < b) (t : Fin p → ℝ) (ht : ∀ a, 0 ≤ t a) {u : ℕ → ℝ} (hu0 : ∀ n, 0 ≤ u n)
    (hu : Tendsto u atTop atTop) :
    Tendsto (fun n : ℕ => smoothDist 3
      (ProbabilityTheory.multivariateGaussian 0 (mesoCovMatrix d s b (fun a => u n + t a) φ))
      (ProbabilityTheory.multivariateGaussian 0 (mesoStatCovMatrix d s b t φ))) atTop (𝓝 0) := by
  have hbound : ∀ n : ℕ, smoothDist 3
      (ProbabilityTheory.multivariateGaussian 0 (mesoCovMatrix d s b (fun a => u n + t a) φ))
      (ProbabilityTheory.multivariateGaussian 0 (mesoStatCovMatrix d s b t φ)) ≤
      (1 / 2) * ∑ i : Fin p, ∑ j : Fin p, |mesoCovMatrix d s b (fun a => u n + t a) φ i j -
        mesoStatCovMatrix d s b t φ i j| := by
    intro n
    have hQ := scrn_mesoCov_psd hd hs0 hsd φ hφ hb (fun a => u n + t a) (fun a => by
      have := hu0 n; have := ht a; linarith)
    have hQ' := scrn_mesoStatCov_psd hd hs0 hsd φ hφ hb t ht
    refine (smoothDist_gaussian_covariance _ _ hQ hQ').trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (HRS.PDE.MFLinear.traceNormMatrix_le_sum _).trans (le_of_eq ?_)
    simp only [Matrix.sub_apply]
  have hlim : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * ∑ i : Fin p, ∑ j : Fin p,
      |mesoCovMatrix d s b (fun a => u n + t a) φ i j - mesoStatCovMatrix d s b t φ i j|)
      atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => ∑ i : Fin p, ∑ j : Fin p,
        |mesoCovMatrix d s b (fun a => u n + t a) φ i j - mesoStatCovMatrix d s b t φ i j|)
        atTop (𝓝 0) := by
      have := tendsto_finset_sum (Finset.univ : Finset (Fin p)) (fun i _ =>
        tendsto_finset_sum (Finset.univ : Finset (Fin p)) (fun j _ =>
          (scrn_stat_entry_tendsto hd hs0 hsd φ hφ hb t ht hu0 hu i j).abs))
      simpa using this
    simpa using h.const_mul (1 / 2 : ℝ)
  exact squeeze_zero (fun n => smoothDist_nonneg 3 _ _) hbound hlim

end HRS
