import HRS.MC.CepP2Aux5

/-!
# Packet CEPP2 (aux 6): local smooth nonnegative density of a finite measure with Fourier decay
-/

open MeasureTheory
noncomputable section
namespace HRS.MC.CepP2
variable {n : ℕ}

/-- A smooth function representing `ν` as a distribution vanishes off `K` (closed support). -/
lemma dens_zero_off {ν : Measure (XS n)} {K : Set (XS n)} (hK : IsClosed K) (hνK : ν Kᶜ = 0)
    {h : XS n → ℝ} (hh : Continuous h)
    (hid : ∀ φ : XS n → ℝ, ContDiff ℝ smTop φ → HasCompactSupport φ → ∫ p, φ p ∂ν = ∫ q, φ q * h q) :
    ∀ q ∉ K, h q = 0 := by
  have hae : ∀ᵐ x ∂(volume : Measure (XS n)), x ∈ Kᶜ → h x = 0 := by
    refine hK.isOpen_compl.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hh.locallyIntegrable.locallyIntegrableOn _) ?_
    intro g hg hgc hgs
    have h1 : ∫ p, g p ∂ν = 0 := by
      have hK' : ∀ᵐ x ∂ν, x ∈ K := by
        have := (measure_eq_zero_iff_ae_notMem.1 hνK)
        filter_upwards [this] with x hx
        simpa using hx
      have : (fun p => g p) =ᵐ[ν] fun _ => 0 := by
        filter_upwards [hK'] with x hx
        exact image_eq_zero_of_notMem_tsupport (fun h' => (hgs h') hx)
      rw [integral_congr_ae this]; simp
    have := hid g hg hgc
    rw [h1] at this
    simpa [smul_eq_mul] using this.symm
  have hae' : h =ᵐ[(volume : Measure (XS n)).restrict Kᶜ] fun _ => 0 := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hK.measurableSet.compl]
    exact hae
  have := Measure.eqOn_open_of_ae_eq hae' hK.isOpen_compl hh.continuousOn continuousOn_const
  intro q hq
  exact this hq


lemma dens_nonneg (ν : Measure (XS n)) [IsFiniteMeasure ν] {h : XS n → ℝ} (hh : Continuous h)
    (hid : ∀ φ : XS n → ℝ, ContDiff ℝ smTop φ → HasCompactSupport φ → ∫ p, φ p ∂ν = ∫ q, φ q * h q) :
    ∀ q, 0 ≤ h q := by
  by_contra hcon
  push Not at hcon
  obtain ⟨q0, hq0⟩ := hcon
  have hU : IsOpen {q : XS n | h q < 0} := isOpen_lt hh continuous_const
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU q0 hq0
  let φ : ContDiffBump q0 := ⟨r / 2, r, by positivity, by linarith⟩
  have hφc : HasCompactSupport φ := φ.hasCompactSupport
  have hφs : ContDiff ℝ smTop φ := φ.contDiff
  have h1 : 0 ≤ ∫ p, φ p ∂ν := integral_nonneg fun p => φ.nonneg
  rw [hid φ hφs hφc] at h1
  have hf : Integrable (fun q => -(φ q * h q)) (volume : Measure (XS n)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (φ.continuous.mul hh).neg
    · exact (hφc.mul_right (f' := h)).comp_left (g := fun x : ℝ => -x) neg_zero
  have hnn : 0 ≤ fun q => -(φ q * h q) := by
    intro q
    show 0 ≤ -(φ q * h q)
    by_cases hq : φ q = 0
    · simp [hq]
    · have : q ∈ Metric.ball q0 r := by
        have : q ∈ Function.support φ := hq
        rwa [φ.support_eq] at this
      have := hball this
      have hpos : 0 ≤ φ q := φ.nonneg
      have : h q < 0 := this
      nlinarith
  have h2 := (integral_pos_iff_support_of_nonneg hnn hf).2 (by
    refine lt_of_lt_of_le (Metric.measure_ball_pos volume q0 (by positivity : 0 < r / 2)) (measure_mono ?_)
    intro q hq
    have hq' : q ∈ Metric.closedBall q0 (r / 2) := Metric.ball_subset_closedBall hq
    have e1 : φ q = 1 := φ.one_of_mem_closedBall hq'
    have e2 : h q < 0 := hball (by
      have : dist q q0 < r / 2 := hq
      show dist q q0 < r
      linarith)
    show -(φ q * h q) ≠ 0
    rw [e1]; linarith)
  rw [integral_neg] at h2
  linarith


/-- Key identity for `cos`/`sin` of a linear form. -/
lemma dens_trig {ν : Measure (XS n)} [IsFiniteMeasure ν] {K : Set (XS n)} (hνK : ν Kᶜ = 0)
    {h : XS n → ℝ} (hhK : ∀ q ∉ K, h q = 0)
    (hid : ∀ φ : XS n → ℝ, ContDiff ℝ smTop φ → HasCompactSupport φ → ∫ p, φ p ∂ν = ∫ q, φ q * h q)
    {χt : XS n → ℝ} (hχt : ContDiff ℝ smTop χt) (hχtc : HasCompactSupport χt)
    (hχt1 : ∀ p ∈ K, χt p = 1) (T : ℝ → ℝ) (hT : ContDiff ℝ smTop T) (L : XS n →L[ℝ] ℝ) :
    ∫ p, T (L p) ∂ν = ∫ q, T (L q) * h q := by
  have hK' : ∀ᵐ x ∂ν, x ∈ K := by
    have := (measure_eq_zero_iff_ae_notMem.1 hνK)
    filter_upwards [this] with x hx
    simpa using hx
  have e1 : ∫ p, T (L p) ∂ν = ∫ p, χt p * T (L p) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hK'] with x hx
    rw [hχt1 x hx, one_mul]
  have hφ : ContDiff ℝ smTop (fun p => χt p * T (L p)) := hχt.mul (hT.comp L.contDiff)
  have hφc : HasCompactSupport (fun p => χt p * T (L p)) := hχtc.mul_right (f' := fun p => T (L p))
  rw [e1, hid _ hφ hφc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  by_cases hq : q ∈ K
  · simp only [hχt1 q hq, one_mul]
  · simp [hhK q hq]


theorem local_density (ν : Measure (XS n)) [IsFiniteMeasure ν]
    (hν : ∀ m : ℕ, Integrable (fun ζ : XS n => ‖ζ‖ ^ m * ‖Gf ν ζ‖))
    {K : Set (XS n)} (hKc : IsCompact K) (hνK : ν Kᶜ = 0)
    {χt : XS n → ℝ} (hχt : ContDiff ℝ smTop χt) (hχtc : HasCompactSupport χt)
    (hχt1 : ∀ p ∈ K, χt p = 1) :
    ∃ h : XS n → ℝ, ContDiff ℝ smTop h ∧ (∀ p, 0 ≤ h p) ∧
      ν = (volume : Measure (XS n)).withDensity (fun p => ENNReal.ofReal (h p)) := by
  obtain ⟨h, hh, hid⟩ := dens_of_fourier ν hν
  have hK := hKc.isClosed
  have hh0 := dens_zero_off hK hνK hh.continuous hid
  have hnn := dens_nonneg ν hh.continuous hid
  refine ⟨h, hh, hnn, ?_⟩
  have hhc : HasCompactSupport h := HasCompactSupport.intro hKc hh0
  have hhi : Integrable h (volume : Measure (XS n)) := hh.continuous.integrable_of_hasCompactSupport hhc
  have : IsFiniteMeasure ((volume : Measure (XS n)).withDensity fun p => ENNReal.ofReal (h p)) :=
    isFiniteMeasure_withDensity_ofReal hhi.2
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_apply, charFunDual_apply]
  rw [integral_withDensity_eq_integral_toReal_smul hh.continuous.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun p => ENNReal.ofReal_lt_top)]
  have hrw : (fun x : XS n => (ENNReal.ofReal (h x)).toReal • Complex.exp (↑(L x) * Complex.I)) =
      fun x => (h x : ℂ) * Complex.exp (↑(L x) * Complex.I) := by
    funext x; rw [ENNReal.toReal_ofReal (hnn x), Complex.real_smul]
  rw [hrw]
  have hint1 : Integrable (fun x : XS n => Complex.exp (↑(L x) * Complex.I)) ν := by
    refine (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact Continuous.aestronglyMeasurable (by fun_prop)
    · rw [Complex.norm_exp_ofReal_mul_I]
  have hint2 : Integrable (fun x : XS n => (h x : ℂ) * Complex.exp (↑(L x) * Complex.I))
      (volume : Measure (XS n)) := by
    have hc := hh.continuous
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.intro hKc fun x hx => ?_)
    simp [hh0 x hx]
  have hT1 := dens_trig hνK hh0 hid hχt hχtc hχt1 Real.cos Real.contDiff_cos L
  have hT2 := dens_trig hνK hh0 hid hχt hχtc hχt1 Real.sin Real.contDiff_sin L
  apply Complex.ext
  · have e1 := integral_re hint1
    have e2 := integral_re hint2
    simp only [RCLike.re_to_complex] at e1 e2
    rw [← e1, ← e2]
    simp only [Complex.exp_ofReal_mul_I_re, Complex.re_ofReal_mul]
    rw [hT1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  · have e1 := integral_im hint1
    have e2 := integral_im hint2
    simp only [RCLike.im_to_complex] at e1 e2
    rw [← e1, ← e2]
    simp only [Complex.exp_ofReal_mul_I_im, Complex.im_ofReal_mul]
    rw [hT2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring

end HRS.MC.CepP2
